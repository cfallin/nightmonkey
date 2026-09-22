/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Compiler options: the tuning parameters and diagnostic switches the
//! toplevel entry points accept.
//!
//! Everything here is either a production parameter or a diagnostic that
//! produces output without changing codegen. There are deliberately no
//! switches that select between codegen designs: the compiler has one
//! lowering strategy and one analysis, and they are not configurable.

/// Write one line of diagnostic output.
///
/// The switches in [`Diagnostics`] produce a structured line stream on
/// stderr. `tools/viz.py` parses the `night: viz ...` lines with anchored
/// patterns, so they must reach the stream verbatim: they cannot go through
/// `log`, which prefixes and filters them. Every diagnostic write goes
/// through this macro, which is why the crate contains no bare `eprintln!`.
/// Anything that can fire in a production compile is a `log::warn!` or
/// `log::error!` instead.
#[macro_export]
macro_rules! diag_line {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr().lock(), $($arg)*);
    }};
}

/// Diagnostic output switches. None of these change the generated code;
/// enabling any of them only adds output on stderr (or, for `facts`, a
/// file). They exist for compiler debugging and are off in production.
#[derive(Clone, Debug, Default)]
pub struct Diagnostics {
    /// Disassemble each script's bytecode before translating it. `Some(ids)`
    /// restricts the dump to those source ids; an empty list means all of
    /// them. A whole-bundle disassembly is megabytes, so the filter is what
    /// makes this usable on anything but a toy program.
    pub disasm: Option<Vec<u32>>,
    /// Dump the per-version BBV state (one record per emitted version).
    pub bbv: bool,
    /// Emit the machine-readable speculation trace consumed by
    /// `tools/viz.py`: one record per version and per guard event.
    pub viz: bool,
    /// With `viz`, additionally dump the per-op lowering: the mini-CFG each
    /// bytecode op expands into, its guards, memory traffic and helper
    /// calls. Per-instruction data, so it is large.
    pub viz_lower: bool,
    /// Write the analysis fact tables to this path (see `likelier::dump`).
    pub facts: Option<String>,
    /// Write the analysis half of the speculation trace to this path
    /// instead of stderr (see `likelier::viz`). Implies `viz` for the
    /// analysis; the translator half still needs `viz` itself.
    pub viz_facts: Option<String>,
    /// Report analysis and translation timings and per-phase counts.
    pub stats: bool,
    /// Emit the per-op emitted-IR census: one record per emitted op
    /// instance with the waffle blocks and instructions its lowering
    /// added, split by instruction class. Static code-size attribution.
    pub opsize: bool,
    /// Emit one record per continuation edge naming the ctx it hands to its
    /// successor pc. The cross-arm diff (`tools/ctxdiff.py`) turns that into
    /// "which arm dropped which fact", which is the half of the Opt-track
    /// question the `dmerge` audit cannot see.
    pub ctxedge: bool,
    /// Emit one record per site that WOULD consume a durable class fact,
    /// naming what it actually had. The fact-kill censuses say a fact died;
    /// this says whether a consumer wanted it, which is the difference
    /// between a kill that costs code and a kill nobody notices.
    pub clsfact: bool,
    /// Emit one record per property-access site the analysis leaves without
    /// a `prop_sites` row, naming the gate that refused. A site with no row
    /// falls to the inline cache, which is the same ~540 bytes at every one
    /// of them, so this is the coverage half of the code-size question --
    /// `--dump-clsfact` says whether a consumer wanted a fact, this says why
    /// the analysis never made one.
    pub propgap: bool,
    /// Emit the redundant-work census: per op instance, the box round
    /// trips, dead boxes and frame round trips its lowering emitted
    /// (`bbv/redundant.rs`). Joined against `--census` entry counts by
    /// `tools/opclass.py`, this is the OPT-path half of the cost question.
    pub redundant: bool,
    /// Dump the CFG, dominator tree and loop nest over the unified pc space
    /// (`bbv/cfg.rs`), including the audit of its loop headers against the
    /// `scan_loop_intervals` extents the token machinery keys on.
    pub cfg: bool,
    /// Per loop header: the slots the single-version join weakens against
    /// the back edge's own arrival, among the slots the body reads -- the
    /// peel rule's census (peel iff some such slot exists).
    pub peel: bool,
    /// Trace every raise into one analysis cell, named `arg:<sid>:<n>` or
    /// `local:<sid>:<n>`: the incoming object type and the constraint
    /// responsible. Answers "which writer made this slot AnyObject", which
    /// no census can, because the answer is one join step inside the solver.
    pub trace_cell: Option<String>,
    /// Trace every heap read and write of one property name.
    pub trace_field: Option<String>,
    /// Trace the per-context evaluation of one read site, `<sid>:<pc>`.
    pub trace_site: Option<String>,
}

impl Diagnostics {
    /// True when any diagnostic is on, i.e. when the compiler is allowed to
    /// write progress output at all.
    pub fn any(&self) -> bool {
        self.disasm.is_some()
            || self.bbv
            || self.viz
            || self.facts.is_some()
            || self.viz_facts.is_some()
            || self.stats
            || self.opsize
            || self.ctxedge
            || self.clsfact
            || self.propgap
            || self.cfg
            || self.peel
            || self.redundant
            || self.trace_cell.is_some()
            || self.trace_field.is_some()
            || self.trace_site.is_some()
    }

    /// Whether `source_id`'s bytecode should be disassembled.
    pub fn disasm_for(&self, source_id: u32) -> bool {
        self.disasm
            .as_ref()
            .is_some_and(|ids| ids.is_empty() || ids.contains(&source_id))
    }
}

/// Instrumentation that deliberately CHANGES the generated code.
///
/// Kept apart from [`Diagnostics`] on purpose: everything there is required
/// to leave codegen byte-identical, and that invariant is worth more than the
/// convenience of one more bool. Anything here emits real instructions and is
/// never on in production.
#[derive(Clone, Debug, Default)]
pub struct Instrumentation {
    /// Emit `night_runtime_census(kind, id)` calls: one per version entry
    /// tagged with its track, and one on each arm of the effect-flag and
    /// construct forks. Answers what fraction of *executed* work runs on the
    /// Opt track, which no static census can. Needs a shell that exports the
    /// helper; without one the switch is silently inert.
    pub census: bool,
    /// Emit `night_runtime_census(kind, id)` calls on every arm of every
    /// speculation point in the property and arithmetic lowerings: one kind
    /// per arm, `id` packing `(sid << 16) | evidence pc`. Answers what no
    /// static census can -- whether the guards the emitter armed actually
    /// HIT, which is the prediction-accuracy question the Opt-track reach
    /// work bottoms out in. Same helper and same dump as `census`; the kinds
    /// are disjoint, so the two can run together.
    pub guards: bool,
    /// Emit `night_runtime_census(70, id)` at the head of every block an
    /// op's lowering created, paired with a static `blockcen` record of the
    /// block's role and instruction classes: EXECUTED emitted IR per
    /// executed op, which no emitted-IR census can give (`bbv/blockcen.rs`,
    /// joined by `tools/blockprof.py`).
    pub blocks: bool,
}

/// Options for a whole compilation.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Leave every script interpreted. A triage switch: it isolates whether
    /// a failure comes from compiled code without rebuilding.
    pub force_interp: bool,
    pub diagnostics: Diagnostics,
    pub instrument: Instrumentation,
}
