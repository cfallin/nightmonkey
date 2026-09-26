//! Compiler options: the tuning parameters and diagnostic switches the
//! toplevel entry points accept.
//!
//! Everything here is either a production parameter or a diagnostic that
//! produces output without changing codegen. There are deliberately no
//! switches that select between codegen designs: the compiler has one
//! lowering strategy and one analysis, and they are not configurable. The
//! one exception is [`Pipeline`], which selects between the legacy BBV
//! path and the baseline/MIR tiers (`docs/BASELINE.md`, `docs/MIR.md`)
//! while the latter replace the former, and is removed with it.
//!
//! [`Options::apply_flag`] is the one parser for compiler flags: the
//! `nightmonkey` CLI and the in-process build's option string both go
//! through it.

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
    /// Tier coverage: one `night: tier <sid> <tier>` line per translated
    /// script, naming the tier that compiled it (or `interp`) and every
    /// decline on the way, and a summary. Coverage is measured, never
    /// assumed.
    pub tiers: bool,
    /// Print each MIR body the builder produces (and an invalid one in
    /// full when the validator rejects it).
    pub mir: bool,
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
            || self.tiers
            || self.mir
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

/// Which compiled tiers a script may use (`docs/BASELINE.md` §5).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Pipeline {
    /// The legacy BBV lowering (OPT+GEN tracks).
    #[default]
    Legacy,
    /// The baseline tier only. A script baseline declines is interpreted.
    Baseline,
    /// MIR where the builder accepts, over baseline; baseline alone where
    /// it declines; the interpreter where baseline declines too.
    Mir,
}

impl std::str::FromStr for Pipeline {
    type Err = String;
    fn from_str(s: &str) -> Result<Pipeline, String> {
        match s {
            "legacy" => Ok(Pipeline::Legacy),
            "baseline" => Ok(Pipeline::Baseline),
            "mir" => Ok(Pipeline::Mir),
            _ => Err(format!(
                "bad pipeline `{s}` (expected legacy, baseline or mir)"
            )),
        }
    }
}

/// Options for a whole compilation.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Leave every script interpreted. A triage switch: it isolates whether
    /// a failure comes from compiled code without rebuilding.
    pub force_interp: bool,
    pub pipeline: Pipeline,
    /// Fail the compilation if any translated script ends up interpreted
    /// for a reason other than an allowed one (`ForceInterpreter`). This
    /// is how a test lane proves it ran compiled code (`DESIGN.md` §12).
    pub strict_coverage: bool,
    /// MIR guard-failure stress mode (`--mir-stress N`): every MIR guard
    /// also fails on every `N`th guard executed, program-wide, to exercise
    /// exits on code that would otherwise stay on the fast path. 0 = off.
    pub mir_stress: u32,
    /// The onramp-root policy for inner loops (`--mir-inner-onramp-bytes
    /// N`; `docs/BASELINE.md` §7): an inner loop gets an onramp root only
    /// when its outermost enclosing loop spans at most `N` bytecode bytes,
    /// since each such root side-enters the loops around it and waffle's
    /// reducifier duplicates code for that. 0 = outermost loops only.
    /// `None` = the default, [`Options::inner_onramp_bytes`].
    pub mir_inner_onramp_bytes: Option<u32>,
    pub diagnostics: Diagnostics,
    pub instrument: Instrumentation,
}

impl Options {
    /// The inner-loop onramp budget in effect (`mir_inner_onramp_bytes`).
    pub fn inner_onramp_bytes(&self) -> u32 {
        self.mir_inner_onramp_bytes.unwrap_or(400)
    }
}

impl Options {
    /// Apply one compiler flag. `next` yields the flag's argument, for the
    /// flags that take one. Returns `Ok(false)` for a flag that is not a
    /// compiler flag (the caller may own it).
    pub fn apply_flag(
        &mut self,
        flag: &str,
        next: &mut dyn FnMut() -> Option<String>,
    ) -> Result<bool, String> {
        let mut arg = |flag: &str| next().ok_or_else(|| format!("{flag} needs an argument"));
        let d = &mut self.diagnostics;
        match flag {
            "--force-interp" => self.force_interp = true,
            "--pipeline" => self.pipeline = arg(flag)?.parse()?,
            "--strict-coverage" => self.strict_coverage = true,
            "--mir-inner-onramp-bytes" => {
                self.mir_inner_onramp_bytes = Some(
                    arg(flag)?
                        .parse()
                        .map_err(|e| format!("--mir-inner-onramp-bytes: {e}"))?,
                )
            }
            "--mir-stress" => {
                self.mir_stress = arg(flag)?
                    .parse()
                    .map_err(|e| format!("--mir-stress: {e}"))?
            }
            "--stats" => d.stats = true,
            "--dump-opsize" => d.opsize = true,
            "--dump-ctxedge" => d.ctxedge = true,
            "--dump-clsfact" => d.clsfact = true,
            "--dump-propgap" => d.propgap = true,
            "--dump-cfg" => d.cfg = true,
            "--dump-peel" => d.peel = true,
            "--dump-redundant" => d.redundant = true,
            "--dump-tiers" => d.tiers = true,
            "--dump-mir" => d.mir = true,
            "--trace-cell" => d.trace_cell = Some(arg(flag)?),
            "--trace-field" => d.trace_field = Some(arg(flag)?),
            "--trace-site" => d.trace_site = Some(arg(flag)?),
            "--dump-bytecode" => d.disasm = Some(Vec::new()),
            "--dump-bbv" => d.bbv = true,
            "--dump-facts" => d.facts = Some(arg(flag)?),
            "--viz" => d.viz = true,
            "--viz-facts" => d.viz_facts = Some(arg(flag)?),
            "--viz-lower" => {
                d.viz = true;
                d.viz_lower = true;
            }
            "--census" => self.instrument.census = true,
            "--guard-census" => self.instrument.guards = true,
            "--block-census" => self.instrument.blocks = true,
            _ if flag.starts_with("--dump-bytecode=") => {
                let list = &flag["--dump-bytecode=".len()..];
                let ids = list
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| {
                        s.parse::<u32>()
                            .map_err(|_| format!("bad source id `{s}` in `{flag}`"))
                    })
                    .collect::<Result<Vec<u32>, String>>()?;
                d.disasm = Some(ids);
            }
            _ => return Ok(false),
        }
        Ok(true)
    }

    /// Options from a whitespace-separated string of compiler flags (the
    /// in-process build's option channel). Every word must be a compiler
    /// flag or a flag's argument.
    pub fn parse_str(s: &str) -> Result<Options, String> {
        let mut opts = Options::default();
        let mut words = s.split_whitespace().map(str::to_string);
        while let Some(w) = words.next() {
            if !opts.apply_flag(&w, &mut || words.next())? {
                return Err(format!("unknown compiler option `{w}`"));
            }
        }
        Ok(opts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_option_strings() {
        let o =
            Options::parse_str("  --pipeline baseline --dump-tiers\t--strict-coverage ").unwrap();
        assert_eq!(o.pipeline, Pipeline::Baseline);
        assert!(o.diagnostics.tiers && o.strict_coverage);
        let o = Options::parse_str("--dump-bytecode=3,4 --trace-site 1:2").unwrap();
        assert_eq!(o.diagnostics.disasm, Some(vec![3, 4]));
        assert_eq!(o.diagnostics.trace_site.as_deref(), Some("1:2"));
        assert_eq!(Options::parse_str("").unwrap().pipeline, Pipeline::Legacy);
        assert!(Options::parse_str("--pipeline")
            .unwrap_err()
            .contains("needs an argument"));
        assert!(Options::parse_str("--pipeline fast")
            .unwrap_err()
            .contains("bad pipeline"));
        assert!(Options::parse_str("-o x")
            .unwrap_err()
            .contains("unknown compiler option"));
    }
}
