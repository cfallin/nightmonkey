//! Compiler options: the tuning parameters and diagnostic switches the
//! toplevel entry points accept.
//!
//! Everything here is either a production parameter or a diagnostic that
//! produces output without changing codegen. There are deliberately no
//! switches that select between codegen designs: the compiler has one
//! lowering strategy and one analysis, and they are not configurable. The
//! one exception is [`Pipeline`], which can restrict a compilation to the
//! baseline tier (`docs/BASELINE.md`, `docs/MIR.md`).
//!
//! [`Options::apply_flag`] is the one parser for compiler flags: the
//! `nightmonkey` CLI and the in-process build's option string both go
//! through it.

/// Write one line of diagnostic output.
///
/// The switches in [`Diagnostics`] produce a structured line stream on
/// stderr. Tools parse the `night: ...` lines with anchored patterns
/// (`--dump-tiers`, the census maps), so they must reach the stream
/// verbatim: they cannot go through
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
    /// Write the analysis fact tables to this path (see `likelier::dump`).
    pub facts: Option<String>,
    /// Write the visualizer's per-script records (bytecode, MIR, waffle IR
    /// and their links; `tools/viz.py`) to this path, one JSON object per
    /// line.
    pub viz: Option<String>,
    /// Report analysis and translation timings and per-phase counts.
    pub stats: bool,
    /// Emit the per-op emitted-IR census: one record per emitted op
    /// instance with the waffle blocks and instructions its lowering
    /// added, split by instruction class. Static code-size attribution.
    pub opsize: bool,
    /// Emit one record per property-access site the analysis leaves without
    /// a `prop_sites` row, naming the gate that refused. A site with no row
    /// falls to the inline cache, which is the same ~540 bytes at every one
    /// of them, so this is the coverage half of the code-size question --
    /// `--dump-clsfact` says whether a consumer wanted a fact, this says why
    /// the analysis never made one.
    pub propgap: bool,
    /// Trace every raise into one analysis cell, named `arg:<sid>:<n>` or
    /// `local:<sid>:<n>`: the incoming object type and the constraint
    /// responsible. Answers "which writer made this slot AnyObject", which
    /// no census can, because the answer is one join step inside the solver.
    pub trace_cell: Option<String>,
    /// Trace every heap read and write of one property name.
    pub trace_field: Option<String>,
    /// After the analysis fixpoint, re-evaluate every live constraint once
    /// and report any cell that still grows: a dependency the solver does
    /// not re-fire on. Always on (and fatal) in debug-assertion builds.
    pub verify_fixpoint: bool,
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
        self.facts.is_some()
            || self.stats
            || self.opsize
            || self.propgap
            || self.trace_cell.is_some()
            || self.trace_field.is_some()
            || self.verify_fixpoint
            || self.trace_site.is_some()
            || self.tiers
            || self.mir
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
    /// Bucket the dense-append helper's misses by reason
    /// (`census::SETELEM_APPEND_WHY`): `night_runtime_census` calls, dumped
    /// at exit.
    pub guards: bool,
    /// Emit `night_runtime_census(MIR_BLOCK_CENSUS_KIND, id)` at the head of
    /// every MIR block: how often each block runs.
    pub blocks: bool,
    /// Emit `night_runtime_census(MIR_ROOT_CENSUS_KIND, id)` at every MIR
    /// rooting site that stores (a GC call's `root`, an edge's slot
    /// conform, a terminator's retain flush), and print the static
    /// `night: mir root <id> sid#<s> <where> <op> stores <n> cold <c>` map
    /// while compiling: the executed rooting stores, by site.
    pub roots: bool,
    /// Emit `night_runtime_census(MIR_VALUE_CENSUS_KIND, id)` at the head
    /// of every lowered Wasm block, and print the static
    /// `night: mir vblock <id> sid#<s> <tag>:<n>...` map of the Wasm values
    /// in it by the MIR op that emitted them (or `(entry)`, `(edges)`,
    /// `(hubs)`): executed Wasm instructions, by MIR op.
    pub values: bool,
    /// Emit `night_runtime_census(90, id)` at every MIR exit, and print the
    /// static `night: mir exit <id> sid#<s> pc <p> <mode>` map while
    /// compiling: how often each exit is taken, which is where a MIR body's
    /// time goes to baseline.
    pub mir_exits: bool,
}

/// The census kind of MIR exits (`Instrumentation::mir_exits`).
pub const MIR_EXIT_CENSUS_KIND: u32 = 90;
/// The census kind of MIR guard failures that exit, by guard (with
/// `--mir-exit-census`): an exit's block is shared by its pc's guards.
pub const MIR_GUARD_CENSUS_KIND: u32 = 92;
/// The census kind of MIR property-get IC misses (with `--mir-exit-census`).
pub const MIR_GET_MISS_CENSUS_KIND: u32 = 91;
/// The census kind of split ops' runtime-helper calls (`getprop.data`,
/// `setprop.data`, `getelem.data`, `setelem.data`, `prim.*`), with
/// `--mir-exit-census`.
pub const MIR_SLOW_CENSUS_KIND: u32 = 97;
/// Census kind for `--block-census` under MIR: one count per MIR block.
pub const MIR_BLOCK_CENSUS_KIND: u32 = 92;
/// Census kind for `--root-census`: one count per executed rooting site.
pub const MIR_ROOT_CENSUS_KIND: u32 = 93;
/// Census kind for `--value-census`: one count per executed Wasm block.
pub const MIR_VALUE_CENSUS_KIND: u32 = 94;

/// Which compiled tiers a script may use (`docs/BASELINE.md` §5).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Pipeline {
    /// The baseline tier only. A script baseline declines is interpreted.
    Baseline,
    /// MIR where the builder accepts, over baseline; baseline alone where
    /// it declines; the interpreter where baseline declines too. The
    /// default.
    #[default]
    Mir,
}

impl std::str::FromStr for Pipeline {
    type Err = String;
    fn from_str(s: &str) -> Result<Pipeline, String> {
        match s {
            "baseline" => Ok(Pipeline::Baseline),
            "mir" => Ok(Pipeline::Mir),
            _ => Err(format!(
                "bad pipeline `{s}` (expected baseline or mir)"
            )),
        }
    }
}

/// Options for a whole compilation.
#[derive(Clone, Debug, Default)]
pub struct Options {
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
            "--dump-propgap" => d.propgap = true,
            "--dump-tiers" => d.tiers = true,
            "--dump-mir" => d.mir = true,
            "--trace-cell" => d.trace_cell = Some(arg(flag)?),
            "--trace-field" => d.trace_field = Some(arg(flag)?),
            "--verify-fixpoint" => d.verify_fixpoint = true,
            "--trace-site" => d.trace_site = Some(arg(flag)?),
            "--dump-facts" => d.facts = Some(arg(flag)?),
            "--viz" => d.viz = Some(arg(flag)?),
            "--guard-census" => self.instrument.guards = true,
            "--mir-exit-census" => self.instrument.mir_exits = true,
            "--block-census" => self.instrument.blocks = true,
            "--root-census" => self.instrument.roots = true,
            "--value-census" => self.instrument.values = true,
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
        let o = Options::parse_str("--trace-site 1:2").unwrap();
        assert_eq!(o.diagnostics.trace_site.as_deref(), Some("1:2"));
        assert_eq!(Options::parse_str("").unwrap().pipeline, Pipeline::Mir);
        assert!(Options::parse_str("--pipeline")
            .unwrap_err()
            .contains("needs an argument"));
        assert!(Options::parse_str("--pipeline legacy")
            .unwrap_err()
            .contains("bad pipeline"));
        assert!(Options::parse_str("-o x")
            .unwrap_err()
            .contains("unknown compiler option"));
    }
}
