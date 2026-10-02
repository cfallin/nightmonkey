//! Heuristic tuning constants.
//!
//! Every constant here is a *policy* level, not a correctness or ABI
//! requirement: changing one changes how much the compiler speculates, how
//! long it is willing to spend, or how large an output it will accept, and
//! never whether the result is right. They live together so the whole
//! speculation budget can be read in one place instead of being discovered
//! one `const` at a time.
//!
//! Structural limits that mirror an engine layout, a wire format or a wasm
//! spec limit are not here -- those belong next to the code that encodes
//! them, because a different value there is a bug, not a tuning choice.

// --- analysis: contexts and callee sets ----------------------------------

/// Context-chain depth cap.
pub(crate) const CTX_DEPTH_CAP: u8 = 8;

/// Distinct callees at a site before the bind degrades to CTX0.
pub(crate) const CALLEE_CAP: usize = 4;
/// Members a class region may have and still get a field view (a write
/// through an `AnyOf` receiver lands in the region view, linked into every
/// member's class view). Linking is O(members) once per (region, name);
/// past this the region is treated as megamorphic and the write dropped.
/// The callee cap is the wrong bound here: real class hierarchies commonly
/// have 20+ members, well past a call site's typical target count.
pub(crate) const REGION_VIEW_CAP: usize = 64;

/// Total context instantiations. Raising it to 1M produces bit-identical
/// facts on the corpus while costing tens of seconds on a large bundle, so
/// this level is the compile-time gate and nothing is lost to it.
pub(crate) const CTX_BUDGET: u64 = 50_000;

/// Cap on the per-site callee set the translator consumes: beyond this the
/// guard chain costs more than the generic dispatch saves. Independent of
/// `CALLEE_CAP`, which bounds context binding rather than emitted facts.
pub const MAX_SITE_TARGETS: usize = 4;

/// Cap on collected fn-table members (drops are censused).
pub(crate) const TABLE_MEMBER_CAP: usize = 2048;

// --- analysis: heap walks ------------------------------------------------

/// Max proto-chain hops walked by `chain_join`.
pub(crate) const CHAIN_DEPTH: usize = 8;

/// Formals the analysis carries a per-argument cell for. Past this a call
/// binds nothing and the callee's formal reads stay unresolved.
///
/// Note the two numberings this sits between: the analysis counts formals
/// from 0 (`FormalIndex`), while the fact tables put the receiver at 0 and
/// formal `n` at `n + 1` (`ArgIndex`). A loop over the fact-table row is
/// therefore `0..=MAX_TRACKED_FORMALS`, not `0..`.
pub(crate) const MAX_TRACKED_FORMALS: u32 = 8;

/// Max primary (`Write`/`Deleg`) construction events recorded per script:
/// the slot-order evidence a layout row is expanded from.
pub(crate) const PRIMARY_EVENT_CAP: usize = 64;

/// Max construction events of any kind per script. Only the `this.m(...)`
/// channel can reach it, since it does not count as a primary and so
/// nothing else would stop it.
pub(crate) const TOTAL_EVENT_CAP: usize = 128;

/// Max method homes considered when attributing a script to a class.
pub(crate) const MAX_HOMES: usize = 8;

/// Max distinct receiver class labels a property site accumulates before
/// it stops being evidence for anything (the region rung's input).
pub(crate) const RECV_LABEL_CAP: usize = 8;

/// Max predicted fixed-slot fields per class layout row.
pub(crate) const LAY_CAP: usize = 16;

/// Max constructor-delegation hops followed when expanding a layout row
/// (`Base.call(this, ...)` chains, `this.init(...)` splices).
pub(crate) const MAX_DELEG_DEPTH: u32 = 8;

/// Depth of the index-of / element-chain def walk.
pub(crate) const IOF_WALK_DEPTH: u32 = 8;

// --- translation: what the compiler will take on -------------------------

/// Hard cap on emitted SSA values: a refined pass that overruns this
/// descends the overflow ladder (fanout-off, then GEN-only); the workqueue
/// drain aborts early once past it. Structural version identity bounds the
/// version count but not the emitted size, and the wasm function-size limit
/// and relooper tail duplication are real and independent of it.
//

// --- translation: the versioning fixpoint --------------------------------

// --- translation: inlining -----------------------------------------------

/// Callee size cap for a polymorphic (guard-chain) inline arm.
pub(crate) const MAX_INLINE_POLY_BYTES: usize = 500;

/// Targets a polymorphic site may splice before it stays a generic call.
pub(crate) const MAX_INLINE_TARGETS: usize = 4;

/// Per-caller splice cap. This is an icache tuning: past a small number of
/// inlined call sites per caller the added footprint raises the icache miss
/// rate faster than it removes call overhead; below the cap the trade
/// reverses.
pub(crate) const MAX_INLINE_SITES: u32 = 8;

/// Cap on the closure a construct admission may drag in -- what the splice
/// transitively pulls in, not just the callee's own size.
///
/// Constructs get their own, much smaller budget because size does not
/// separate the winning splices from the losing ones. Benefit does, and a
/// ctor splice earns exactly one thing -- the field-init stores running in
/// the caller against a provably fresh `this` -- so its payoff is small and
/// Fixed however large its closure. A call splice's payoff scales with what
/// it removes, so it keeps the generous per-target caps.
///
/// The level is one CALL_COST: a ctor with a real call out prices above it,
/// a plain field-init ctor below. Pricing the site by what it emits is what
/// this buys over a syntactic "the ctor contains a call" test -- a proven
/// apply-forward is one helper call with no classify diamond, so it stays
/// cheap and its ctor stays eligible.
pub(crate) const CONSTRUCT_CLOSURE_CAP: usize = 300;

/// Inline arm only for small array literals: giant data-table literals
/// (thousands of InitElemArray ops) would inflate compile time for one-shot
/// init code; past the cap the generic helper is fine.
pub(crate) const INLINE_INIT_ELEM_CAP: u32 = 16;

// --- regex ---------------------------------------------------------------

/// Backtracks before giving up and deferring to the interpreter.
pub(crate) const BT_BUDGET: u32 = 1 << 27;

/// Translation caps: oversized/pathological programs stay interpreted.
pub(crate) const MAX_BYTECODE_LEN: usize = 1 << 17;
pub(crate) const MAX_BT_LABELS: usize = 8192;

// --- diagnostics ---------------------------------------------------------

// --- guard-arm census kinds ----------------------------------------------

/// Census kinds for `Instrumentation::guards`: one per arm of each
/// speculation point, so a run's counts give the per-site hit rate of every
/// guard the emitter armed. Disjoint from the track-census kinds (1/2/3,
/// 47, 48/50) so both instruments can run in the same build.
///
/// The property ladder's kinds mirror DESIGN.md section 5.2: `L1*` are the
/// class-fact arms (the analysis's own prediction), `IC_*` the per-site
/// inline cache below them. A site's total executions are the sum over its
/// kinds, and "the prediction held" is the L1 share of that.
pub(crate) mod census {

}
