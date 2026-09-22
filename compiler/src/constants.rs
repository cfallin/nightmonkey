/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

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

/// Size gate on a script the translator will attempt at all, in bytecode
/// terms: past it, the wasm function-size cap is the likelier outcome than a
/// compiled body, so the script stays interpreted.
pub(crate) const MAX_TRANSLATE_BYTECODE: usize = 128 * 1024;

/// Size gate on the body a call cell may be emitted into.
pub(crate) const CALL_CELL_SCRIPT_MAX_BYTECODE: usize = 16 * 1024;

/// Hard cap on emitted SSA values: a refined pass that overruns this
/// descends the overflow ladder (fanout-off, then GEN-only); the workqueue
/// drain aborts early once past it. Structural version identity bounds the
/// version count but not the emitted size, and the wasm function-size limit
/// and relooper tail duplication are real and independent of it.
//
/// Sized to clear real hot bodies that expand to a few hundred thousand
/// values on the full rung while still catching pathological bodies an
/// order of magnitude larger.
pub(crate) const MAX_BODY_VALUES: usize = 400_000;

// --- translation: the versioning fixpoint --------------------------------

/// How many times the `Code` pass may report the map not closed before the
/// whole map is stripped. See the closure check in `translate_script`.
pub(crate) const CLOSURE_MAX_TRIES: u32 = 3;

/// Rounds the `ContextOnly` fixpoint may take before the still-moving
/// versions are widened straight to the empty ctx. Convergence is guaranteed
/// without this (the lattice is finite and joins only descend), so the cap
/// is a compile-time bound, not a correctness one -- and widening to empty
/// is the safe direction: every lineage implies it.
///
/// The value is calibrated with headroom over the worst script measured in
/// the corpus (the interval fixpoint piggybacks on full rounds, so each
/// widening-rung raise can cost one), and it is only the floor of a cap that
/// scales with the version population (see the fixpoint loop): a flat cap
/// stripped scripts whose lost facts were the whole point of the analysis.
/// Stripping must leave the map closed, since the `Code` pass walks against
/// every ctx the fixpoint emitted under; an unclosed strip must never pass
/// silently.
pub(crate) const CTXONLY_MAX_ROUNDS: u32 = 48;

/// Rounds the stripped fixpoint may take to close after `strip_all`. Two is
/// the argued bound (the first stripped walk discovers the versions widening
/// brought in, the second confirms nothing moved); this leaves slack and is
/// a backstop, not a policy.
pub(crate) const STRIP_MAX_ROUNDS: u32 = 4;

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

/// Per-block instruction detail cap in the `--lower` view: a data-table
/// literal can expand to thousands of stores and the view only needs shape.
pub(crate) const VIZ_BLOCK_INST_CAP: usize = 48;

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
    /// L1a: checkless immediate -- an upstream guard already proved it.
    pub(crate) const GET_L1A: u32 = 100;
    /// L1b: the folded SHALLOW|SLOTS(|RANGES) stamp test.
    pub(crate) const GET_L1B_HIT: u32 = 101;
    pub(crate) const GET_L1B_MISS: u32 = 102;
    /// L1c: the bare SLOTS bit test under a live identity fact.
    pub(crate) const GET_L1C_HIT: u32 = 103;
    pub(crate) const GET_L1C_MISS: u32 = 104;
    /// L1d: fused identity + SLOTS, the site-row arm with no live fact.
    pub(crate) const GET_L1D_HIT: u32 = 105;
    pub(crate) const GET_L1D_MISS: u32 = 106;
    /// L4/W0: the IC's monomorphic way, pre-decoded fixed-slot offset.
    pub(crate) const GET_IC_W0: u32 = 110;
    /// L4/W1: the IC's holder tail (proto holder or dynamic slot).
    pub(crate) const GET_IC_W1: u32 = 111;
    /// L4/W2: both inline ways missed, entering the poly/mega probe.
    pub(crate) const GET_IC_PROBE: u32 = 112;
    /// L4/W3: the probe missed too -- the full miss helper.
    pub(crate) const GET_IC_MISS: u32 = 113;
    /// The probe's receiver: 114 keyed by `(pc << 16) | (shape >> 3)`, so
    /// the count of distinct ids under one pc is the number of shapes the
    /// site sees; 115 keyed by the shape's immutable-flags word (which
    /// carries numFixedSlots and the slot span), site-blind.
    pub(crate) const GET_IC_PROBE_SHAPE: u32 = 114;
    pub(crate) const GET_IC_PROBE_SHAPE_FLAGS: u32 = 115;

    pub(crate) const SET_L1A: u32 = 120;
    pub(crate) const SET_L1_HIT: u32 = 121;
    pub(crate) const SET_L1_MISS: u32 = 122;
    pub(crate) const SET_IC_W0: u32 = 130;
    pub(crate) const SET_IC_MEGA: u32 = 131;
    pub(crate) const SET_IC_TRANS: u32 = 132;
    /// The add-transition replay whose proto validation the carried proof
    /// discharged (a subset of `SET_IC_TRANS`).
    pub(crate) const SET_IC_TRANS_PROVEN: u32 = 123;
    /// `GetGName` guarded-binding arms, by site: the per-binding value
    /// fuse served the read; the guarded slot load; the resolve leaf; the
    /// generic helper.
    pub(crate) const GNAME_FUSE_HIT: u32 = 181;
    pub(crate) const GNAME_SLOT_HIT: u32 = 182;
    pub(crate) const GNAME_RESOLVE: u32 = 183;
    pub(crate) const GNAME_HELPER: u32 = 184;
    pub(crate) const SET_IC_MISS: u32 = 133;

    /// The arithmetic guards: the typed fall-through against the generic
    /// helper arm that `bbv dirties` names as box2d's second entrance.
    pub(crate) const ARITH_FAST: u32 = 140;
    pub(crate) const ARITH_SLOW: u32 = 141;

    /// Opt -> Dirty transition actually EXECUTED, plus the op family that
    /// owns it: +0 property read, +1 property write, +2 arithmetic,
    /// +3 scripted call/new, +4 everything else. The dynamic twin of the
    /// `bbv dirties` static histogram.
    pub(crate) const DIRTY_ENTER: u32 = 150;

    /// Same event at an indirect (unresolved-callee) call, which never
    /// reaches `note_call_eff` and so was invisible to `DIRTY_ENTER`.
    /// A separate kind keeps the historical direct-call numbers comparable.
    pub(crate) const DIRTY_ENTER_IND: u32 = 155;
    /// A side arm's track step from Opt: the fall-off event NO other
    /// census could see, because it is not a call and not a guard miss --
    /// a typed-load ladder's other-type arm (a pure tag route) steps the
    /// lineage down purely for version identity, and since the Side->Dirty
    /// fold that step is a full track deopt. Participates in root
    /// attribution like kinds 150-155.
    pub(crate) const DIRTY_ENTER_SIDE_ARM: u32 = 156;
    /// A builtin arm's success exit joining the call op's generic merge
    /// (no keep state armed): the inline arm ran helper-free, and the
    /// lineage still drops to the post-call Dirty continuation.
    pub(crate) const DIRTY_ENTER_BUILTIN_MERGE: u32 = 158;

    /// Downstream-attribution bracket: PUSH right before a may-run-user-code
    /// call, POP right after it returns (the pop is in the caller, so it
    /// runs on the error path too -- wasm calls always return). The runtime
    /// keeps a stack of "most recent departure site" cells: a departure
    /// tick sets the top cell, a Dirty/Side version-entry tick attributes
    /// to it, and the bracket keeps a callee's internal departures from
    /// leaking into the caller's attribution. The runtime SYNTHESIZES kinds
    /// 5/6 from this: downstream Dirty/Side version entries per departure
    /// site -- the measured form of "recovering a departure pays in
    /// proportion to executed code downstream of it".
    pub(crate) const FRAME_PUSH: u32 = 60;
    pub(crate) const FRAME_POP: u32 = 61;
    /// `GetGName` served by a carried binding value fact (`Ctx::gcells`):
    /// the fuse/slot diamond ran with no tag ladder behind it.
    pub(crate) const GNAME_FACT_HIT: u32 = 62;
    /// A keep continuation re-proved its carried binding facts (the
    /// callee's word said a binding was written, or a helper ran).
    pub(crate) const GCELL_RECHECK: u32 = 63;

    /// A compiled inline arm demoted an existing object's stamp (claim-bit
    /// clear that found the bit set). The runtime advances the stamp epoch
    /// on receipt, mirroring the C++ chokes' unconditional bumps
    /// (vm/JSObject.h), so an unchanged epoch across a call bracket proves
    /// no stamp-guarded fact died. The runtime SYNTHESIZES from the
    /// comparison: kinds 11/12 = departures with stamps intact / broken,
    /// kinds 13/14 = downstream Dirty/Side version entries whose ROOT
    /// departure had stamps intact -- the population a keep-facts fork arm
    /// ("heap written, no stamps invalidated") could recover.
    pub(crate) const STAMP_DEMOTE: u32 = 65;

    /// Why a class-fact guard missed, read off the receiver's own class
    /// word on the miss arm: +0 the receiver is not an object at all, +1 it
    /// was never stamped (class idx 0), +2 the prediction named the WRONG
    /// class, +3 the right class with the SLOTS bit clear, +4 a bucket that
    /// should be unreachable (in range and stamped, yet the guard missed).
    /// The get and set arms report into the same buckets, offset by 10.
    pub(crate) const GET_MISS_WHY: u32 = 160;
    pub(crate) const SET_MISS_WHY: u32 = 170;

    /// Which edge of `SetElem`'s fast diamond sent execution to the generic
    /// helper: +0 receiver not an object, +1 key not an int32, +2 the
    /// predicted-TA arm missed (class, bounds, or value kind), +3 the
    /// receiver is a non-native object, +4 the append/hole check refused
    /// (growth past capacity, bail flags, row probe or proto guard miss),
    /// +5 the poly-TA probe returned false, +6 frozen elements.
    pub(crate) const SETELEM_WHY: u32 = 24;

    /// The interior of `night_elem_append_check`'s refusal (the SETELEM_WHY
    /// +4 bucket, split): kind = base + the helper's fail code. +1 append
    /// past capacity, +2 elements bail flags set (append or hole path), +3
    /// append-row probe miss, +4 proto live-shape guard miss, +5 the index
    /// is beyond the initialized length (neither append nor in-bounds), +6
    /// the in-bounds slot is not a hole. Guard-census builds only: the
    /// helper returns these codes instead of 0 and the call site tests
    /// `>= 8` and ticks the code before departing.
    pub(crate) const SETELEM_APPEND_WHY: u32 = 31;

    /// The constructor exit stamp's outcome, per ctor script: the class-fact
    /// guards' hit rate cannot exceed how often this store runs, so a guard
    /// that never hits is usually a stamp that never fired. Each refusal
    /// edge gets its own kind.
    pub(crate) const STAMP_BASE: u32 = 180;
    pub(crate) const RESTAMP_BASE: u32 = 190;
    pub(crate) const STAMP_OK: u32 = 0;
    pub(crate) const STAMP_NOT_OBJECT: u32 = 1;
    pub(crate) const STAMP_NOT_OWNED: u32 = 2;
    pub(crate) const STAMP_SHORT_SPAN: u32 = 3;
    pub(crate) const STAMP_ALREADY: u32 = 4;

    /// The receiver's own address, ticked on a class-fact miss. The count of
    /// DISTINCT ids is the answer: a handful means the misses come from
    /// long-lived singletons, millions means they come from fresh
    /// allocations that were never stamped.
    pub(crate) const GET_MISS_RECV: u32 = 165;
    pub(crate) const SET_MISS_RECV: u32 = 175;
    /// The receiver's whole class word, ticked on the same miss: names
    /// WHICH class the mispredicted receivers carry and which validity
    /// bits (SLOTS/TYPES/RANGES) they have lost.
    pub(crate) const GET_MISS_IDX: u32 = 166;
    pub(crate) const SET_MISS_IDX: u32 = 176;
    /// The class word a ctor-exit stamp found (id = the word), ticked on
    /// the STAMP_OK path: which validity bits survived construction.
    pub(crate) const STAMP_EXIT_WORD: u32 = 178;

    /// The construct fork's two arms. Arming a fork at more sites is worth
    /// nothing unless the ctor's returned word is actually zero there, and
    /// those are different numbers.
    pub(crate) const CTOR_FORK_CLEAN: u32 = 148;
    pub(crate) const CTOR_FORK_DIRTY: u32 = 149;
    /// The construct fork's keep-facts arm: the ctor's word carries MUT
    /// bits but not FLAG_STAMPS, so the caller rejoins Opt with its facts.
    /// The flag fork's twin arm reports as track-census kind 49 (beside
    /// kinds 48/50).
    pub(crate) const CTOR_FORK_STAMP: u32 = 147;
    /// The construct fork's dirty arm, plus which MUT bits of the runtime
    /// word blocked the clean arm: +0 none, +1 MUT_THIS, +2 MUT_OTHER,
    /// +3 both. `word` is `ct_delta | (callee_eff & MUT_OTHER)`, so a
    /// MUT_THIS here can only have come from the allocation path.
    /// (Keep clear of 180-194: the stamp/restamp outcome bands.)
    pub(crate) const CTOR_FORK_WHY: u32 = 196;
    /// The effect-flag fork's dirty arm, plus WHY the clean arm could not
    /// take: +0 the callee's raw word was dirty but FOLDED clean from this
    /// caller's perspective (a recoverable class the fork currently
    /// forfeits), +1 MUT_THIS, +2 MUT_OTHER, +3 both, +4 the callee
    /// returned an error. Keyed at the CALL's evidence pc (unlike kinds
    /// 48/50, which are keyed at next_pc) so it joins the departure and
    /// downstream records directly.
    pub(crate) const FLAG_FORK_WHY: u32 = 142;

    /// Reliance census: what the CHOSEN fast form's facts rest on -- the
    /// bytecode alone (intrinsic), a validated analysis claim, a tag test
    /// the emitter invented (the shadow analysis), or both. kind =
    /// RELY_BASE + family * 4 + Prov::class (0 intrinsic, 1 claim, 2 test,
    /// 3 mixed). Ticked only where a fast form was actually emitted on the
    /// strength of a ctx/operand fact, so a run's counts weight each site
    /// by executions; the test-backed rows, ranked, ARE the analysis gaps.
    pub(crate) const RELY_BASE: u32 = 66;
    pub(crate) const RELY_ARITH_I32: u32 = 0;
    pub(crate) const RELY_ARITH_NUM: u32 = 1;
    pub(crate) const RELY_STRING: u32 = 2;
    pub(crate) const RELY_CMP: u32 = 3;
    pub(crate) const RELY_PROP_OBJ: u32 = 4;
    pub(crate) const RELY_PROP_CLS: u32 = 5;
    pub(crate) const RELY_ELEM: u32 = 6;
    pub(crate) const RELY_IV_RUNG: u32 = 7;

    /// The on-ramp census, one TRY/OK pair per conform form: how often a
    /// Dirty lineage REACHES a conform chain, and how often the chain lets
    /// it back onto Opt. On-ramps are the only mechanism that returns
    /// execution to Opt without a fresh function entry, so these take rates
    /// bound how long a lineage dwells on Dirty after a call.
    ///
    /// 134-139 is clear of every other band; keep it that way.
    ///
    /// Loop header, from the shared funnel or a dirty entry edge:
    pub(crate) const ONRAMP_TRY: u32 = 134;
    pub(crate) const ONRAMP_OK: u32 = 135;
    /// A conform into the RECOVERY TWIN (the dirty cycle's back edge, or
    /// the twin's own excursion funnel): a site ticking TRY with no OK
    /// every iteration names a population whose Opt header fact is
    /// genuinely dead.
    pub(crate) const CYC_ONRAMP_TRY: u32 = 136;
    pub(crate) const CYC_ONRAMP_OK: u32 = 137;
    /// The just-in-time on-ramp at a call return: the keep fork's runtime
    /// proof failed, and the conform re-proves the successor's prediction
    /// instead of dwelling on GEN until the next loop header.
    pub(crate) const RET_ONRAMP_TRY: u32 = 138;
    pub(crate) const RET_ONRAMP_OK: u32 = 139;
}

/// Formals an apply-forward fast arm will fill from the caller's actuals.
/// The arm guards on the caller having passed exactly the callee's formal
/// count and then emits that many loads; past a handful it is a long
/// unrolled copy behind a guard that holds less and less often.
pub(crate) const APPLY_FWD_MAX_ARGS: u32 = 8;
/// Known-target arms an apply-forward site without a single target emits
/// (one patched identity compare each).
pub(crate) const APPLY_FWD_MAX_TARGETS: usize = 16;
