/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Workqueue basic-block versioning: the one codegen path.
//!
//! The long form is `night/docs/DESIGN.md` section 4; this is the map.
//!
//! A version is `Ver { pc, class, track, depth }` -- STRUCTURAL identity, and
//! nothing else. It names a block. The token class and the depth are what
//! keep every cycle single-entry (DESIGN 4.9), so two versions may be
//! duplicates of one another for reducibility's sake alone.
//!
//! The FACT context is a different object, keyed by the program point and
//! by nothing else: one prediction per pc on Opt, and none at all on GEN,
//! which carries no facts. It is computed by `predict.rs` before any IR is
//! appended, and emission is a pure consumer of it -- codegen consults a
//! prediction and emits code that ENFORCES it, shunting any execution that
//! would diverge to GEN. It never mints a fact and never moves one.
//!
//! Every Opt block at a pc therefore reads the same prediction and emits
//! the same body. That is the test of the split: on an ISA admitting
//! irreducible control flow the duplicate blocks would simply disappear,
//! and no dynamic path's code would change.
//!
//! Version count is bounded by construction -- two tracks per (pc, token
//! class, depth) -- rather than by a minting budget. Contexts are never
//! hashed; the only interned thing is the token vector (`tok_class`), whose
//! class ids must name the same thing in every round and so persist across
//! them, as must the splice set (`Splices`), which owns synthetic pc space.
//!
//! `emit` drains a workqueue of versions and `run_version` lowers exactly one
//! bytecode op per version, so every op ends its block -- which is why "one
//! prediction per program point" and "one prediction per block entry" are
//! the same statement here. Every successor edge a lowering produces passes
//! through `cont` -> `theta` -> `cont_at`. `theta` is the only merge point
//! and holds no merge policy: it interns the structural identity and looks
//! up the pc's prediction. In the prediction pass it also joins the arrival
//! in, and re-arms every block at that pc if the prediction moved -- that
//! re-arm is the worklist, and there is no dependency graph beyond it. A
//! failed speculation is an ordinary edge to the GEN version of the same
//! successor pc: no deopt landings, no bailouts, no ahead-of-time plan.
//!
//! Whole-script inputs are restricted to syntactic structural facts: loop
//! extents, try-notes, and the atom/name tables.
//!
//! Module map:
//! - `ctx`      the context lattice (`SlotCtx`, `Ctx`), operands, type predicates
//! - `version`  `Ver`/`VerTable`, tokens, carriers, `theta`, `cont`, the driver
//! - `facts`    the sig2 flags word, effect classification, fact kills, store duty
//! - `emit`     the low-level wasm emission primitives and the diamond helpers
//! - `arms`     `ArmState` and `side_arm`: what a leaving diamond arm borrows
//! - `frame`    prologue, unwinding, write barriers, environments, locals, return
//! - `call`     call/construct dispatch; `inline` the splice machinery
//! - `generator` the suspend/resume state machine for generator and async bodies
//! - `ops`      `emit_op` dispatch, with the lowerings in `arith`, `compare`,
//!              `property`, `element`, `gname`, `object`
//! - `predict`  the prediction: one fact context per program point
//! - `licm`     the post-emission reducibility assert and LICM pass
//! - `viz`      the diagnostic dumps

use crate::constants::{
    census, APPLY_FWD_MAX_ARGS, APPLY_FWD_MAX_TARGETS, CALL_CELL_SCRIPT_MAX_BYTECODE,
    CLOSURE_MAX_TRIES, CONSTRUCT_CLOSURE_CAP, IOF_WALK_DEPTH, MAX_BODY_VALUES,
    MAX_TRANSLATE_BYTECODE,
};
pub(crate) mod abi;
mod arith;
mod arms;
mod blockcen;
mod call;
mod cfg;
pub use call::build_call_classify_helper;
pub use element::build_elem_append_helper;
pub use property::{build_elem_mega_helpers, build_ic_set_cold_helper};
mod compare;
mod ctx;
mod element;
mod emit;
mod facts;
mod frame;
mod generator;
mod gname;
mod inline;
mod licm;
mod live;
mod object;
mod ops;
mod outline;
mod predict;
mod property;
mod redundant;
mod version;
mod viz;

pub use abi::EARLY_KEY_MAX;
pub(crate) use abi::*;
pub(crate) use ctx::*;
use licm::{assert_reducible, licm};
use version::{VerId, VerTable};
pub(crate) use viz::{viz_claim_str, viz_prims_str, viz_sanitize, viz_script_name};
use viz::{viz_cls_range, viz_op_args};

use waffle::{
    Block, BlockTarget, Func, FunctionBody, Memory, MemoryArg, Module, Operator, Terminator, Type,
    Value, ValueDef,
};

use super::effects;
use super::effects::{EffectClass, HeapKind, HelperMeta};
use super::translate;
use super::translate::{
    branch_target, max_locals, AddPred, ArgIndex, AtomTable, Claim, FuseCallPatch, FusedGname,
    Helpers, LikelyFacts, NameId, Outcome, Pc, Prims, PropSiteIn, ScriptId, Site, StampCtorIn,
    StampKey, TranslateCtx, ValueRange, ALL_PRIMS, APPEND_CACHE_ENTRY_BYTES, APPEND_CACHE_SIZE,
    BC_ARRAY_CTOR, BC_ARR_POP, BC_ARR_PUSH, BC_PARSE_INT, ELEMENTS_POP_BAIL_MASK,
    MAGIC_ELEMENTS_HOLE, MAGIC_GENERATOR_CLOSING, MAGIC_IS_CONSTRUCTING, MAGIC_NO_ITER_VALUE,
    MAGIC_UNINITIALIZED_LEXICAL, MN_ABS, MN_CEIL, MN_CLZ32, MN_COS, MN_FLOOR, MN_FROUND, MN_IMUL,
    MN_MAX, MN_MIN, MN_POW, MN_SIN, MN_SQRT, MN_TRUNC, NATIVE_ROUTE_SCRIPT_MAX_BYTECODE,
    PRIM_BIGINT, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_STRING, PRIM_SYMBOL,
    PRIM_UNDEFINED, TAG_BIGINT_HI, TAG_BOOLEAN, TAG_CLEAR, TAG_INT32, TAG_MAGIC, TAG_NULL,
    TAG_OBJECT, TAG_STRING, TAG_SYMBOL, TAG_UNDEFINED,
};
use crate::bytecode::{BytecodeParser, JSOp, OpcodeVisitor, Script, TryNoteKind};
use crate::opsem;
use crate::options::Options;
use crate::source::{Source, SourceObject, SourceObjectId};
use crate::view::TypeDesc;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use waffle::cfg::CFGInfo;
use waffle::entity::EntityRef;

// The byte layouts the emitted code addresses live in `abi`.

/// Add-arm predicted-slot check resolution (emit_add_slots_check).
#[derive(Clone)]
enum AddCheck {
    /// Atom predicted at this byte offset; any other assigned offset
    /// clears SLOTS.
    Predicted(u32),
    /// Atom unpredicted anywhere in the receiver's clump; an assigned
    /// offset below `own` (the receiver's own layout byte bound) clears
    /// SLOTS, one in `own..bound` keeps it and sets ADV_INELIGIBLE.
    Unpredicted { bound: u32, own: u32 },
    /// Receiver layout not static: compare the receiver's runtime key
    /// against the atom's prefix-closed (k+1, off) prediction pairs; an
    /// unmatched in-bound add clears SLOTS. Empty pairs = pure
    /// conservative (every in-bound add clears).
    Runtime(Vec<AddPred>),
}

/// The construct-time allocation word for a resolved `new` site (see
/// translate.rs `early_stamp_word`): sentinel + early key + all three
/// validity bits seeded optimistically -- construction's checked stores
/// maintain them and the ctor-exit stamp carries forward whichever
/// survived. A key past the early-key space degrades gracefully: no key
/// means the engine add hook cannot check predictions, so SLOTS must not
/// be seeded.
/// `keep_shallow`/`keep_ranges`: seed SHALLOW/RANGES only when the
/// resolved layout has masked fields / range claims -- a vacuous bit
/// protects nothing and turns every engine-path non-number store into a
/// demote-and-epoch-bump (see the exit stamp's matching gate).
fn early_stamp_word(k_plus_1: u32, keep_shallow: bool, keep_ranges: bool) -> u32 {
    let validity = CLASS_WORD_SLOTS
        | if keep_shallow { CLASS_WORD_SHALLOW } else { 0 }
        | if keep_ranges { CLASS_WORD_RANGES } else { 0 };
    if k_plus_1 <= EARLY_KEY_MAX {
        CLASS_WORD_SENTINEL | validity | (k_plus_1 << EARLY_KEY_SHIFT)
    } else {
        CLASS_WORD_SENTINEL | validity
    }
}

// --- block keys ----------------------------------------------------------

/// Pc-space cap. Scripts are capped at 128 KiB of bytecode (the translate
/// size gate) and inline segments are allocated above the root's bytecode in
/// the same space, so 24 bits bounds both.
const MAX_PC: u32 = (1 << 24) - 1;

// The token dimension is a per-enclosing-loop layer marker -- peel
// (acyclic at this level), cycle (steady non-Opt cycling), OPT (the Opt
// cycle) -- i.e. the 2-sides x depth-layers lattice in vector form.
// Capping the marker on a cycling lineage is a trap: the versions it would
// save are paid back with interest in relooper tail duplication, because
// the merged lineage is irreducible.

/// One conform guard's kind: a tag test on a boxed source, or an
/// exactness compare on an exact-integer (I64) carrier whose target wants
/// int32.
#[derive(Clone, Copy, Debug)]
enum ProofGuard {
    Tag,
    ExactI64,
    /// An unboxed f64 carrier re-proving exact int32: the wrap/convert
    /// round-trip plus an explicit negative-zero rejection (unlike the
    /// integer carrier, an f64 CAN hold -0, which round-trips through 0 and
    /// compares equal).
    ExactF64,
    /// An unboxed i32 arrival whose interval claim would widen the target
    /// slot's stored interval (entry-form onramps never join): a runtime
    /// bounds check against the stored interval proves containment
    /// exactly, so the slot delivers the stored interval unchanged and
    /// the edge is admitted instead of declined. The stored interval
    /// licenses rung cutovers (overflow-check elision), so nothing weaker
    /// than exact containment may pass.
    IvRange,
}

/// The call-return on-ramp's admission budget: one conform guard per this
/// many bytes of recovered bytecode (`ret_onramp_admits`).
///
/// Generous, and the measurement says it should be. The standing constraint
/// -- a proof that can fail, on an edge that runs every iteration, is
/// worse than a weak prediction -- is about conforms that FAIL. This one
/// does not: the guard census puts its take rate near 100% on richards,
/// because a call return's guards ask about facts the callee's
/// write did not touch. Where the guards pass, paying more of them to
/// recover more code is the right trade, and the budget only has to stop
/// a long chain from being emitted to recover three ops.
const RET_ONRAMP_BYTES_PER_GUARD: u32 = 8;

/// Which slot of the arriving lineage a proof gap names.
#[derive(Clone, Copy, Debug)]
enum ProofSrc {
    Stack(usize),
    Local(u32),
    /// Slot 0 is `this`; slot `1 + i` is formal `i`.
    ArgSlot(usize),
    /// A slot of the CALLER's frame, addressed inside a spliced segment.
    /// A splice carries the caller's frame facts into the segment ctx by
    /// construction, so a header inside a segment claims them and a proof
    /// edge to it has to discharge them like any other slot. The frame is
    /// flat memory and the parent segment's view addresses it, so this is a
    /// load and a test -- and the slot cannot have been reassigned, because
    /// a splice cannot write the caller's frame.
    CallerLocal(u32),
    /// Slot 0 is the caller's `this`; slot `1 + i` is its formal `i`.
    CallerArgSlot(usize),
    /// A global binding's value fact (`Ctx::gcells`), by binding id: the
    /// operand is the binding's value cell and the guard is the cell's
    /// fuse word AND the tag test.
    GCell(u32),
}

/// Which caller-frame slot `caller_operand_for_edge` should load.
#[derive(Clone, Copy)]
enum CallerSlot {
    Local(u32),
    /// Slot 0 is `this`; slot `1 + i` is formal `i`.
    Arg(usize),
}

/// What `proof_gaps` decided: the guards a proof edge to some target
/// fact context owes, and the interval each slot would deliver across it.
struct ProofPlan {
    gaps: Vec<(ProofSrc, SlotCtx, ProofGuard)>,
    iv_stack: Vec<Option<ValueRange>>,
    iv_locals: Vec<Option<ValueRange>>,
    iv_args: Vec<Option<ValueRange>>,
}

/// The shared peel: the acyclic-at-this-level marker. All acyclic chains
/// of a loop -- mid-body track-steps, side entries, and every distinct
/// outer history -- share the one funnel class this names. It never appears
/// on a cycling edge: a TOK_PEEL version's only way to cycle is through a
/// header, which hands out its side's cycle marker, so the funnel is
/// acyclic by construction.
const TOK_PEEL: u64 = u64::MAX - 2;

/// The depth re-label: the one token a non-OPT header hands its body.
/// A non-Opt lineage's per-loop marker is thus peel (transitional at that
/// level) or cycle (steady dirty cycling), nothing else, so the token
/// vector is exactly a per-depth layer label.
const TOK_CYCLE: u64 = u64::MAX - 3;

/// The OPT-cycle layer marker: what an Opt header hands its body, in place
/// of the header's own interned key (those keys measured
/// information-free corpus-wide). The OPT side has one layer, so one
/// marker; on-ramp layers add depth indices on this side.
const TOK_OPT: u64 = u64::MAX - 4;

/// The recovery-twin layer marker: the Opt copy of a loop header that the
/// loop's own dirty cycle conforms back into (the on-ramp layer the
/// TOK_OPT note anticipates). It rides as an OWN-LOOP entry on the twin
/// header's token vector -- the twin-header form `out_tokens_for`'s header
/// rule special-cases -- so the twin's identity never collides with the
/// steady header. Reducibility: the twin is entered ONLY by proof edges
/// (from the dirty cycle's back edge and from its own excursion funnel),
/// all of whose sources the dirty header dominates, so the composite
/// {dirty cycle, twin} region is a natural loop headed at the dirty
/// header with the twin as a nested single-entry cycle inside it.
const TOK_RECOVER: u64 = u64::MAX - 5;

/// The recovery twin's own excursion funnel: acyclic like TOK_PEEL, but a
/// separate class (one extra funnel per loop, a constant, not the
/// per-outer-history explosion) so its back-edge conform re-targets the
/// TWIN and never couples the steady cycle through the shared funnel --
/// which is what would otherwise make the composite region irreducible. Its
/// conform-fail bail is the dirty header, like every funnel's.
const TOK_RECOVER_PEEL: u64 = u64::MAX - 6;

/// The per-lineage accumulator: Const = a compile-time word (no code; 0 = nothing
/// effectful yet, FLAGS_ALL = saturated, MUT_THIS alone = own-this store
/// arms on this lineage), Dyn = the live OR chain's SSA value plus a
/// CONST OVERLAY of bits OR'd since -- deferred to materialization so that
/// const contributions (leaf writes, classified store bits) never mint a
/// value mid-arm and never have to saturate the whole word to stay inside
/// their dominance region.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum FlagsAcc {
    Const(u32),
    Dyn(Value, u32),
}

/// Splice admission fuel. Inlining is the one remaining decision priced in
/// emitted values -- version count is bounded by construction -- so it gets
/// a budget of its own rather than sharing a global one.
const SPLICE_FUEL_VALUES: usize = 100_000;

/// The small-callee exemption line for the fuel gate (see the splice-fuel
/// check): callees at or below this bytecode length may splice past
/// `SPLICE_FUEL_VALUES` until the harder value line below -- a tiny
/// callee left as a call kills the facts of the whole loop that contains
/// it, once per iteration.
const SMALL_SPLICE_BC: usize = 160;
const SMALL_SPLICE_FUEL_VALUES: usize = 250_000;

// Deliberately per-admission and not cumulative: total size is not the
// failure mode, a single over-reaching admission is. The fuel cap already
// bounds a body's total growth, and in emitted values rather than an
// estimate.

/// Every call/construct pc in `script` with its op, for closure pricing.
fn call_site_pcs(script: &Script) -> Vec<(u32, JSOp)> {
    struct Scan(Vec<(u32, JSOp)>);
    impl OpcodeVisitor for Scan {
        fn before_op(&mut self, pc: Pc, op: JSOp, _nuses: usize, _ndefs: usize) {
            if matches!(op, JSOp::Call | JSOp::CallIgnoresRv | JSOp::New) {
                self.0.push((pc.get(), op));
            }
        }
    }
    script.parser().visit(Scan(Vec::new())).0
}

/// Locals that are this aliases: every assignment is the adjacent
/// `FunctionThis; SetLocal n` (or InitLexical) pattern -- the compiled form
/// of `var self = this`, which is how code ported from languages with an
/// explicit receiver reaches its own `this` for every store. A store whose
/// receiver provenance is such a local is a store through the frame's own
/// `this`. Frame locals have no aliases (captured bindings
/// compile to AliasedVar ops), so the pattern is exact.
fn compute_this_alias_locals(script: &Script) -> HashSet<u32> {
    struct Scan {
        prev_was_this: bool,
        after_this: bool,
        candidates: HashSet<u32>,
        disqualified: HashSet<u32>,
    }
    impl OpcodeVisitor for Scan {
        fn before_op(&mut self, _pc: Pc, op: JSOp, _nuses: usize, _ndefs: usize) {
            self.after_this = self.prev_was_this;
            self.prev_was_this = matches!(op, JSOp::FunctionThis);
        }
        fn set_local(&mut self, localno: u32) {
            if self.after_this {
                self.candidates.insert(localno);
            } else {
                self.disqualified.insert(localno);
            }
        }
        fn init_lexical(&mut self, localno: u32) {
            self.set_local(localno);
        }
    }
    let scan = script.parser().visit(Scan {
        prev_was_this: false,
        after_this: false,
        candidates: HashSet::default(),
        disqualified: HashSet::default(),
    });
    scan.candidates
        .difference(&scan.disqualified)
        .copied()
        .collect()
}

/// The locals-into-SSA candidate set: every local the script touches, and
/// -- as `STALE_ARG | argno` keys -- every formal it reads or writes (a
/// mapped-arguments frame carries no formal: `carried_out` filters).
/// The whole formal set rides rather than just the written ones: a loop
/// header entered once from above carries every formal raw around the
/// loop, and dropping the unwritten ones would reintroduce their frame
/// loads at each read.
fn hot_locals(script: &Script) -> Vec<u32> {
    struct Scan {
        seen: HashSet<u32>,
    }
    impl OpcodeVisitor for Scan {
        fn get_local(&mut self, localno: u32) {
            self.seen.insert(localno);
        }
        fn set_local(&mut self, localno: u32) {
            self.seen.insert(localno);
        }
        fn init_lexical(&mut self, localno: u32) {
            self.seen.insert(localno);
        }
        fn get_arg(&mut self, argno: u16) {
            self.seen.insert(STALE_ARG | u32::from(argno));
        }
        fn set_arg(&mut self, argno: u16) {
            self.seen.insert(STALE_ARG | u32::from(argno));
        }
    }
    let scan = script.parser().visit(Scan {
        seen: HashSet::default(),
    });
    let mut hot: Vec<u32> = scan.seen.into_iter().collect();
    hot.sort_unstable();
    hot
}

// The structural-input scans (uses_env_ops / uses_arguments /
// uses_new_target / uses_actual_args / env_unsupported /
// scan_loop_intervals) are shared with translate.rs -- they are gate
// definitions, not lowerings, and the two lanes must agree on them.
use super::translate::{uses_actual_args, uses_arguments, uses_env_ops, uses_new_target};

/// Which half of the emitter is running. The same `emit_op` body serves
/// both, so the abstract transfer function and the lowering can never drift
/// apart -- the maintainability property the whole design rests on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum EmitMode {
    /// Lower to IR. **Consult-only**: the prediction is closed, so `theta`
    /// is a pure lookup and no path here may move a fact. This is the only
    /// mode that appends values.
    Code,
    /// The prediction pass (`predict.rs`): compute the per-program-point
    /// fact context. The IR primitives append nothing; the transfer runs
    /// unchanged. It runs to a fixpoint before `Code` ever starts.
    ContextOnly,
}

/// The splice set, decided once and then frozen. A spliced callee body owns
/// a range of synthetic pc space, and the prediction is keyed by pc -- so if
/// a later walk renumbered the segments, every prediction past the first
/// splice would silently describe a different program point. Freezing after
/// the first walk makes pc space a round-stable function of the program
/// rather than of the walk that happened to run first, which is what the
/// prediction being pc-keyed requires. Later walks may only look segments
/// up; a site that finds none lowers generically.
struct Splices {
    segs: Vec<SegDecision>,
    by_call_pc: HashMap<(Pc, ScriptId), usize>,
    alloc: u32,
    sites: u32,
    cost: usize,
    gname_call_bids: HashMap<Site, u32>,
    gname_method_pcs: HashSet<Site>,
    gname_scanned: HashSet<ScriptId>,
}

/// One decided splice, free of borrows so it can outlive the walk that
/// decided it. Everything else on `InlineSeg` is a pure function of the
/// callee script and is recomputed on adoption.
struct SegDecision {
    base: u32,
    end: u32,
    sid: ScriptId,
    call_pc: Pc,
    ret_pc: Pc,
    caller_depth: u32,
    frame_base: u32,
    parent: Option<usize>,
    caller_operand_base: u32,
    is_construct: bool,
    argc: u16,
}

impl<'a> Bbv<'a> {
    /// Hand the decided splice set to the next walk, and freeze it.
    fn take_splices(&mut self) -> Splices {
        Splices {
            segs: self
                .segs
                .iter()
                .map(|g| SegDecision {
                    base: g.base,
                    end: g.end,
                    sid: g.sid,
                    call_pc: g.call_pc,
                    ret_pc: g.ret_pc,
                    caller_depth: g.caller_depth,
                    frame_base: g.frame_base,
                    parent: g.parent,
                    caller_operand_base: g.caller_operand_base,
                    is_construct: g.is_construct,
                    argc: g.argc,
                })
                .collect(),
            by_call_pc: std::mem::take(&mut self.seg_by_call_pc),
            alloc: self.seg_alloc,
            sites: self.inline_sites,
            cost: self.spliced_cost,
            gname_call_bids: std::mem::take(&mut self.gname_call_bids),
            gname_method_pcs: std::mem::take(&mut self.gname_method_pcs),
            gname_scanned: std::mem::take(&mut self.gname_bids_scanned),
        }
    }

    /// Adopt a decided splice set. The segments' loop intervals are
    /// re-appended in segment order, which is the order the first walk
    /// created them in, so a loop's index -- and therefore every interned
    /// token class -- names the same loop in every walk.
    fn adopt_splices(&mut self, s: Splices) {
        let source: &'a Source = self.source;
        let mut live_cache = std::mem::take(&mut self.live_cache);
        let names = &self.atoms.names;
        let syn_gnames = self.ctx.syn_gnames;
        self.segs = s
            .segs
            .iter()
            .map(|g| {
                let SourceObject::Script(script) = source.object(SourceObjectId::new(g.sid.get()))
                else {
                    unreachable!("a spliced segment names a script");
                };
                let bid_of = |idx: u32| -> Option<u32> {
                    let gc = *script.gcthings.get(usize::try_from(idx).ok()?)?;
                    let SourceObject::String(st) = source.object(gc) else {
                        return None;
                    };
                    syn_gnames.get(&names.lookup(st)?).copied()
                };
                for (h, e) in super::translate::scan_loop_intervals(script) {
                    self.loop_intervals.push((g.base + h, g.base + e));
                }
                let apply_fwd_pcs = super::translate::compute_apply_fwd_pcs(
                    script,
                    &self.ctx.facts.apply_sites,
                    g.sid.get(),
                )
                .unwrap_or_default();
                let nformals = if apply_fwd_pcs.is_empty() {
                    script.nargs
                } else {
                    script.nargs.max(g.argc)
                };
                InlineSeg {
                    base: g.base,
                    end: g.end,
                    sid: g.sid,
                    script,
                    call_pc: g.call_pc,
                    ret_pc: g.ret_pc,
                    caller_depth: g.caller_depth,
                    frame_base: g.frame_base,
                    parent: g.parent,
                    caller_operand_base: g.caller_operand_base,
                    hot: hot_locals(script),
                    is_construct: g.is_construct,
                    argc: g.argc,
                    nformals,
                    apply_fwd_pcs,
                    this_alias_locals: compute_this_alias_locals(script),
                    live: live::ScriptLive::shared(&mut live_cache, g.sid, script, &bid_of),
                }
            })
            .collect();
        self.live_cache = live_cache;
        self.seg_by_call_pc = s.by_call_pc;
        self.seg_alloc = s.alloc;
        self.inline_sites = s.sites;
        self.spliced_cost = s.cost;
        self.gname_call_bids = s.gname_call_bids;
        self.gname_method_pcs = s.gname_method_pcs;
        self.gname_bids_scanned = s.gname_scanned;
        self.splices_frozen = true;
    }

    /// The unified-pc-space CFG. Only meaningful once the splice set is
    /// frozen -- before that a segment the next walk creates would extend
    /// the pc space this graph does not cover -- so it is built on demand
    /// and every caller is in the `Code` pass or later.
    fn cfg(&self) -> &cfg::Cfg {
        debug_assert!(
            self.splices_frozen || self.segs.is_empty(),
            "the CFG covers a frozen pc space"
        );
        self.cfg
            .get_or_init(|| cfg::Cfg::build(self.root_script, &self.segs))
    }
}

// --- the driver ----------------------------------------------------------

/// Translate one script through the BBV driver. Mirrors the contract of
/// `translate::translate_script_with_gnames` (same `Outcome`). Scripts the
/// driver does not cover skip to the interpreter (always sound).
pub fn translate_script(
    ctx: &TranslateCtx,
    m: &mut Module,
    atoms: &mut AtomTable,
    source_id: ScriptId,
    script: &Script,
    is_global: bool,
) -> Result<Outcome, String> {
    if ctx.opts.diagnostics.disasm_for(source_id.get()) {
        crate::diag_line!("=== disasm #{source_id} ===");
        script
            .parser()
            .visit(crate::disasm::Disassembler::default());
    }
    if script.bytecode.len() > MAX_TRANSLATE_BYTECODE {
        return Ok(Outcome::Skipped(format!(
            "script too large ({} bytecode bytes)",
            script.bytecode.len()
        )));
    }
    // Generator scope gate: the arguments object and the actuals region are
    // not part of the saved generator state, so a generator that reads
    // either cannot be resumed from the saved frame. Such scripts stay
    // interpreted; everything else about the resumable state machine is
    // lowered (generator.rs).
    if script.is_generator_or_async
        && (uses_arguments(script) || script.has_mapped_args || uses_actual_args(script))
    {
        return Ok(Outcome::Skipped(
            "bbv: generator using arguments".to_string(),
        ));
    }
    if uses_env_ops(script) {
        if let Some(reason) = super::translate::env_unsupported(ctx.source, script) {
            return Ok(Outcome::Skipped(reason));
        }
    }
    // Reducibility by construction (DESIGN.md section 4.9) rests on every
    // cycle having its entry re-labeled at a loop header, and the header set
    // comes from the `LoopHead` markers. A back edge to an unmarked target
    // gets no loop interval, so no token, so no re-labeling -- and the cycle
    // can pick up a second entry. SpiderMonkey marks every loop header, so
    // this only fires on hand-written bytecode, but it is the precondition
    // the discipline needs and it is cheaper to state than to detect after
    // emission.
    if let Some(&(from, to)) = super::translate::unmarked_back_edges(script).first() {
        return Ok(Outcome::Skipped(format!(
            "back edge {from} -> {to} with no LoopHead at the target"
        )));
    }
    // BBV bodies carry the widened (err, eff) ABI; the funcref table gets
    // a per-script `night_abi_sig` adapter (translate_all), so only
    // patched direct calls ever see the second result.
    let sig = ctx.helpers.night_abi_sig2;
    // Overflow ladder: full refined -> fanout-off refined (only when the
    // overflowing pass had a meaningful share of fanout-attributable
    // versions, so a near-cap script keeps as much refinement as fits) ->
    // GEN-only.
    let mut skip_fanout_rung = false;
    // A generator body starts at the bottom rung and stays there: a version's
    // identity names a location inside the body, and a suspend leaves the
    // body entirely, so a resume has no arriving version to name. On the GEN
    // rung there is one version per pc, which a resume can name by pc alone
    // (generator.rs).
    let rungs: &[(bool, bool)] = if script.is_generator_or_async {
        &[(true, true)]
    } else {
        &[(false, false), (true, false), (true, true)]
    };
    'ladder: for &(fanout_off, gen_only) in rungs {
        if fanout_off && !gen_only && skip_fanout_rung {
            continue;
        }
        let started = std::time::Instant::now();
        let mut closure_tries = 0;
        // Predict, then emit once against the prediction (`predict.rs`).
        // Emitting first and regenerating cannot do this job: the moment a
        // back edge weakens a program point's prediction, the preheader's
        // already-emitted edge targets the wrong repr, and repairing it is
        // not a retarget -- the transition may need conversion code that
        // edge never had, which cascades to its predecessors. That cascade
        // IS a fixpoint, paid in re-emission.
        let mut vers = VerTable::default();
        let mut tok_classes: HashMap<Vec<(u32, u64)>, u32> = HashMap::default();
        let mut rounds = 0;
        let mut prov_rounds = 0;
        let mut stripping = false;
        let mut splices: Option<Splices> = None;
        let (mut t, outcome) = 'closure: loop {
            match predict::run(
                m,
                sig,
                ctx,
                &mut *atoms,
                source_id,
                script,
                predict::Rung {
                    is_global,
                    gen_only,
                    fanout_off,
                },
                &mut predict::State {
                    vers: &mut vers,
                    tok_classes: &mut tok_classes,
                    splices: &mut splices,
                    stripping: &mut stripping,
                    rounds: &mut rounds,
                    prov_rounds: &mut prov_rounds,
                },
            ) {
                Ok(()) => {}
                Err(reason) => return Ok(Outcome::Skipped(reason)),
            }
            let mut t = Bbv::new(
                FunctionBody::new(m, sig),
                ctx,
                &mut *atoms,
                source_id,
                script,
            );
            t.is_global = is_global;
            t.bigint_free = ctx.bigint_free;
            t.gen_only = gen_only;
            t.fanout_off = fanout_off;
            t.stripping = stripping;
            t.vers = vers;
            t.tok_classes = tok_classes;
            if let Some(sp) = splices.take() {
                t.adopt_splices(sp);
            }
            if ctx.opts.diagnostics.viz {
                crate::diag_line!("night: viz begin sid#{source_id}");
            }
            let outcome = t.emit();
            // The closure check, a net rather than a mechanism: the strip
            // path closes on its own (see the fixpoint loop above), so this
            // is expected never to fire. It stays because it turns any future
            // divergence between the two modes into a slow compile instead of
            // a miscompile -- `Code` emitting against a ctx an arrival does
            // not imply would convert the edge to a repr the value has not
            // been proven to have.
            if t.map_changed && !gen_only {
                if closure_tries >= CLOSURE_MAX_TRIES {
                    // Out of retries with the map still moving. The body in
                    // hand may convert an edge to an unproven repr, so it
                    // must not be emitted. Descend the overflow ladder
                    // instead; its bottom rung is GEN-only, where every
                    // version is facts-empty and the check does not apply, so
                    // this terminates.
                    if ctx.opts.diagnostics.bbv {
                        crate::diag_line!(
                            "night: bbv script#{source_id} closure exhausted, descending"
                        );
                    }
                    continue 'ladder;
                }
                closure_tries += 1;
                vers = std::mem::take(&mut t.vers);
                tok_classes = std::mem::take(&mut t.tok_classes);
                splices = Some(t.take_splices());
                if closure_tries == CLOSURE_MAX_TRIES {
                    crate::diag_line!(
                        "night: bbv WARNING script#{source_id} STRIPPED by closure retry {closure_tries} ({} versions)",
                        vers.len()
                    );
                    vers.strip_all();
                    stripping = true;
                }
                if ctx.opts.diagnostics.bbv {
                    crate::diag_line!("night: bbv script#{source_id} reclosure {closure_tries}");
                }
                continue 'closure;
            }
            break 'closure (t, outcome);
        };
        match outcome {
            Ok(()) => {
                // Clean-ret revocation (non-threaded bodies only; threaded
                // ones account per-lineage in the accumulator): some version
                // emitted after a clean return recorded a user-heap write
                // (spliced store arms, leaf writers the bytecode scan never
                // sees) -- every provisional clean flag constant becomes the
                // body's classified word: any non-this write revokes to
                // FLAGS_ALL, own-this writes alone to MUT_THIS.
                let revoke_word = t.untracked_flags
                    | if t.wrote_other {
                        FLAGS_ALL
                    } else if t.wrote_this {
                        FLAG_MUT_THIS
                    } else {
                        0
                    };
                if revoke_word != 0 && !t.clean_ret_flag_patches.is_empty() {
                    if ctx.opts.diagnostics.bbv {
                        crate::diag_line!(
                            "night: bbv script#{source_id} clean-ret REVOKED to {revoke_word} ({} returns)",
                            t.clean_ret_flag_patches.len()
                        );
                    }
                    for &v in &t.clean_ret_flag_patches {
                        if let ValueDef::Operator(Operator::I32Const { value }, _, _) =
                            &mut t.body.values[v]
                        {
                            *value = revoke_word;
                        }
                    }
                }
                if ctx.opts.diagnostics.bbv {
                    let nparams: usize = t.body.blocks.values().map(|b| b.params.len()).sum();
                    crate::diag_line!(
                        "night: bbv script#{source_id} shape blocks {} params {} values {} segs {} cost {} rung {}",
                        t.body.blocks.len(),
                        nparams,
                        t.body.values.len(),
                        t.segs.len(),
                        t.spliced_cost,
                        if gen_only { "gen" } else if fanout_off { "fanout-off" } else { "full" },
                    );
                    // The on-ramp only ever fires at a pc that is a loop
                    // header here, and a header it does not know about is
                    // silent -- so print the set it does know.
                    for &(h, e) in &t.loop_intervals {
                        crate::diag_line!("night: bbv script#{source_id} loop {h}..{e}");
                    }
                    // The synthetic-pc decoder ring: kind-34 / DIRTYTRACE
                    // ids beyond bclen name spliced code; this maps them.
                    for (i, s) in t.segs.iter().enumerate() {
                        crate::diag_line!(
                            "night: bbv script#{source_id} seg {i} base {} end {} callee sid#{} call_pc {} construct {}",
                            s.base, s.end, s.sid, s.call_pc, u8::from(s.is_construct),
                        );
                    }
                }
                if ctx.opts.diagnostics.redundant {
                    t.dump_redundant();
                }
                if ctx.opts.diagnostics.cfg {
                    let iv = std::mem::take(&mut t.loop_intervals);
                    t.cfg().dump(source_id, &iv);
                    t.loop_intervals = iv;
                }
                if ctx.opts.diagnostics.peel {
                    t.dump_peel(source_id);
                }
                // Instrument values are excluded: the ladder must land on
                // the same rung a production build's would, or the census
                // changes the version shape of the thing it measures.
                let decision_len = t.body.values.len() - t.instrument_values;
                if decision_len > MAX_BODY_VALUES {
                    if !gen_only {
                        // Version growth overran the cap on a very large
                        // script: descend the ladder -- the generic lane fits
                        // where the refined one does not.
                        if !fanout_off {
                            // Versions attributable to the fanout dimensions:
                            // carried caller facts or tokened segment copies
                            // (baseline segments were token-free and shared).
                            let root_len = u32::try_from(script.bytecode.len()).unwrap();
                            let fanout_versions = t
                                .blocks
                                .keys()
                                .filter(|&&key| {
                                    let c = t.vers.ctx(key);
                                    !c.caller_locals.is_empty()
                                        || !c.caller_args.is_empty()
                                        || (t.vers.ver(key).pc >= Pc::new(root_len)
                                            && !c.tokens.is_empty())
                                })
                                .count();
                            // Take the middle rung only when the fanout
                            // dimensions plausibly tipped a near-cap script:
                            // some fanout share and a marginal overflow. A
                            // huge overflow is baseline-shaped, so the middle
                            // pass would just burn another failed emission.
                            skip_fanout_rung =
                                fanout_versions == 0 || decision_len > MAX_BODY_VALUES * 3 / 2;
                            if ctx.opts.diagnostics.bbv {
                                crate::diag_line!(
                                    "night: bbv script#{source_id} RETRY versions {} fanout-versions {} values {} next {}",
                                    t.blocks.len(),
                                    fanout_versions,
                                    t.body.values.len(),
                                    if skip_fanout_rung { "gen-only" } else { "fanout-off" }
                                );
                            }
                        }
                        continue;
                    }
                    return Ok(Outcome::Skipped(format!(
                        "body too large ({} SSA values)",
                        t.body.values.len()
                    )));
                }
                // Reducibility is a property of the token discipline
                // (DESIGN.md section 4.9), not a hope: `out_tokens_for`
                // drops a loop's own token at its header pc, so every edge
                // into a cycle lands on the header. `assert_reducible`
                // re-derives it from the emitted CFG, and a violation is a
                // compiler bug -- the body is refused rather than shipped,
                // because LICM's natural-loop math and waffle's stackify
                // both assume what it proves. GEN-only bodies skip both the
                // check and LICM: one version per pc is trivially
                // reducible, and there is nothing left to hoist.
                if !gen_only {
                    let cfg = match assert_reducible(&t.body) {
                        Ok(cfg) => cfg,
                        Err((from, to)) => {
                            let describe = |b: Block| {
                                t.blocks
                                    .iter()
                                    .find(|&(_, &blk)| blk == b)
                                    .map(|(&key, _)| {
                                        let v = t.vers.ver(key);
                                        let toks = &t.vers.ctx(key).tokens;
                                        format!(
                                            "pc{} class{} {:?} toks{toks:x?}",
                                            v.pc, v.class, v.track
                                        )
                                    })
                                    .unwrap_or_else(|| "non-version block".to_string())
                            };
                            return Ok(Outcome::Skipped(format!(
                                "irreducible version graph: {from} ({}) -> {to} ({})",
                                describe(from),
                                describe(to)
                            )));
                        }
                    };
                    // Effect-cleared LICM on the emitted IR. retval_out
                    // counts as frame traffic: it is the caller's out-slot
                    // pointer (a fixed frame address), so return-value
                    // stores never poison a loop summary.
                    let frame_roots = [t.vp, t.sp, t.retval_out];
                    let hoisted = licm(
                        &mut t.body,
                        &cfg,
                        &t.effects,
                        &frame_roots,
                        t.root_source_id.get(),
                        &t.load_pcs,
                    );
                    if ctx.opts.diagnostics.bbv && hoisted > 0 {
                        crate::diag_line!("night: bbv script#{source_id} licm hoisted {hoisted}");
                    }
                }
                if ctx.opts.instrument.blocks {
                    t.flush_block_census();
                }
                // Instruments: per-pc version counts + per-script
                // translation time under the bbv dump.
                if ctx.opts.diagnostics.bbv {
                    let mut per_pc: HashMap<Pc, u32> = HashMap::default();
                    for key in t.blocks.keys() {
                        *per_pc
                            .entry(Pc::new(t.vers.ver(*key).pc.get()))
                            .or_insert(0) += 1;
                    }
                    let max_at_pc = per_pc.values().copied().max().unwrap_or(0);
                    let mut by_track = [0u32; 3];
                    for key in t.blocks.keys() {
                        by_track[t.vers.ver(*key).track as usize] += 1;
                    }
                    let hdr_tracks = {
                        let mut h = [0u32; 3];
                        for key in t.blocks.keys() {
                            let v = t.vers.ver(*key);
                            if t.loop_intervals.iter().any(|&(lh, _)| lh == v.pc.get()) {
                                h[v.track as usize] += 1;
                            }
                        }
                        h
                    };
                    crate::diag_line!(
                        "night: bbv script#{source_id} tracks opt {} side {} dirty {} hdrs opt {} side {} dirty {}",
                        by_track[0], by_track[1], by_track[2],
                        hdr_tracks[0], hdr_tracks[1], hdr_tracks[2],
                    );
                    crate::diag_line!(
                        "night: bbv script#{source_id} versions {} pcs {} max-per-pc {} idents {} gen-only {} fanout-off {} {}us",
                        t.blocks.len(),
                        per_pc.len(),
                        max_at_pc,
                        t.vers.len(),
                        u8::from(gen_only),
                        u8::from(fanout_off),
                        started.elapsed().as_micros()
                    );
                }
                if ctx.opts.diagnostics.viz {
                    let name = viz_script_name(ctx.source, source_id.get());
                    crate::diag_line!(
                        "night: viz script sid#{source_id} name {} nargs {} nlocals {} bclen {} global {}",
                        name.as_deref().unwrap_or("-"),
                        script.nargs,
                        max_locals(script),
                        script.bytecode.len(),
                        u8::from(is_global),
                    );
                    for &(h, e) in &t.loop_intervals {
                        crate::diag_line!("night: viz loop sid#{source_id} interval {h} {e}");
                    }
                    if let Some(tl) = ctx.this_layouts_in.get(&source_id) {
                        crate::diag_line!(
                            "night: viz site sid#{source_id} pc 0 kind this pred {}",
                            viz_cls_range(tl.layout_id, tl.hi_layout_id)
                        );
                    }
                    let name_tbl = &t.atoms.names;
                    let gname_name = |pcu: Pc| -> Option<NameId> {
                        let b = script
                            .bytecode
                            .get(pcu.get() as usize + 1..pcu.get() as usize + 5)?;
                        let idx = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
                        let id = *script.gcthings.get(idx as usize)?;
                        if id.is_other() {
                            return None;
                        }
                        match ctx.source.object(id) {
                            SourceObject::String(st) => name_tbl.lookup(st.chars()),
                            _ => None,
                        }
                    };
                    let total = script.bytecode.len();
                    let mut p = script.parser();
                    let mut first_ops: Vec<(JSOp, String)> = Vec::new();
                    loop {
                        let pc = total - p.remaining();
                        let Some(op) = p.next_op() else { break };
                        if p.advance(usize::try_from(op.len()).unwrap() - 1).is_none() {
                            break;
                        }
                        let pcu = u32::try_from(pc).unwrap();
                        let args = viz_op_args(ctx.source, script, Pc::new(pcu), op);
                        crate::diag_line!(
                            "night: viz op sid#{source_id} pc {pc} op {op:?} args [{args}]"
                        );
                        if first_ops.len() < 2 {
                            first_ops.push((op, args));
                        }
                        let key = Site::new(source_id, Pc::new(pcu));
                        if let Some(ps) = ctx.prop_sites_in.get(&key) {
                            let pred = format!(
                                "{} slot {} mask {}",
                                viz_cls_range(ps.layout_id, ps.hi_layout_id),
                                ps.slot,
                                viz_claim_str(ps.claim)
                            );
                            crate::diag_line!(
                                "night: viz site sid#{source_id} pc {pc} kind prop pred {pred}"
                            );
                        }
                        let mut eparts: Vec<String> = Vec::new();
                        if let Some(&m) = ctx.likely_elems.get(&key) {
                            eparts.push(format!("claim {}", viz_claim_str(m)));
                        }
                        if let Some(&k) = ctx.facts.ta_elem_sites.get(&key) {
                            eparts.push(format!("ta={}", k.code()));
                        }
                        if ctx.facts.elem_poly_sites.contains(&key) {
                            eparts.push("poly".to_string());
                        }
                        if !eparts.is_empty() {
                            crate::diag_line!(
                                "night: viz site sid#{source_id} pc {pc} kind val pred {}",
                                eparts.join(" ")
                            );
                        }
                        let t = ctx.facts.scripted_targets(key);
                        if !t.is_empty() {
                            let ts: Vec<String> = t.iter().map(|x| x.to_string()).collect();
                            crate::diag_line!(
                                "night: viz site sid#{source_id} pc {pc} kind call pred targets {}",
                                ts.join(",")
                            );
                        }
                        if matches!(
                            op,
                            JSOp::GetGName
                                | JSOp::SetGName
                                | JSOp::StrictSetGName
                                | JSOp::BindUnqualifiedGName
                        ) {
                            if let Some(n) = gname_name(Pc::new(pcu)) {
                                if let Some(&FusedGname { boxed: bits, .. }) =
                                    ctx.fused_gnames.get(&n)
                                {
                                    crate::diag_line!(
                                        "night: viz site sid#{source_id} pc {pc} kind gname pred fused-lit 0x{bits:x}"
                                    );
                                } else if let Some(&bid) = ctx.syn_gnames.get(&n) {
                                    crate::diag_line!(
                                        "night: viz site sid#{source_id} pc {pc} kind gname pred slot-bid {bid}"
                                    );
                                }
                            }
                        }
                    }
                    // The bytecode's .this binding: `FunctionThis; SetLocal N`
                    // prologue, so `this.x` reads are GetLocal N; GetProp x.
                    if let [(JSOp::FunctionThis, _), (JSOp::SetLocal, l)] = &first_ops[..] {
                        crate::diag_line!("night: viz thislocal sid#{source_id} loc {l}");
                    }
                }
                return Ok(Outcome::Compiled {
                    sig,
                    body: t.body,
                    likely_patches: t.likely_patches,
                    fuse_call_patches: t.fuse_call_patches,
                    call_cell_patches: t.call_cell_patches,
                    alloc_cell_patches: t.alloc_cell_patches,
                    iof_cell_patches: t.iof_cell_patches,
                    construct_cell_patches: t.construct_cell_patches,
                    strlit_patches: t.strlit_patches,
                    intrinsic_cell_patches: t.intrinsic_cell_patches,
                    prop_ic_patches: t.prop_ic_patches,
                    body_off_patches: t.body_off_patches,
                    ctor_nslots_patches: t.ctor_nslots_patches,
                });
            }
            Err(reason) => return Ok(Outcome::Skipped(reason)),
        }
    }
    unreachable!("gen-only retry always returns")
}

/// Whether an operand's type already implies a likely arg claim (then no
/// guard: the def keeps its -- equal or tighter -- type). An unboxed
/// carrier repr is itself proof (refine_by_repr's rule).
fn arg_claim_implied(o: &Operand, claim: Claim) -> bool {
    if !matches!(o.repr, Repr::Boxed) {
        return true;
    }
    let ty = &o.ty;
    if claim.is_object() {
        return is_object_only(ty);
    }
    !ty.prims.is_empty() && !ty.outside && ty.prims.subset_of(claim.prims())
}

/// `ToInt32(f)`: truncate toward zero mod 2^32. Callers gate on |f| < 2^63
/// so the saturating trunc is exact.
impl<'a> Bbv<'a> {
    fn to_int32_from_f64(&mut self, f: Value) -> Value {
        let i64v = self.unop(Operator::I64TruncSatF64S, f, Type::I64);
        self.unop(Operator::I32WrapI64, i64v, Type::I32)
    }
}

/// Chain a builtin fast arm before the helper tail: the arm's miss edge
/// targets `helper_blk`, which becomes the new `cur` for the next arm.
impl<'a> Bbv<'a> {
    fn builtin_arm(&mut self, body: impl FnOnce(&mut Self, Block)) {
        let helper_blk = self.body.add_block();
        body(self, helper_blk);
        self.cur = helper_blk;
    }
}

/// One completion-unwind action found by the try-note walk.
enum UnwindClose {
    ForIn(u32),
    Destructuring(u32),
}

// --- effect kinds (kind-granular; see DESIGN.md section 4.11) ------------

// What a tagged heap access touches: `HeapKind`, defined in effects.rs
// beside the EffectClass and leaf-write tables. The conflict relation is
// kind-equality plus Unknown-conflicts-with-everything; Frame traffic is
// classified by address rooting (vp/sp/retval_out) at LICM time and never
// conflicts with heap kinds.

/// The emitter state a leaving diamond arm borrows and restores (see
/// `arm_state`): everything an arm may mutate that its siblings must not
/// see -- the operand stack, the track, the flags accumulator, the tracked
/// frame facts and the SSA carriers. Bundled so that no arm site can save
/// half of it; `side_arm` adds the one field an arm site keeps for itself,
/// the emission block.
#[derive(Clone)]
struct ArmState {
    stack: Vec<Operand>,
    track: Track,
    post_call: bool,
    cur_flags: FlagsAcc,
    locals_ctx: Vec<SlotCtx>,
    args_ctx: Vec<SlotCtx>,
    caller_locals_ctx: Vec<SlotCtx>,
    caller_args_ctx: Vec<SlotCtx>,
    /// The frames above `caller_*`, innermost first (see `Ctx::outer`).
    outer_ctx: Vec<CallerFrame>,
    gcells_ctx: Vec<(u32, SlotCtx)>,
    locals_ssa: Vec<Option<(Value, Repr)>>,
    args_ssa: Vec<Option<(Value, Repr)>>,
    outer_ssa: Vec<Option<(Value, Repr)>>,
    frame_stale: HashSet<u32>,
}

/// The array-population fold a typed element load may apply: fusing the
/// receiver's stamp-word test into the load's own int32-tag test buys the
/// site's proven element range for free, so the pushed operand carries an
/// interval and downstream arithmetic elides its overflow ladders.
#[derive(Clone, Copy)]
struct ArrFold {
    /// The receiver, already proven to be an object by the arms above.
    recv_ptr: Value,
    /// The exact class word the receiver must carry: the population's stamp
    /// key with the validity bits the claim is consumed behind.
    want_word: u32,
    /// The element range the population claims.
    range: ValueRange,
}

/// A depth-1 inline segment: the callee's bytecode mapped into the
/// synthetic pc space above the root script, so a splice is a pc-space
/// region rather than a recursive descent. The child frame lives at the call
/// site's operand spill offsets (the contiguous-frame ABI trick):
/// [0]=callee, [8]=this, [16+]=args, then locals/rval, exactly the layout
/// the popped call operands spill into when argc == nargs.
struct InlineSeg<'a> {
    /// The segment's half-open extent [base, end) in the synthetic pc space.
    base: u32,
    end: u32,
    /// The callee this segment holds.
    sid: ScriptId,
    script: &'a Script,
    /// Call-site pc in the caller's pc space (root or a parent segment;
    /// segment pcs count as inside every loop containing the transitively
    /// resolved root site, which is what keeps loop tokens continuous
    /// across a splice).
    call_pc: Pc,
    /// Caller-space continuation pc (the op after the call).
    ret_pc: Pc,
    /// Caller operand depth below the callee slot (reloaded at return).
    caller_depth: u32,
    /// Child frame byte offset from vp.
    frame_base: u32,
    /// Nested splices: the parent segment (None = root caller) and the
    /// caller frame's operand-region base (the return path reloads the
    /// caller operands and restores the caller frame view from these).
    parent: Option<usize>,
    caller_operand_base: u32,
    /// Locals-into-SSA candidate set for this frame (`hot_locals`).
    hot: Vec<u32>,
    /// Ctor-body splice: segment returns stamp the ctor-exit
    /// class word and substitute `is_object(ret) ? ret : this`.
    is_construct: bool,
    /// The site's actual count (static: the splice's operands).
    argc: u16,
    /// Formal slots the child frame keeps below its locals: `nargs`, or
    /// `max(nargs, argc)` for an apply-forward wrapper, whose surplus
    /// actuals are the forward's payload and must survive the locals
    /// init (the root frame keeps them the same way, via the vp rebase).
    nformals: u16,
    /// The callee's apply-forward pcs (local pc space), non-empty iff the
    /// callee is an apply-forward wrapper (`compute_apply_fwd_pcs`).
    apply_fwd_pcs: HashSet<Pc>,
    /// The segment's `this`-alias locals (`compute_this_alias_locals`),
    /// precomputed: store classification asks per store, and the scan walks
    /// the whole callee bytecode.
    this_alias_locals: HashSet<u32>,
    /// Per-pc liveness of the callee's frame slots (`live::ScriptLive`).
    live: std::rc::Rc<live::ScriptLive>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Eff {
    /// A tagged load whose result may be GC-relocatable state: a heap
    /// pointer (Shape*, elements/slots/TA-data base, table entries) or a
    /// boxed JS::Value. The conservative default for every tagged load.
    Read(HeapKind),
    /// A tagged load whose result is GC-immune bits: lengths, flags,
    /// class/fuse words, slot-offset bounds, chars, TA element data.
    /// Only the emitter knows -- an i32-by-type proxy counts base pointers
    /// and Shape* words as primitive and is wrong. A GC cannot change these
    /// values, so they may cross gc points in plain SSA once hoisted.
    ReadBits(HeapKind),
    Write(HeapKind),
    /// A call that provably reads engine state only.
    CallPure,
    /// A call that writes engine state but runs no user code and no GC.
    /// Carries the callee's write summary as a `HeapKind::bit` mask
    /// (effects.rs helper_leaf_writes), folded into the loop summary by
    /// LICM.
    CallLeaf(u16),
    /// May GC or run user code: kills all hoisting in the loop (a moving
    /// GC relocates objects; user code mutates anything).
    CallGc,
    /// A quiet alloc (helper_quiet_alloc): may GC but runs no user code
    /// and writes no pre-existing user-visible heap. For LICM it
    /// contributes only the allocator's own state (AllocCursor/Fresh) to
    /// the loop write summary; hoisted GC-immune bits stay valid across
    /// it, while pointer-valued hoists still may not cross.
    CallGcQuiet,
}

struct Bbv<'a> {
    body: FunctionBody,
    mem: Memory,
    helpers: Helpers,
    /// Set when an operand stack outgrew the u16 a version identity names;
    /// the workqueue drain then refuses the script.
    depth_overflow: bool,
    /// The effect table, hashed once per compile (effects.rs).
    helper_meta: HashMap<Func, HelperMeta>,
    opts: &'a Options,
    source: &'a Source,
    atoms: &'a mut AtomTable,
    /// The script being compiled -- the root script, even inside a spliced
    /// segment (`enter_frame_view` swaps it to the segment's callee).
    source_id: ScriptId,
    script: &'a Script,
    is_global: bool,
    /// Every analysis table this body may read, borrowed once (the
    /// individual tables are documented on `TranslateCtx`). All of it is
    /// arm-order and speculation-policy evidence, never proof -- the emitted
    /// guards are the proof.
    ctx: &'a TranslateCtx<'a>,
    /// Scratch: the array fold `push_load_typed` should apply, if any.
    arr_fold: Option<ArrFold>,
    /// Scratch: the viz-local pc of the op being lowered, so a side arm
    /// records its continuation against the same key the lowering uses.
    viz_lpc: Pc,
    /// Ctor full-layout slot counts for construct-`this` alloc sizing
    /// (see translate.rs `construct_nslots`).
    /// Root-space pcs of proven `T.apply(this, arguments)`
    /// forwards. Non-empty means this script's `arguments` object is
    /// unobservable and is never built (see translate.rs
    /// `compute_apply_fwd_pcs`).
    apply_fwd_pcs: HashSet<Pc>,
    /// Call sites (root and spliced) whose callee is `Global.method` (see
    /// `compute_gname_call_bids`).
    gname_method_pcs: HashSet<Site>,
    /// One-entry memo behind `likely_mono`.
    mono_memo: std::cell::Cell<Option<(Site, Option<ScriptId>)>>,
    /// Which half of the emitter is running; see `EmitMode`.
    mode: EmitMode,
    /// The fixpoint overran `CTXONLY_MAX_ROUNDS` and every ctx has been
    /// widened to its all-TOP form, so a version minted from here on must be
    /// widened too. That is what makes the strip path close: with every ctx
    /// stripped, a version's ctx is a function of its own identity (a
    /// stripped ctx is just its tokens and track, both of which the identity
    /// already fixes), so no arrival can move one and the next round walks
    /// exactly the same versions. Widening a subset would not close --
    /// stripping changes which arms the walk takes, and the versions that
    /// change brings in have to be discovered before `Code` runs.
    stripping: bool,
    /// Values the IR primitives would have appended, counted only in
    /// `ContextOnly` (where nothing is appended). Every decision that reads
    /// the size of the body goes through `value_count()` so the two modes
    /// see the same number and take the same control decisions -- without
    /// that, the context map would describe a program we do not emit.
    virtual_values: usize,
    /// Values appended by the census instruments (Code mode only). They are
    /// real emitted code, but they must not count toward `value_count()`:
    /// fuel and overflow decisions have to land exactly where a production
    /// build's would, or the instrument changes the splice/version shape of
    /// the thing it measures -- and ContextOnly (which skips instruments
    /// entirely) would diverge from Code on those decisions, breaking the
    /// lockstep invariant above.
    instrument_values: usize,
    /// Arm blocks the current op emitted through the `side_arm` family,
    /// for `--block-census` role attribution.
    /// Locals whose frame slot is behind their SSA value (`write_local`
    /// defers the store of a raw-repr local: the GC does not need it and
    /// no reader sees the frame while the SSA value lives). Flushed at
    /// every edge to a version that does not carry the local, and at every
    /// seam; a version entry marks its carried raw locals stale, since the
    /// frame's freshness is not part of the version identity.
    frame_stale: HashSet<u32>,
    /// The root script's environment-bearing scopes (`env_scopes_of`),
    /// computed on first use by the exception-edge env unwind.
    env_scopes: Option<Vec<u32>>,
    op_arm_blocks: Vec<(Block, blockcen::ArmKind)>,
    /// The lowering form the current op took (`prop_form`) and its store
    /// choke decision, for the `--block-census` entry record.
    op_form: Option<&'static str>,
    op_choke: Option<&'static str>,
    /// `--block-census` records, printed after LICM so the per-block counts
    /// describe the code that ships; keyed by the tick call value.
    blockcen_recs: Vec<blockcen::BlockRec>,
    blockcen_ticks: HashMap<Value, u32>,
    /// Every version entry block (`ensure_version_block`), so a per-op
    /// block set can tell an op's own blocks from the continuations it
    /// minted.
    ver_blocks: HashSet<Block>,
    /// Closure cost this body has absorbed through splices (census only,
    /// reported on the bbv-dump shape line). It is not a budget --
    /// see the deleted cumulative term above for why.
    spliced_cost: usize,
    /// Whole-module BigInt freedom (translate.rs `module_is_bigint_free`):
    /// the module can never manufacture a BigInt, so an arithmetic result
    /// that would otherwise be typed `Int32|Double|BigInt` is just numeric.
    /// That matters far past the one op: `is_numeric` is what lets the next
    /// arithmetic op take the unboxed f64 path instead of the fully generic
    /// tag-guarded ladder, and the BigInt bit alone was disqualifying it.
    bigint_free: bool,
    /// (script sid, frame-local call pc) -> the global binding the callee
    /// was read from (see translate.rs `compute_gname_call_bids`).
    /// Filled for the root script up front and for each callee script when
    /// its first segment is created, so segment-interior sites resolve
    /// through the frame view like every other evidence table.
    gname_call_bids: HashMap<Site, u32>,
    gname_bids_scanned: HashSet<ScriptId>,
    /// Fuse-guarded direct-call arms claimed by this body.
    fuse_call_patches: Vec<FuseCallPatch>,

    // Compiled-body ABI params (copied layout from translate.rs `Translator`).
    cur: Block,
    cx: Value,
    sp: Value,
    /// Variable-region base: `sp`, or `sp + 8*max(argc-nargs, 0)` for a
    /// `uses_arguments` body (actuals stay intact below the variable region).
    vp: Value,
    argc: Value,
    retval_out: Value,
    /// ABI parameter 4 is the body's own `JSScript*`, and nothing binds it:
    /// a raw script pointer held in a wasm local does not survive a
    /// compacting GC, so every use re-derives it from the rooted frame slot
    /// instead (`cur_script_value`). The parameter stays in the signature --
    /// it is shared with the specialized-call `call_indirect` and the
    /// `night_abi_sig` adapter -- and is simply ignored.
    new_target_param: Value,
    needs_new_target: bool,
    new_target_slot_off: u32,

    stack: Vec<Operand>,
    rval_slot_off: u32,
    /// Per-sid memo for `script_names_push` (the dense push arm's gate).
    push_named: HashMap<ScriptId, bool>,
    /// Per-sid memo of eq-compare pcs whose RHS operand is a `String`
    /// literal pushed by the immediately preceding op -- a syntactic fact
    /// that survives version boundaries where the operand's ctx fact is
    /// dropped (the proven-string equality lowering's admission).
    lit_rhs_cmp: HashMap<ScriptId, rustc_hash::FxHashSet<Pc>>,
    /// Per script: the `JumpIfTrue` pcs an `IsNoIter` feeds (`noiter_jump`).
    noiter_jumps: HashMap<ScriptId, rustc_hash::FxHashSet<Pc>>,
    /// Per-sid memo of Add/Sub pcs whose every consumer truncates through
    /// ToInt32/ToUint32 (directly or through further Add/Sub links), so
    /// the site lowers as a wrapping int32 op with no overflow arm (see
    /// `trunc_demanded`).
    trunc_sites: HashMap<ScriptId, rustc_hash::FxHashSet<Pc>>,
    /// `script_names_array` memo (the `new Array()` arm's emission gate).
    array_named: HashMap<ScriptId, bool>,
    /// Memoized `script_ret_clean` scan classes, keyed by sid (callers consult
    /// it for their resolved callees too).
    ret_clean: HashMap<ScriptId, ScanClass>,
    /// Memoized `ctor_returns_this` verdicts: whether a construct's result
    /// is provably the freshly allocated `this`.
    ctor_ret_this: HashMap<ScriptId, bool>,
    /// Root-script locals proven to alias `this` (see
    /// `compute_this_alias_locals`); consulted by store classification,
    /// never inside segments.
    this_alias_locals: HashSet<u32>,
    /// Adapter-offset placeholder consts (see `Outcome::body_off_patches`).
    body_off_patches: Vec<Value>,
    /// Ctor-nslots region base placeholders (see `NSLOTS_REGION_PLACEHOLDER`).
    ctor_nslots_patches: Vec<Value>,
    needs_args_obj: bool,
    args_obj_slot_off: u32,
    local_base: u32,
    nlocals: u32,
    /// Formal slots of the active frame view (`InlineSeg::nformals`; the
    /// root's is its script's `nargs`). Sizes `args_ctx`/`args_ssa`.
    nformals: u16,
    operand_base: u32,
    /// Tagged-load site info for the viz LICM report: value -> the
    /// preformatted "pc .. lpc .. site .. path .." suffix.
    load_pcs: HashMap<Value, String>,
    needs_env: bool,
    env_slot_off: u32,

    error_blk: Option<Block>,
    cur_pc: Pc,
    cur_op: Option<JSOp>,
    /// Keyed by (finally pc, edge tokens): landings are shared only within
    /// a token class (a shared landing across classes would splice loop
    /// lineages -- the irreducibility the tokens exist to prevent).
    finally_landing: HashMap<(u32, Vec<(u32, u64)>), Block>,

    // CFG state: the version table, keyed by structural version identity.
    blocks: HashMap<VerId, Block>,
    block_params: HashMap<VerId, Vec<Value>>,
    workqueue: Vec<VerId>,
    processed: HashSet<VerId>,
    /// Virtual values each identity contributed, so that re-running one in
    /// the prediction pass replaces its contribution instead of adding a
    /// second copy. `value_count()` has to mean the same thing on the
    /// hundredth visit as on the first, or the splice fuel and the overflow
    /// cap would fire on the walk's shape rather than the program's.
    ver_values: HashMap<VerId, usize>,
    /// Interned token vectors (token classes). Persists across
    /// `ContextOnly` rounds: a class id is part of a version identity, so
    /// it has to name the same thing in round N+1 that it named in round N.
    tok_classes: HashMap<Vec<(u32, u64)>, u32>,
    /// The structural version identities and the fixpoint's ctx for each --
    /// The map. Carried in from the `ContextOnly` rounds and read-only by
    /// the time `Code` runs.
    vers: VerTable,
    /// The identity currently being emitted (the self-token a header
    /// version hands to its body edges).
    cur_ver: VerId,
    /// The track the current emission point is on. Seeded per version from
    /// its ctx, stepped down by `side_arm` (structural happy-path
    /// designation) and by every may-GC call, never back up.
    cur_track: Track,
    /// The splice set is decided and may no longer grow: later walks look
    /// segments up, and a site with no segment lowers generically. See
    /// `Splices`.
    splices_frozen: bool,
    /// A version ctx moved this pass: the `ContextOnly` fixpoint is not
    /// closed and needs another round.
    map_changed: bool,
    /// A version ctx's provenance bits moved this pass (see theta): re-arms
    /// fixpoint rounds only under the census instruments.
    prov_changed: bool,
    /// Census split of `map_changed` re-arms this pass: versions whose ctx
    /// went None -> Some (breadth-layer discovery of the version graph) vs
    /// versions whose existing ctx a join descended.
    changed_discover: u32,
    changed_join: u32,
    /// The enclosing-loop tokens of the version currently being emitted.
    cur_tokens: Vec<(u32, u64)>,
    /// GEN-only retry mode (a first refined pass overran MAX_BODY_VALUES):
    /// theta routes every edge to GEN, so every version is facts-empty.
    /// Generator bodies are pinned to it from the start -- see generator.rs
    /// for why a suspend cannot cross a version boundary.
    gen_only: bool,
    /// Whether this body is a generator or async function, i.e. whether it
    /// carries the suspend/resume state machine (generator.rs).
    is_generator: bool,
    /// The resume dispatcher block, when this is a generator body: the
    /// physical entry's resume arm, terminated once the body is emitted.
    gen_dispatch_blk: Option<Block>,
    /// One entry per suspend point: (engine resume index, the version the
    /// resume lands on, the operand depth saved there).
    gen_resume: Vec<(u32, VerId, u32)>,
    /// Fanout-off retry mode (middle rung of the overflow ladder): the four
    /// refinements that multiply version count -- dirty-arm forks, segment
    /// token continuity, caller-fact carrying, typed retvals -- are all
    /// disabled, for near-cap scripts their growth tips over
    /// MAX_BODY_VALUES.
    fanout_off: bool,
    /// The tracked per-local facts of the version being emitted (SetLocal
    /// strong update; seeded from the version's ctx).
    locals_ctx: Vec<SlotCtx>,
    /// The tracked frame-argument facts ([0] = this, [1 + i] = arg i) of
    /// the version being emitted; refined by guard-pass write-back,
    /// strong-updated by SetArg. Empty (untracked) for mapped-args frames.
    args_ctx: Vec<SlotCtx>,
    /// The caller frame facts carried through the current inline
    /// segment (mirrors `Ctx::caller_locals` / `Ctx::caller_args`); set at
    /// segment entry, restored into locals_ctx/args_ctx at the return
    /// edge. Empty outside segments.
    caller_locals_ctx: Vec<SlotCtx>,
    caller_args_ctx: Vec<SlotCtx>,
    /// The frames above `caller_*`, innermost first (see `Ctx::outer`).
    outer_ctx: Vec<CallerFrame>,
    /// The tracked per-binding value facts of the version being emitted
    /// (mirrors `Ctx::gcells`).
    gcells_ctx: Vec<(u32, SlotCtx)>,
    /// Locals-into-SSA carriers for the frame `ssa_seg`: the current SSA
    /// value + repr of each frame local, or None (read the frame slot).
    /// Write-through discipline: SetLocal still stores the boxed value (the
    /// frame stays root-complete; spill_all unchanged), reads and version
    /// edges use the carrier. Seeded per version from the carried block
    /// params; installed by SetLocal and GetLocal's load; killed at every
    /// CallGc unless the repr/fact proves the value GC-immune.
    locals_ssa: Vec<Option<(Value, Repr)>>,
    /// Inside a segment: the parent frame's raw carriers riding through it
    /// (`OUTER_LOCAL` keys), indexed by the parent's local number. Empty at
    /// the root.
    outer_ssa: Vec<Option<(Value, Repr)>>,
    /// At a splice seam only: the popped actuals, indexed by formal, that
    /// the entering edge may hand the callee as raw formal carriers
    /// (`STALE_ARG` keys) instead of a boxed frame store and a `GetArg`
    /// reload. The frame build stored a placeholder for each raw one; the
    /// edge stores the real value where the target does not carry it raw.
    seam_args: Vec<Option<Operand>>,
    /// The frame `locals_ssa` describes (None = root). Edges to a pc in a
    /// different frame never consult carriers (cross-splice edges read the
    /// target frame's slots -- the rooted truth).
    ssa_seg: Option<usize>,
    /// Locals-into-SSA candidate set for the root frame (`hot_locals`).
    hot_root: Vec<u32>,
    /// Per-pc liveness of the root frame's slots, and the per-callee tables
    /// the segments share.
    live_root: std::rc::Rc<live::ScriptLive>,
    live_cache: HashMap<ScriptId, std::rc::Rc<live::ScriptLive>>,
    /// A may-GC call (`Eff::CallGc`) was emitted since the last reset (per
    /// version / per arm scope). Read by `side_arm` to name its
    /// continuation a dirty one; the track is what actually carries the
    /// dirt now, so this is bookkeeping for the seam, not a version key.
    post_call: bool,
    /// Loop extents [header, end): an allowed structural input. Consulted
    /// to pick the in-loop merge-back operator form.
    loop_intervals: Vec<(u32, u32)>,
    /// Per-op-instance value ranges for the redundant-work census
    /// (`redundant.rs`), recorded only when `--dump-redundant` is on:
    /// `add_value` appends, so an op's lowering owns a contiguous range and
    /// the census can attribute a finding to the op that emitted it without
    /// a per-value side table.
    red_ranges: Vec<(Pc, Pc, JSOp, Track, u32, u32, u32)>,
    /// The CFG, dominator tree and loop nest over the unified pc space
    /// (`cfg.rs`). Built on first use rather than per walk: it is a pure
    /// function of the root script and the FROZEN segment table, so it is
    /// meaningless before walk 1 has decided the splices and constant
    /// afterwards.
    cfg: std::cell::OnceCell<cfg::Cfg>,

    stack_limit_ssa: Option<Value>,
    dda_fuse_word_addr_ssa: Option<Value>,

    alloc_cell_patches: Vec<(Value, u32)>,
    iof_cell_patches: Vec<(Value, u32)>,
    strlit_patches: Vec<(Value, u32)>,
    intrinsic_cell_patches: Vec<(Value, u32)>,
    prop_ic_patches: Vec<(Value, u32)>,
    construct_cell_patches: Vec<(Value, u32)>,

    /// Inlining (depth 1): likely-call evidence, funcidx guard patches
    /// (the translate.rs likely-patch protocol), and the segment table.
    likely_patches: Vec<(Value, Value, u32)>,
    segs: Vec<InlineSeg<'a>>,
    /// (call pc, callee script) -> the segment that splice created.
    seg_by_call_pc: HashMap<(Pc, ScriptId), usize>,
    seg_alloc: u32,
    cur_seg: Option<usize>,
    inline_sites: u32,
    /// Root-frame view stash (run_version swaps the view per segment).
    root_script: &'a Script,
    root_source_id: ScriptId,
    root_local_base: u32,
    root_nlocals: u32,
    root_rval_slot_off: u32,
    root_operand_base: u32,
    /// Current frame's byte offset from vp (0 for the root frame).
    frame_base: u32,

    /// Effect side table, keyed by waffle Value at emission time.
    /// Calls record their helper's effect class; the hot
    /// guard/slot/elem loads and stores are kind-tagged at their emitters;
    /// everything else defaults by address rooting at LICM time.
    effects: HashMap<Value, Eff>,
    /// Whether emission has produced a user-heap write in this body --
    /// root or spliced segment, inline store arm or leaf writer helper --
    /// classified by receiver: `wrote_this` = only provably own-this stores
    /// (root frame `this` by SlotRef::This provenance),
    /// `wrote_other` = anything else. The clean-ret accounting of record
    /// (the bytecode scan cannot see splices); read at pass end to revoke
    /// clean-ret flag constants to the classified word.
    wrote_this: bool,
    wrote_other: bool,
    /// The accumulator ORs a NON-threaded body could not record, unioned
    /// body-wide and folded into the clean-ret revocation.
    ///
    /// A body without an accumulator returns a compile-time word. Because a
    /// call does not step the track, an Opt-track return does not by
    /// itself prove the callee wrote no heap: a caller's fork could
    /// believe a zero word from a body that called something that wrote
    /// heap. The proof has to be made somewhere, and body-global
    /// revocation is the mechanism this file already has for exactly that
    /// shape ("the bytecode scan cannot see splices"): every `or_flags_*`
    /// that finds no accumulator records its bits here instead. Threaded
    /// bodies are unaffected -- their accumulator is exact and
    /// per-lineage.
    untracked_flags: u32,
    /// The successor pc a call's failed keep fork armed the just-in-time
    /// on-ramp at (`try_call_return_onramp`), for this version's emission
    /// only. Matching on the pc rather than a bare flag keeps the proof
    /// off the op's other edges -- an exception landing, a result-claim
    /// side arm to some other pc.
    ret_onramp_pc: Option<Pc>,
    /// Whether this body threads the dynamic-flags accumulator (demanded
    /// scan-passing bodies only).
    flags_on: bool,
    /// The tri-state accumulator for the current emission point
    /// ({const-0, const-1, dynamic}); materialized to an i32 only at edges
    /// and merges of differing states.
    cur_flags: FlagsAcc,
    /// Whether this body keeps an add-transition proto-proof cell (the
    /// stamping-ctor / init-delegate bodies, where `this.f = v` adds are
    /// the steady path). The cell is one IC row of the body's own:
    /// `[this ptr, proto0 shape, proto1 shape]`, written by an inline
    /// replay whose proto validation passed on the root `this`, and read
    /// by the body's later replays on that `this`: a row recording the
    /// same two shape words needs no proto loads -- the receiver's proto
    /// is fixed by its (matched) shape, so hop 0 is the same object, and
    /// hop 0's shape fixes hop 1 and the chain beyond it. Zeroed at
    /// activation entry (a dead `this` address can be reused), at every
    /// class-fact kill and at any op that may reshape an existing object
    /// (`op_kills_proto_cell`), and by the GC's region purge. Only the
    /// ROOT body's `this` mints and spends: it is one live object for the
    /// activation, so its raw address identifies it; a construct splice's
    /// fresh object can die and be reallocated at the same address across
    /// a minor GC, which does not purge the region.
    proto_on: bool,
    /// The cell's IC row, allocated on first use in Code mode.
    proto_cell_idx: Option<u32>,
    /// The I32Const flag values emitted at clean returns of non-threaded
    /// bodies, patched to the classified `wrote_*` word at pass end
    /// (order-independent: a store may be emitted after the return
    /// version). Threaded bodies return the accumulator instead.
    clean_ret_flag_patches: Vec<Value>,

    /// Args-into-SSA carriers (the args half of locals-into-SSA): the
    /// current SSA value + repr of each formal, seeded per version from the
    /// carried-arg block params, installed by SetArg and GetArg's load,
    /// killed at CallGc under the same immunity rules as locals.
    args_ssa: Vec<Option<(Value, Repr)>>,
    /// layout id -> (field name -> (fixed slot, value mask)), derived once
    /// from the analysis's layout descriptions. The second evidence source
    /// for a property arm: a per-site row says which layout a site's
    /// receiver probably has, and this says what a layout contains -- so a
    /// receiver carrying a proven class-idx fact can take the same arm at a
    /// site that has no row of its own.
    layout_fields: HashMap<u32, HashMap<NameId, (u32, Claim, Option<ValueRange>)>>,
    /// Per-site callee value cells. bbv emits `emit_inline_classify` once
    /// per version that reaches a call, so the cell is interned on
    /// `(source_id, evid_pc)` -- every version of a site shares the site's
    /// learned callee, so the cell count tracks site count rather than
    /// scaling with version breadth.
    call_cells: HashMap<Site, u32>,
    /// Placeholder address consts `wasm/mod.rs` patches (`call_cell_patches`).
    call_cell_patches: Vec<(Value, u32)>,
}

impl<'a> Bbv<'a> {
    fn new(
        body: FunctionBody,
        ctx: &'a TranslateCtx<'a>,
        atoms: &'a mut AtomTable,
        source_id: ScriptId,
        script: &'a Script,
    ) -> Self {
        let helpers = ctx.helpers;
        let source = ctx.source;
        let opts = ctx.opts;
        // Frame layout.
        let entry = body.entry;
        let cx = body.blocks[entry].params[0].1;
        let sp = body.blocks[entry].params[1].1;
        let argc = body.blocks[entry].params[2].1;
        let retval_out = body.blocks[entry].params[3].1;
        let new_target_param = body.blocks[entry].params[5].1;
        let local_base = 16 + 8 * u32::from(script.nargs);
        let nlocals = max_locals(script);
        let env_slot_off = local_base + 8 * nlocals;
        let needs_env = uses_env_ops(script);
        let needs_args_obj =
            uses_arguments(script) || script.has_mapped_args || uses_actual_args(script);
        let args_obj_slot_off = env_slot_off + if needs_env { 8 } else { 0 };
        let needs_new_target = uses_new_target(script);
        let new_target_slot_off = args_obj_slot_off + if needs_args_obj { 8 } else { 0 };
        let rval_slot_off = new_target_slot_off + if needs_new_target { 8 } else { 0 };
        // The dynamic-flags accumulator is an SSA value threaded through
        // the version graph (a trailing i32 block param;
        // FlagsAcc tri-state at emission), not a frame slot: the frame
        // layout is untouched, the GC never sees the word, and there is no
        // per-invocation init. Only demanded scan-passing bodies thread it.
        let scan_class = script_heap_scan(script, source_id, &ctx.facts.apply_sites);
        let flags_on = ctx.flag_demand.contains(&source_id) && scan_class != ScanClass::Fail;
        let proto_on = ctx.stamp_ctors_in.contains_key(&source_id)
            || ctx.deleg_restamps_in.contains_key(&source_id)
            || ctx
                .this_layouts_in
                .get(&source_id)
                .is_some_and(|li| li.init_home);
        if opts.diagnostics.bbv && scan_class != ScanClass::Fail {
            crate::diag_line!(
                "night: bbv flags sid#{source_id} scan {scan_class:?} threaded {}",
                u8::from(flags_on)
            );
        }
        let mut loop_intervals = super::translate::scan_loop_intervals(script);
        loop_intervals.sort_unstable();
        let this_alias_locals = compute_this_alias_locals(script);
        let operand_base = rval_slot_off + 8;
        let hot_root = hot_locals(script);
        let live_root = {
            let bid_of = |idx: u32| -> Option<u32> {
                let gc = *script.gcthings.get(usize::try_from(idx).ok()?)?;
                let SourceObject::String(st) = ctx.source.object(gc) else {
                    return None;
                };
                ctx.syn_gnames.get(&atoms.names.lookup(st)?).copied()
            };
            std::rc::Rc::new(live::ScriptLive::build(script, &bid_of))
        };
        let apply_fwd_pcs = super::translate::compute_apply_fwd_pcs(
            script,
            &ctx.facts.apply_sites,
            source_id.get(),
        )
        .unwrap_or_default();
        let (gname_call_bids, gname_method_pcs) =
            super::translate::compute_gname_call_bids(source, script, &atoms.names, ctx.syn_gnames);
        let gname_method_pcs: HashSet<Site> = gname_method_pcs
            .into_iter()
            .map(|pc| Site::new(source_id, pc))
            .collect();
        let gname_call_bids: HashMap<Site, u32> = gname_call_bids
            .into_iter()
            .map(|(pc, bid)| (Site::new(source_id, pc), bid))
            .collect();
        Bbv {
            body,
            mem: helpers.mem,
            depth_overflow: false,
            helper_meta: effects::helper_meta_map(&helpers),
            helpers,
            opts,
            source,
            atoms,
            source_id,
            script,
            is_global: false,
            ctx,
            arr_fold: None,
            viz_lpc: Pc::new(0),
            apply_fwd_pcs,
            gname_method_pcs,
            mono_memo: std::cell::Cell::new(None),
            push_named: HashMap::default(),
            lit_rhs_cmp: HashMap::default(),
            noiter_jumps: HashMap::default(),
            trunc_sites: HashMap::default(),
            ret_clean: HashMap::default(),
            ctor_ret_this: HashMap::default(),
            array_named: HashMap::default(),
            this_alias_locals,
            body_off_patches: Vec::new(),
            ctor_nslots_patches: Vec::new(),
            bigint_free: false,
            mode: EmitMode::Code,
            stripping: false,
            virtual_values: 0,
            instrument_values: 0,
            frame_stale: HashSet::default(),
            env_scopes: None,
            op_arm_blocks: Vec::new(),
            op_form: None,
            op_choke: None,
            blockcen_recs: Vec::new(),
            blockcen_ticks: HashMap::default(),
            ver_blocks: HashSet::default(),
            spliced_cost: 0,
            gname_call_bids,
            gname_bids_scanned: [source_id].into_iter().collect(),
            fuse_call_patches: Vec::new(),
            cur: entry,
            cx,
            sp,
            vp: sp,
            argc,
            retval_out,
            new_target_param,
            needs_new_target,
            new_target_slot_off,
            stack: Vec::new(),
            rval_slot_off,
            needs_args_obj,
            args_obj_slot_off,
            local_base,
            nlocals,
            nformals: script.nargs,
            operand_base,
            load_pcs: HashMap::default(),
            needs_env,
            env_slot_off,
            error_blk: None,
            cur_pc: Pc::new(0),
            cur_op: None,
            finally_landing: HashMap::default(),
            blocks: HashMap::default(),
            block_params: HashMap::default(),
            workqueue: Vec::new(),
            processed: HashSet::default(),
            ver_values: HashMap::default(),
            tok_classes: HashMap::default(),
            vers: VerTable::default(),
            cur_ver: VerId(0),
            cur_track: Track::Opt,
            map_changed: false,
            prov_changed: false,
            changed_discover: 0,
            changed_join: 0,
            cur_tokens: Vec::new(),
            gen_only: false,
            is_generator: script.is_generator_or_async,
            gen_dispatch_blk: None,
            gen_resume: Vec::new(),
            fanout_off: false,
            locals_ctx: vec![SlotCtx::TOP; nlocals as usize],
            args_ctx: vec![SlotCtx::TOP; 1 + script.nargs as usize],
            caller_locals_ctx: Vec::new(),
            caller_args_ctx: Vec::new(),
            outer_ctx: Vec::new(),
            gcells_ctx: Vec::new(),
            locals_ssa: vec![None; nlocals as usize],
            outer_ssa: Vec::new(),
            seam_args: Vec::new(),
            ssa_seg: None,
            hot_root,
            live_root,
            live_cache: HashMap::default(),
            post_call: false,
            loop_intervals,
            red_ranges: Vec::new(),
            cfg: std::cell::OnceCell::new(),
            stack_limit_ssa: None,
            dda_fuse_word_addr_ssa: None,
            alloc_cell_patches: Vec::new(),
            iof_cell_patches: Vec::new(),
            strlit_patches: Vec::new(),
            intrinsic_cell_patches: Vec::new(),
            prop_ic_patches: Vec::new(),
            construct_cell_patches: Vec::new(),
            effects: HashMap::default(),
            wrote_this: false,
            wrote_other: false,
            untracked_flags: 0,
            ret_onramp_pc: None,
            clean_ret_flag_patches: Vec::new(),
            likely_patches: Vec::new(),
            segs: Vec::new(),
            seg_by_call_pc: HashMap::default(),
            seg_alloc: 0,
            splices_frozen: false,
            cur_seg: None,
            inline_sites: 0,
            root_script: script,
            root_source_id: source_id,
            root_local_base: local_base,
            root_nlocals: nlocals,
            root_rval_slot_off: rval_slot_off,
            flags_on,
            cur_flags: FlagsAcc::Const(0),
            proto_on,
            proto_cell_idx: None,
            root_operand_base: operand_base,
            frame_base: 0,
            args_ssa: Vec::new(),
            layout_fields: {
                let mut m: HashMap<u32, HashMap<NameId, (u32, Claim, Option<ValueRange>)>> =
                    HashMap::default();
                for li in ctx.this_layouts_in.values() {
                    let e = m.entry(li.layout_id).or_default();
                    for (i, &name) in li.fields.iter().enumerate() {
                        let slot = u32::try_from(i).unwrap();
                        let claim = li.masks.get(i).copied().unwrap_or(Claim::NONE);
                        // A group home's row is the hull over its members,
                        // so it stays sound for the member keyed here.
                        let range = li.ranges.get(i).copied().flatten();
                        e.entry(name).or_insert((slot, claim, range));
                    }
                }
                m
            },
            call_cells: HashMap::default(),
            call_cell_patches: Vec::new(),
        }
    }

    /// Swap the active frame view to `seg` (None = root). The emitters
    /// address every frame slot through these fields.
    fn enter_frame_view(&mut self, seg: Option<usize>) {
        match seg {
            None => {
                self.script = self.root_script;
                self.source_id = self.root_source_id;
                self.local_base = self.root_local_base;
                self.nlocals = self.root_nlocals;
                self.nformals = self.root_script.nargs;
                self.rval_slot_off = self.root_rval_slot_off;
                self.operand_base = self.root_operand_base;
                self.frame_base = 0;
            }
            Some(i) => {
                let s = &self.segs[i];
                self.source_id = s.sid;
                self.script = s.script;
                self.frame_base = s.frame_base;
                self.local_base = s.frame_base + 16 + 8 * u32::from(s.nformals);
                self.nlocals = max_locals(s.script);
                self.nformals = s.nformals;
                self.rval_slot_off = self.local_base + 8 * self.nlocals;
                self.operand_base = self.rval_slot_off + 8;
            }
        }
        self.cur_seg = seg;
    }

    /// Resolve a synthetic pc to its owning segment.
    fn seg_of(&self, pc: Pc) -> Option<usize> {
        self.segs
            .iter()
            .position(|s| pc >= Pc::new(s.base) && pc < Pc::new(s.end))
    }

    /// Inline v2: the evidence-table pc for the current frame -- inside a
    /// segment, likelier tables are keyed (callee sid, local pc); the
    /// frame view already holds the callee sid, so translating the
    /// synthetic pc un-blinds likely_calls/prop_sites/likely_elems at
    /// segment-interior sites.
    /// Whether user code reached from here could write a live frame's
    /// formals without moving a stamp: a MAPPED arguments object (sloppy
    /// simple-parameter functions) aliases them, and one may belong to the
    /// root frame or to any enclosing splice frame. `needs_args_obj` is the
    /// wrong gate for the keep continuations -- strict/unmapped `arguments`
    /// (react's helpers) alias nothing.
    fn mapped_args_reachable(&self) -> bool {
        let mapped = |s: &Script| s.has_mapped_args && s.nargs > 0;
        if mapped(self.root_script) {
            return true;
        }
        // The ACTIVE splice chain only: `segs` holds every segment the body
        // ever opened, and a mapped-args callee spliced somewhere else in
        // the body says nothing about the frames live here.
        let mut seg = self.cur_seg;
        while let Some(i) = seg {
            if mapped(self.segs[i].script) {
                return true;
            }
            seg = self.segs[i].parent;
        }
        false
    }

    fn evid_pc(&self, pc: Pc) -> Pc {
        match self.cur_seg {
            Some(i) => pc - self.segs[i].base,
            None => pc,
        }
    }

    /// The active frame's apply-forward pc set (the root's, or the
    /// segment's callee's).
    pub(super) fn apply_fwd_pcs_here(&self) -> &HashSet<Pc> {
        match self.cur_seg {
            Some(i) => &self.segs[i].apply_fwd_pcs,
            None => &self.apply_fwd_pcs,
        }
    }

    /// Whether `pc` (synthetic) is a proven apply-forward site of the
    /// active frame.
    pub(super) fn is_apply_fwd_site(&self, pc: Pc) -> bool {
        self.apply_fwd_pcs_here().contains(&self.evid_pc(pc))
    }

    /// The evidence-table site that entered the active segment: the call
    /// site in its caller's own pc space (root, or the parent segment's
    /// callee). None at the root.
    pub(super) fn seg_entry_site(&self) -> Option<Site> {
        let i = self.cur_seg?;
        let s = &self.segs[i];
        Some(match s.parent {
            Some(p) => Site::new(self.segs[p].sid, s.call_pc - self.segs[p].base),
            None => Site::new(self.root_source_id, s.call_pc),
        })
    }

    /// `arith_result_ty` over the ctx-computed result interval (the rung
    /// cutover): a clean in-int32 result interval proves the Int32 TAG via
    /// the canonical-boxing provenance condition (see `SlotCtx::iv`).
    fn result_ty_iv(&self, mask: Prims, riv: opsem::Iv) -> TypeDesc {
        if mask.intersects(PRIM_INT32) && mask != PRIM_INT32 {
            if let Some(r) = opsem::iv_clean(riv) {
                if r.lo >= i64::from(i32::MIN) && r.hi <= i64::from(i32::MAX) {
                    if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
                        crate::diag_line!(
                            "night: tighten sid#{} pc {} track {:?}",
                            self.source_id,
                            self.evid_pc(self.cur_pc),
                            self.cur_track
                        );
                    }
                    return prim_desc(PRIM_INT32);
                }
            }
        }
        prim_desc(mask)
    }

    /// Frame-entry prologue: formal padding, locals/args-obj/rval
    /// `undefined` init, new.target spill, stack-limit + dda-fuse SSA loads,
    /// the environment head, and the eager mapped-arguments object.
    /// The two fixed-address words every body reads: the AOT stack limit and
    /// the dynamic-code fuse's address. They are SSA values the whole body
    /// uses, so in a generator body they are loaded ahead of the
    /// fresh-vs-resume fork -- the prologue block does not dominate the
    /// resume path.
    pub(super) fn emit_entry_word_loads(&mut self) {
        if self.stack_limit_ssa.is_some() {
            return;
        }
        let limit_slot = self.i32_const(self.helpers.night_stack_limit_base);
        let limit = self.load_i32(limit_slot, 0);
        self.stack_limit_ssa = Some(limit);
        let dda_slot = self.i32_const(self.helpers.dda_fuse_addr_slot);
        let dda_addr = self.load_i32(dda_slot, 0);
        self.dda_fuse_word_addr_ssa = Some(dda_addr);
    }

    fn emit_frame_prologue(&mut self) {
        self.emit_formal_padding();
        let undef = self.boxed_const(TAG_UNDEFINED << 32);
        for j in 0..self.nlocals {
            self.store_i64(self.vp, self.local_base + 8 * j, undef);
        }
        if self.needs_args_obj {
            self.store_i64(self.vp, self.args_obj_slot_off, undef);
        }
        if self.needs_new_target {
            self.store_i64(self.vp, self.new_target_slot_off, self.new_target_param);
        }
        self.store_i64(self.vp, self.rval_slot_off, undef);
        self.kill_proto_cell();
        self.emit_entry_word_loads();
        if self.needs_env {
            self.emit_env_setup();
        }
        // Skipped when the object is elided (apply-forward: the flow check
        // proved no observer, and `nargs == 0` means no formal routes
        // through it).
        if self.script.has_mapped_args && self.apply_fwd_pcs.is_empty() {
            let sp = self.sp;
            let argc = self.argc;
            let built = if self.needs_env {
                let env = self.load_i64(self.vp, self.env_slot_off);
                self.rt_call(self.helpers.arguments_env, true, move |_, _| {
                    vec![sp, argc, env]
                })
                .unwrap()
            } else {
                self.rt_call(self.helpers.arguments_, true, move |_, _| vec![sp, argc])
                    .unwrap()
            };
            self.store_i64(self.vp, self.args_obj_slot_off, built);
        }
    }
}

/// The scan verdict: ReadOnly = every op heap-readonly on its
/// inline paths; StoreOnly = readonly except store ops (SetProp /
/// StrictSetProp / SetElem / StrictSetElem), whose receiver
/// classification is emission's job; Fail = anything else.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ScanClass {
    ReadOnly,
    StoreOnly,
    Fail,
}

/// The heap-readonly opcode scan in free form (the flag-demand
/// computation runs it before any emitter exists); allowlist semantics
/// unchanged from the memoized ret_clean_for above, plus the
/// StoreOnly tier.
/// Whether this body's `arguments` is provably never materialized: every
/// value the `Arguments` op produces flows only into `T.apply(this,
/// arguments)` forwards, which the lowering elides. `compute_apply_fwd_pcs`
/// is the proof and already requires `nargs == 0`, so there are no formals
/// for a mapped object to alias either.
pub(super) fn args_object_elided(
    script: &Script,
    sid: ScriptId,
    apply_sites: &HashMap<Site, crate::facts::CallForm>,
) -> bool {
    super::translate::compute_apply_fwd_pcs(script, apply_sites, sid.get()).is_some()
}

pub(crate) fn script_heap_scan(
    script: &Script,
    sid: ScriptId,
    apply_sites: &HashMap<Site, crate::facts::CallForm>,
) -> ScanClass {
    use JSOp::*;
    if script.is_generator_or_async {
        return ScanClass::Fail;
    }
    // Mapped `arguments` aliases the formals, so a write through the object
    // changes a formal invisibly -- except where the object is never
    // materialized at all. That is exactly the generated-constructor idiom
    // `function C() { C.C.apply(this, arguments) }`, a common generated
    // ctor-wrapper shape; vetoing the whole body for it would mean none of
    // them threaded an effect word, so no `new C(...)` site above them
    // could fork.
    if script.has_mapped_args && !args_object_elided(script, sid, apply_sites) {
        return ScanClass::Fail;
    }
    let mut saw_store = false;
    for op in script.parser().opcodes() {
        // Every other arguments-reading op is on the allowlist below; only
        // materializing the object is disqualifying, and only when it really
        // is materialized.
        if op == Arguments {
            if args_object_elided(script, sid, apply_sites) {
                continue;
            }
            return ScanClass::Fail;
        }
        // Store ops: receiver classification is emission's job. For literal
        // allocs and their fills, the inline nursery-bump arms neither GC
        // nor touch pre-existing heap (fills hit the fresh
        // literal, contributing nothing), and the helper fallbacks are
        // CallGc -- they saturate the lineage dynamically. Either way the
        // per-lineage word stays truthful, so the ops stop disqualifying
        // the body; they only bar the ReadOnly tier.
        if matches!(
            op,
            SetProp
                | StrictSetProp
                | SetElem
                | StrictSetElem
                | NewInit
                | NewObject
                | NewArray
                | InitProp
                | InitHiddenProp
                | InitLockedProp
                | InitElem
                | InitHiddenElem
                | InitLockedElem
                | InitElemArray
                | InitElemInc
        ) {
            saw_store = true;
            continue;
        }
        if !matches!(
            op,
            Undefined
                | Null
                | False
                | True
                | Int32
                | Zero
                | One
                | Int8
                | Uint16
                | Uint24
                | Double
                | String
                | Symbol
                | Void
                | Typeof
                | TypeofExpr
                | TypeofEq
                | Pos
                | Neg
                | BitNot
                | Not
                | BitOr
                | BitXor
                | BitAnd
                | Eq
                | Ne
                | StrictEq
                | StrictNe
                | StrictConstantEq
                | StrictConstantNe
                | Lt
                | Gt
                | Le
                | Ge
                | Instanceof
                | In
                | Lsh
                | Rsh
                | Ursh
                | Add
                | Sub
                | Inc
                | Dec
                | Mul
                | Div
                | Mod
                | Pow
                | NopIsAssignOp
                | ToPropertyKey
                | ToNumeric
                | ToString
                | IsNullOrUndefined
                | GlobalThis
                | GetProp
                | GetElem
                | HasOwn
                | CheckIsObj
                | CheckObjCoercible
                | Call
                | CallContent
                | CallIgnoresRv
                // Constructs sit with the calls: create_this is a quiet
                // alloc, and the ctor call's effects arrive through
                // the construct word / merged track exactly like a call's.
                | New
                | IsConstructing
                | JumpTarget
                | LoopHead
                | Goto
                | JumpIfFalse
                | JumpIfTrue
                | And
                | Or
                | Coalesce
                | Case
                | Default
                | TableSwitch
                | Return
                | GetRval
                | SetRval
                | RetRval
                | CheckReturn
                | Throw
                | ThrowMsg
                | Uninitialized
                | InitLexical
                | CheckLexical
                | CheckAliasedLexical
                | CheckThis
                | GetGName
                | GetArg
                | GetFrameArg
                | GetLocal
                | ArgumentsLength
                | GetActualArg
                | GetAliasedVar
                | GetIntrinsic
                | Callee
                | SetArg
                | SetLocal
                | FunctionThis
                | Pop
                | PopN
                | Dup
                | Dup2
                | DupAt
                | Swap
                | Pick
                | Unpick
                | Nop
                | Lineno
                | NopDestructuring
        ) {
            return ScanClass::Fail;
        }
    }
    if saw_store {
        ScanClass::StoreOnly
    } else {
        ScanClass::ReadOnly
    }
}

/// The flag-demand set: sids whose returned flags word some caller can
/// Consume, so only their bodies pay accumulator
/// ORs and dynamic returns. Roots: mono-resolved call targets passing
/// the heap-readonly scan. Closure: a demanded scan-passing body's
/// accumulator ORs its callees' words, so its resolved targets are
/// demanded too. Unresolved edges are not walked, and callers DO fork on
/// unresolved callees (the runtime word decides), so a non-demanded body
/// really is forked on -- soundness there rests on its compile-time word,
/// which `untracked_flags` revokes to all-set the moment it calls
/// anything. That is conservative, not wrong: such a site loses its clean
/// arm and keeps its epoch-proven keep arm. Widening the roots to every
/// scan-passing body would buy the clean arm back at the price of an
/// accumulator in every one of them.
pub(crate) fn compute_flag_demand(
    source: &Source,
    facts: &LikelyFacts,
) -> rustc_hash::FxHashSet<ScriptId> {
    let scan_of = |sid: ScriptId| -> ScanClass {
        match source.object(sid.source()) {
            SourceObject::Script(s) => script_heap_scan(s, sid, &facts.apply_sites),
            _ => ScanClass::Fail,
        }
    };
    let mut by_caller: HashMap<ScriptId, Vec<ScriptId>> = HashMap::default();
    for (site, sids) in facts.scripted_call_sites() {
        by_caller
            .entry(site.script)
            .or_default()
            .extend(sids.iter());
    }
    // Apply-forward edges count too. At `T.apply(this, arguments)` the site's
    // own callee is `apply` -- a native, so `scripted_call_sites` has nothing
    // for it -- while the body that actually runs is `T`. Without this edge a
    // forwarded callee is never demanded, returns const all-set, and the
    // caller's accumulator reads MUT_OTHER however clean the callee was,
    // which would cost nearly every construct fork above a ctor-wrapper
    // population its clean arm.
    for (site, &target) in &facts.apply_targets {
        by_caller.entry(site.script).or_default().push(target);
    }
    let mut demanded = rustc_hash::FxHashSet::default();
    // Roots mirror the flag-site gate population -- consumer-reachable
    // only: ReadOnly callees, the population the fork actually lands
    // clean on. The closure still walks through any non-Fail demanded
    // body so transitive callees feed classified dynamic words upward.
    let mut work: Vec<ScriptId> =
        facts
            .scripted_call_sites()
            .filter_map(|(_, sids)| match sids {
                [sid] if matches!(scan_of(*sid), ScanClass::ReadOnly | ScanClass::StoreOnly) => {
                    Some(*sid)
                }
                _ => None,
            })
            .chain(
                facts.apply_targets.values().copied().filter(|&sid| {
                    matches!(scan_of(sid), ScanClass::ReadOnly | ScanClass::StoreOnly)
                }),
            )
            .collect();
    while let Some(s) = work.pop() {
        if !demanded.insert(s) {
            continue;
        }
        if scan_of(s) == ScanClass::Fail {
            continue;
        }
        if let Some(targets) = by_caller.get(&s) {
            work.extend(targets.iter().copied());
        }
    }
    demanded
}
