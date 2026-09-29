//! The JSOps-to-MIR builder (`docs/MIR.md` §8), for the M2 subset: locals,
//! args, `this` and the operand stack as SSA values; int32 and double
//! arithmetic and compares, with the generic `js.*` ops as the fallback;
//! branches, loops and returns. Any other op declines the script, which
//! then runs in baseline alone.
//!
//! **Types.** Every frame slot has an abstract type: a raw `I32`, `F64` or
//! `Bool`, or a boxed `Val` with a tag set. Each bytecode basic block
//! starts from fixed entry types (its MIR block's params), and those come
//! from a fixpoint: the builder runs over the whole script, recording the
//! types that flow into every block; where they are wider than the block's
//! current entry types, the entry types widen and the builder runs again.
//! The run in which nothing widens is the result, so the type policy
//! exists once, in the emitting code. The widening lattice is small
//! (`I32 < F64`, and everything else joins to `Val` of the union of tags),
//! so the fixpoint comes quickly.
//!
//! **Guard-at-defs.** Formals with an `arg_types` claim are guarded at the
//! entry root: int32 to `I32`, numeric to `F64`. A failing guard exits to
//! baseline at pc 0.
//!
//! **Exits.** Every fallible op's `fail` edge exits at its own pc with the
//! state from before the op, since nothing observable has happened (§5.1's
//! resume rule), and every throwing op's `err` edge goes to its pc's throw
//! block (§5.3). Both are shared per pc and carry the whole frame, boxed.

use std::collections::BTreeMap;

use crate::bytecode::{BytecodeParser, JSOp, Script};
use crate::facts::Claim;
use crate::ids::{ArgIndex, Pc, ScriptId};
use crate::mir;
use crate::mir::func::{Edge, EdgeArg, FrameShape, LoopDecl, Root, RootKind};
use crate::mir::ops::{
    ArithOp, BitOp, Cc, ConstVal, F64Op, JsBinop, JsCc, JsUnop, MathFn, NumRepr, Opcode, RtOp,
    UnboxKind,
};
use crate::mir::types::{
    KeyRange, LayoutClaim, LayoutState, ObjInfo, ObjKind, TagSet, Type as MType,
};
use crate::opsem::{PRIM_BIGINT, PRIM_INT32, PRIM_NULL, PRIM_UNDEFINED};
use crate::wasm::baseline::layout::{self, FrameLayout, StackDepths};
use crate::wasm::translate::{StampCtorIn, TranslateCtx};

type R<T> = Result<T, String>;

/// A frame slot's abstract type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ty {
    I32,
    F64,
    Bool,
    Val(TagSet),
    /// An object of one of `keys`' layouts, with its TYPES bit if the
    /// first flag says so and its SLOTS bit if the second does: the raw
    /// object (`obj{L…}`), proven by a guard that dominates (§4.3). The
    /// slot keeps the proof across joins and loops, so the field accesses
    /// through it take no guard of their own (an access with a slot
    /// prediction guards SLOTS where it is not yet proven).
    Obj(KeyRange, bool, bool),
    /// An object proven of `keys`' layouts before a fence that may have
    /// changed that (a call, a generic op): the raw object (`obj`). A
    /// field access through it guards the layout again, exiting on a miss
    /// (identity rarely changes), and refines the slot back to `Obj`.
    ObjHint(KeyRange),
    /// An object under construction for layout `key` with its first `n`
    /// fields added, TYPES held if the flag says so (MIR.md §2.3,
    /// `obj{Lkey constructing(n)}`, raw): made by an inlined `new`'s
    /// allocation, advanced by `init_field`, published by `publish_layout`
    /// once every field is there. Its field accesses below `n` are typed;
    /// a fence (anything that may reach the object) demotes it to a boxed
    /// object, which the rest of the constructor treats generically.
    Ctor(u32, u32, bool),
    /// A native object (`obj{Native}`, raw): its elements are addressable
    /// (`load_elem`, `store_elem`). Immutable, so no fence kills it.
    Native,
    /// A typed array of this kind (`obj{TypedArray(k)}`, raw): its
    /// elements are `load_ta`/`store_ta`. Immutable.
    Ta(crate::opsem::TaKind),
    /// A closure of this script (boxed, `val{object}`): made by a
    /// `Lambda` here, or the caller's for a formal of a callee built for
    /// inlining at a call passing one (the context-sensitive target: a
    /// call of it has exactly this callee).
    Fn(ScriptId),
    /// A local, formal or rval that is dead here (never read before it is
    /// next written): no value, no block param. An exit passes it as
    /// `const.val dead`.
    Dead,
}

/// A number's raw representation, for arithmetic.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Num {
    I32,
    F64,
}

impl Ty {
    fn mir(self) -> MType {
        match self {
            Ty::I32 => MType::I32_TOP,
            Ty::F64 => MType::F64_TOP,
            Ty::Bool => MType::Bool,
            Ty::Val(t) => MType::val(t),
            Ty::Fn(_) => MType::val(TagSet::OBJECT),
            Ty::Obj(keys, types, slots) => MType::Obj(ObjInfo {
                layout: Some(LayoutClaim {
                    keys,
                    types,
                    slots,
                    state: LayoutState::Published,
                }),
                ..ObjInfo::TOP
            }),
            Ty::ObjHint(_) => MType::OBJ_TOP,
            Ty::Ctor(key, n, types) => MType::Obj(ObjInfo {
                layout: Some(LayoutClaim {
                    keys: KeyRange::one(crate::ids::LayoutKey::new(key)),
                    types,
                    slots: true,
                    state: LayoutState::Constructing(n),
                }),
                ..ObjInfo::TOP
            }),
            Ty::Native => MType::Obj(ObjInfo::kind(ObjKind::Native)),
            Ty::Ta(k) => MType::Obj(ObjInfo::kind(ObjKind::TypedArray(k))),
            Ty::Dead => unreachable!("a dead slot has no type"),
        }
    }

    fn tags(self) -> TagSet {
        match self {
            Ty::I32 => TagSet::INT32,
            Ty::F64 => TagSet::NUMBER,
            Ty::Bool => TagSet::BOOLEAN,
            Ty::Val(t) => t,
            Ty::Obj(..) | Ty::ObjHint(_) | Ty::Ctor(..) | Ty::Native | Ty::Ta(_) | Ty::Fn(_) => TagSet::OBJECT,
            Ty::Dead => TagSet::NONE,
        }
    }

    fn join(self, o: Ty) -> Ty {
        match (self, o) {
            (a, b) if a == b => a,
            (Ty::Dead, x) | (x, Ty::Dead) => x,
            (Ty::I32, Ty::F64) | (Ty::F64, Ty::I32) => Ty::F64,
            (Ty::Obj(k1, t1, s1), Ty::Obj(k2, t2, s2)) => Ty::Obj(k1.hull(&k2), t1 && t2, s1 && s2),
            (Ty::Ctor(k1, n1, t1), Ty::Ctor(k2, n2, t2)) if k1 == k2 && n1 == n2 => Ty::Ctor(k1, n1, t1 && t2),
            (Ty::Obj(k1, ..) | Ty::ObjHint(k1), Ty::Obj(k2, ..) | Ty::ObjHint(k2)) => {
                Ty::ObjHint(k1.hull(&k2))
            }
            (a, b) => Ty::Val(a.tags().union(b.tags())),
        }
    }

    /// Whether a value of type `self` can be passed where `o` is expected
    /// (after `convert`). Anything fits a dead slot.
    fn fits(self, o: Ty) -> bool {
        o == Ty::Dead || (self != Ty::Dead && self.join(o) == o)
    }

    /// The raw number representation this type unboxes to without a
    /// check, if it is a number.
    fn num(self) -> Option<Num> {
        match self {
            Ty::I32 => Some(Num::I32),
            Ty::F64 => Some(Num::F64),
            Ty::Val(t) if t.is_nonempty_subset_of(TagSet::INT32) => Some(Num::I32),
            Ty::Val(t) if t.is_nonempty_subset_of(TagSet::NUMBER) => Some(Num::F64),
            _ => None,
        }
    }
}

/// The representation a numeric claim is speculated in (§8's
/// guard-at-defs): int32 for an int32-only claim; with `int_first`, also
/// for a number claim with int32 in it that is not flagged double-first
/// (the order bbv's typed-load ladder tries), exiting on a double; f64
/// for other number claims. `None` for anything else. Int-first suits
/// formals, element and name reads (indices, digits, counters: crypto's
/// am3 gains 17%); property reads and call results often hold doubles
/// the claim does not flag (raytrace's vectors), and an exit per double
/// costs far more than the ToInt32s int-first saves.
const SPECULATE_INT_FIRST: bool = true;

/// Whether the generic runtime ops (`js.rt`, `js.throw`, `js.typeof`)
/// are built.
const RT_OPS: bool = true;

/// Whether `T.apply(this, arguments)` forwards the actuals.
const APPLY_FWD: bool = true;

/// Whether `T.call(thisArg, args…)` inlines its resolved targets.
const CALL_FWD: bool = true;

/// Whether an inlined `new` builds its constructor for a `this` of the
/// constructing type (MIR.md §2.3, `Ty::Ctor`).
const CTOR_TYPES: bool = true;

/// Whether scripts that read their actuals are built.
const ACTUALS: bool = true;

fn num_claim_ty(claim: crate::facts::Claim, int_first: bool) -> Option<Ty> {
    let prims = claim.prims();
    if claim.is_none() || claim.is_object() || prims.is_empty() {
        None
    } else if prims.subset_of(PRIM_INT32)
        || (SPECULATE_INT_FIRST
            && int_first
            && prims.subset_of(crate::opsem::NUM)
            && prims.intersects(PRIM_INT32)
            && !claim.double_first())
    {
        Some(Ty::I32)
    } else if prims.subset_of(crate::opsem::NUM) {
        Some(Ty::F64)
    } else {
        None
    }
}

impl<'a> Shape<'a> {
    /// Whether callee `k` is small enough to inline at `pc` among
    /// `ntargets` targets: bbv's caps, 150 bytes of bytecode for one
    /// target (200 in a loop), 500 each for several.
    /// Layout `cls`'s field `name`: its slot and value claim, from the
    /// layout rows (`this_layouts_in`, as bbv's `layout_fields`).
    fn layout_field(&self, cls: u32, name: crate::ids::NameId) -> Option<(u32, crate::facts::Claim)> {
        let mut cache = self.layout_fields.borrow_mut();
        let m = cache.get_or_insert_with(|| {
            let mut m: BTreeMap<u32, BTreeMap<crate::ids::NameId, (u32, crate::facts::Claim)>> = BTreeMap::new();
            for li in self.ctx.this_layouts_in.values() {
                let e = m.entry(li.layout_id).or_default();
                for (i, &n) in li.fields.iter().enumerate() {
                    let claim = li.masks.get(i).copied().unwrap_or(crate::facts::Claim::NONE);
                    e.entry(n).or_insert((u32::try_from(i).unwrap(), claim));
                }
            }
            m
        });
        m.get(&cls)?.get(&name).copied()
    }

    /// Every class whose layout types field `name` (a class word's
    /// identity, layout key + 1), with its type for it; made on first use.
    fn name_classes(&self, name: crate::ids::NameId) -> std::rc::Rc<Vec<(u32, TagSet)>> {
        if let Some(v) = self.name_classes.borrow().get(&name) {
            return v.clone();
        }
        let v: Vec<(u32, TagSet)> = crate::wasm::bbv::field_classes(self.ctx, name)
            .into_iter()
            .map(|(k, c)| (k, claim_tags(c)))
            .collect();
        let v = std::rc::Rc::new(v);
        self.name_classes.borrow_mut().insert(name, v.clone());
        v
    }

    /// TYPES where layout `k` predicts a type for any field
    /// (`layout_types_bit`).
    fn types_bit(&self, k: u32) -> u32 {
        crate::wasm::bbv::layout_types_bit(self.ctx, k)
    }

    /// A construct site's allocation word (`typed_alloc_word`).
    fn alloc_word(&self, mono: Option<ScriptId>, site: crate::ids::Site) -> u32 {
        crate::wasm::bbv::typed_alloc_word(self.ctx, mono, site)
    }

    /// Whether a call of script `k` may go straight to its compiled body
    /// (bbv's `likely_call_target`): not a class constructor, generator or
    /// async function.
    fn direct_ok(&self, k: ScriptId) -> bool {
        matches!(
            self.ctx.source.object(crate::source::SourceObjectId::new(k.get())),
            crate::source::SourceObject::Script(ks) if !ks.is_class_ctor && !ks.is_generator_or_async
        )
    }

    /// Whether nothing in the script catches or closes on a throw (only
    /// loop notes; not a generator): baseline's landing for any throw is
    /// its error return, which reads nothing of the frame.
    fn throws_uncaught(&self) -> bool {
        !self.script.is_generator_or_async
            && self
                .script
                .try_notes
                .iter()
                .all(|t| t.kind == crate::bytecode::TryNoteKind::Loop)
    }

    /// Callee `k` built for inlining here (§5.5), if it may be: an
    /// inline-eligible script that is not this one, not a constructor
    /// that stamps its `this`, and small enough once built.
    fn callee(&self, k: ScriptId, ictx: InlineCtx) -> Option<std::rc::Rc<super::inline::Callee>> {
        self.callee_ctx(k, &[], None, ictx)
    }

    /// `callee`, built knowing which of its formals the call passes a
    /// known closure in (`Ty::Fn`, by formal; missing ones none), and for
    /// a `this` under construction (`Ty::Ctor` of these parts) where the
    /// call passes one: context-sensitive in the closures it passes and
    /// the receiver's construction state, and built where `ictx` says.
    fn callee_ctx(
        &self,
        k: ScriptId,
        fns: &[Option<ScriptId>],
        this_ctor: Option<(u32, u32, bool)>,
        ictx: InlineCtx,
    ) -> Option<std::rc::Rc<super::inline::Callee>> {
        let mut fns = fns.to_vec();
        while fns.last() == Some(&None) {
            fns.pop();
        }
        let key = (k, fns, this_ctor, ictx);
        if let Some(c) = self.callees.borrow().get(&key) {
            return c.clone();
        }
        let c = self.build_callee(k, &key.1, this_ctor, ictx).map(std::rc::Rc::new);
        self.callees.borrow_mut().insert(key, c.clone());
        c
    }

    fn build_callee(
        &self,
        k: ScriptId,
        fns: &[Option<ScriptId>],
        this_ctor: Option<(u32, u32, bool)>,
        ictx: InlineCtx,
    ) -> Option<super::inline::Callee> {
        if k == self.sid {
            return None;
        }
        let names = self.names?;
        let crate::source::SourceObject::Script(ks) =
            self.ctx.source.object(crate::source::SourceObjectId::new(k.get()))
        else {
            return None;
        };
        if !super::inline_eligible(self.ctx, ks) {
            return None;
        }
        let nargs = usize::from(ks.nargs);
        let fns: Vec<Option<ScriptId>> = fns.iter().copied().take(nargs).collect();
        let (mut mm, f, this_out, sites) = match build_at(self.ctx, names, k, ks, false, ictx, &fns, this_ctor) {
            Ok(r) => r,
            Err(_) => return None,
        };
        mm.script_addrs.insert(k, ks.addr);
        let max_depth = StackDepths::compute(ks).ok()?.max;
        let fenced = super::inline::fenced(&f, &mm);
        Some(super::inline::Callee {
            mm,
            f,
            max_depth,
            fenced,
            this_out,
            sites,
            reads_actuals: layout::reads_actuals(ks),
        })
    }
}

/// A property access the analysis predicts: the receiver's layouts
/// `[lo, hi]`, and whether the field's predicted type is backed by the
/// stamp's TYPES bit: with it set on a valid stamp, every field holds a
/// value of its layout's predicted type (any type), so a read is of that
/// type unchecked.
#[derive(Clone, Copy, Debug)]
struct TypedSite {
    lo: u32,
    hi: u32,
    types: bool,
    /// The analysis's value claim, to guard at the def when the stamp
    /// does not back it (`!types`).
    claim: crate::facts::Claim,
    /// The field's predicted type over the layouts: what a read is (their
    /// union), and what a store must be to keep TYPES on every one of
    /// them (their intersection).
    load_tags: TagSet,
    store_tags: TagSet,
    /// Whether the field has a slot prediction (its layouts' rows place
    /// it): its access then needs SLOTS proven, and reads the slot; one
    /// without finds the slot through an IC, under TYPES alone.
    slotted: bool,
}

impl TypedSite {
    fn claim_ty(&self) -> MType {
        if self.types {
            MType::val(self.load_tags)
        } else {
            MType::VAL_TOP
        }
    }
}

/// The tags a likelier claim admits.
fn claim_tags(c: crate::facts::Claim) -> TagSet {
    TagSet {
        prims: c.prims(),
        object: c.bits() & crate::facts::Claim::OBJECT.bits() != 0,
        magic: false,
    }
}

/// A frame slot: the SSA value holding it now, and its type.
#[derive(Clone, Copy, Debug)]
struct Slot {
    v: mir::Value,
    ty: Ty,
}

impl Slot {
    /// A dead slot (`Ty::Dead`): its value is never used.
    fn dead() -> Slot {
        Slot {
            v: mir::Value::from_u32(u32::MAX),
            ty: Ty::Dead,
        }
    }
}

/// Build the MIR body for `script`, or decline with a reason.
pub fn build<'a>(
    ctx: &'a TranslateCtx<'a>,
    names: &'a crate::ids::Names,
    sid: ScriptId,
    script: &'a Script,
    is_global: bool,
) -> Result<(mir::Module, mir::Func), String> {
    build_at(ctx, names, sid, script, is_global, InlineCtx::ROOT, &[], None).map(|(m, f, _, _)| (m, f))
}

/// Element accesses the analysis predicts on arrays, with int32 keys, are
/// `load_elem`/`store_elem` on a native receiver.
const NATIVE_ELEMS: bool = true;

/// Element accesses the analysis predicts on typed arrays are
/// `load_ta`/`store_ta`.
const TA_ELEMS: bool = true;

/// A loop-invariant array's receiver guard is hoisted to the loop's entry.
const HOIST_NATIVE: bool = true;

/// Scripts whose mapped `arguments` alias formals are built: the formals
/// are read and written through the object.
const MAPPED_ARGS: bool = true;

/// `new` of a site's one constructor is inlined.
const INLINE_CONSTRUCT: bool = true;

/// Typed field accesses exit on a dirty IC arm rather than rejoin.
const DIRTY_EXITS: bool = true;

/// A type test a branch consumes narrows the tested value on the branch
/// it proves (`fuse_test`).
const NARROW_TESTS: bool = true;

/// A call of a known single callee not inlined gets a direct arm
/// (`attach_targets`).
const DIRECT_CALLS: bool = true;

/// A call of a closure the frame knows (`Ty::Fn`) has exactly its script
/// as callee, and a callee built for inlining knows its formals' closures.
const CALL_KNOWN_FNS: bool = true;

/// How many likely callees a call not inlined gets direct arms for.
const MAX_DIRECT_TARGETS: usize = 4;


/// A generic element op at a polymorphic typed-array site probes the
/// typed-array kinds (`ta_poly`).
const TA_POLY: bool = true;

/// A typed array's `.length` is its length slot (`length.ta`).
const LENGTH_TA: bool = true;

/// Property stores keep TYPES for a value of the field's predicted type
/// (`field_claim`), and reads under TYPES are of that type.
const FIELD_MASKS: bool = true;

/// How many classes a store lists (`field_claim`) before it names only
/// the receiver's predicted ones.
const MAX_STORE_CLASSES: usize = crate::wasm::bbv::MAX_STORE_CLASSES;

/// Receivers the analysis hints one class for get typed sites
/// (`hinted_site`).
const CLS_HINTS: bool = true;

/// `Math.<fn>(...)` calls are typed ops behind a native check (`math_call`).
const MATH_CALLS: bool = true;

/// The Math functions `math_call` types, by property name.
fn math_fn_named(s: &str) -> Option<MathFn> {
    Some(match s {
        "abs" => MathFn::Abs,
        "floor" => MathFn::Floor,
        "ceil" => MathFn::Ceil,
        "trunc" => MathFn::Trunc,
        "sqrt" => MathFn::Sqrt,
        "fround" => MathFn::Fround,
        "min" => MathFn::Min,
        "max" => MathFn::Max,
        "pow" => MathFn::Pow,
        "sin" => MathFn::Sin,
        "cos" => MathFn::Cos,
        _ => return None,
    })
}

fn math_fn_name(m: MathFn) -> &'static str {
    match m {
        MathFn::Abs => "abs",
        MathFn::Floor => "floor",
        MathFn::Ceil => "ceil",
        MathFn::Trunc => "trunc",
        MathFn::Sqrt => "sqrt",
        MathFn::Fround => "fround",
        MathFn::Min => "min",
        MathFn::Max => "max",
        MathFn::Pow => "pow",
        MathFn::Sin => "sin",
        MathFn::Cos => "cos",
        _ => "?",
    }
}

/// Generic ops keep proven layouts on their clean edge (`js_keep`).
const KEEP_ON_CLEAN: bool = true;

/// Syntactic globals read and written as `load_gname`/`store_gname`
/// behind `check.binding` (§3).
const TYPED_GNAMES: bool = true;

/// `a.length` of a receiver the builder has array evidence for is
/// `length.array` behind `guard.kind Array` (§7).
const LENGTH_ARRAY: bool = true;

/// Guard a method's `this` to its predicted layouts at `FunctionThis`.
const THIS_ENTRY_GUARD: bool = true;

// Inlining admission mirrors bbv's (`Bbv::inline_candidates_for`): the
// same caps in the same order, so both tiers inline the same sites.
/// How deep inlining nests below a call site in a loop, and below one not
/// in a loop (the root site's: bbv's `max_depth`).
const MAX_INLINE_DEPTH_LOOP: u32 = 8;
const MAX_INLINE_DEPTH: u32 = 4;
/// The most sites one function splices, its callees' own included,
/// counted depth-first (bbv's per-body `MAX_INLINE_SITES`).
const MAX_INLINE_SITES: u32 = crate::constants::MAX_INLINE_SITES;
/// The most targets a call site inlines (a guard chain on the script).
const MAX_INLINE_TARGETS: usize = crate::constants::MAX_INLINE_TARGETS;
/// Splice fuel (bbv's `SPLICE_FUEL_VALUES`, 100000 waffle values, at the
/// ~4 values a MIR instruction lowers to): past this many instructions a
/// function splices nothing more, but callees of at most
/// `SMALL_SPLICE_BC` bytes, up to the harder line.
const SPLICE_FUEL_INSTS: usize = 25_000;
const SMALL_SPLICE_BC: usize = 160;
const SMALL_SPLICE_FUEL_INSTS: usize = 60_000;

/// `build`, as the callee of an inlining `depth` levels down.
fn build_at<'a>(
    ctx: &'a TranslateCtx<'a>,
    names: &'a crate::ids::Names,
    sid: ScriptId,
    script: &'a Script,
    is_global: bool,
    ictx: InlineCtx,
    formal_fns: &[Option<ScriptId>],
    this_ctor: Option<(u32, u32, bool)>,
) -> Result<(mir::Module, mir::Func, Option<(u32, u32, bool)>, u32), String> {
    if is_global {
        return Err("global script".into());
    }
    // A MIR script carries two bodies (MIR and baseline). An
    // Emscripten-sized function would dominate the batch's memory and
    // compile time for little gain, so it stays in baseline.
    const MAX_MIR_BYTECODE: usize = 32 * 1024;
    if script.bytecode.len() > MAX_MIR_BYTECODE {
        return Err(format!(
            "too large for MIR ({} bytecode bytes)",
            script.bytecode.len()
        ));
    }
    let fl = FrameLayout::of(script);
    // A resume re-enters with no actuals (`EnterNightResume`), which a
    // body reading them past its formals cannot rebase over.
    if script.is_generator_or_async && fl.rebase_vp {
        return Err("generator reading its actuals".into());
    }
    // A mapped arguments object aliases the formals. With no formals there
    // is nothing to alias, and the object (made by the runtime, which maps
    // by the callee) is an unmapped one plus `callee`: scheme runtimes'
    // variadic `sc_list`, prototype.js's `Class.create` wrapper.
    if script.has_mapped_args && script.nargs > 0 && !MAPPED_ARGS {
        return Err("mapped arguments".into());
    }
    if !ACTUALS && fl.rebase_vp {
        return Err("reads actuals".into());
    }
    // The env chain is fixed for the whole activation (§5.1): the callee's
    // own environment, or the one the entry makes (`env_setup`); an op
    // that pushes a scope declines on its own.
    let depths = StackDepths::compute(script).map_err(|e| format!("stack depths ({e})"))?;
    let mut shape = Shape::of(ctx, sid, script, fl, depths)?;
    shape.names = Some(names);
    shape.apply_fwd = crate::wasm::translate::compute_apply_fwd_pcs(script, &ctx.facts.apply_sites, sid.get())
        .filter(|s| APPLY_FWD && !s.is_empty());
    shape.inline_depth = ictx.depth;
    shape.ictx = ictx;
    shape.formal_fns = formal_fns.to_vec();
    shape.this_ctor = this_ctor;
    for (i, &gc) in script.gcthings.iter().enumerate() {
        if gc.is_other() {
            continue;
        }
        if let crate::source::SourceObject::String(s) = ctx.source.object(gc) {
            let Some(n) = names.lookup(s.chars()) else {
                continue;
            };
            let i = u32::try_from(i).unwrap();
            if let Some(fg) = ctx.fused_gnames.get(&n) {
                shape.fused.insert(i, *fg);
            }
            if let Some(c) = ctx.facts.gname_types.get(&n) {
                shape.gname_types.insert(i, *c);
            }
            if let Some(&bid) = ctx.syn_gnames.get(&n) {
                shape.syn_bids.insert(i, bid);
            }
        }
    }
    let mut table: BTreeMap<Pc, Vec<Ty>> = BTreeMap::new();
    // Loop-header slots guarded on the way into their loop (§10.2).
    let mut hoist: BTreeMap<(Pc, usize), Ty> = BTreeMap::new();
    // Within a run, a block's entry types join every forward edge into it
    // (`Run::pending`), so a run misses only what a loop's back edges
    // bring. Each rerun widens some loop header's entry types, and there
    // are finitely many widenings; the bound is a backstop.
    for _ in 0..256 {
        let mut run = Run::new(&shape, &table, &hoist);
        run.build()?;
        let new_hoists: Vec<((Pc, usize), Ty)> = run
            .hoist_req
            .iter()
            .filter(|(k, _)| !hoist.contains_key(k))
            .map(|(&k, &t)| (k, t))
            .collect();
        if !run.widen && new_hoists.is_empty() {
            let mm = std::mem::take(&mut run.mm);
            let this_out = run.this_out.flatten();
            let sites = run.inline_sites;
            return Ok((mm, run.finish(), this_out, sites));
        }
        let out = std::mem::take(&mut run.out);
        drop(run);
        if !new_hoists.is_empty() {
            // Entry types only widen across runs: a narrower header starts
            // them over (the hoist set only grows, so this terminates).
            hoist.extend(new_hoists);
            table.clear();
            continue;
        }
        for (pc, tys) in out {
            let e = table.entry(pc).or_insert_with(|| tys.clone());
            for (a, b) in e.iter_mut().zip(&tys) {
                *a = a.join(*b);
            }
        }
    }
    Err("BUG: type fixpoint did not converge".into())
}

/// A decoded op.
#[derive(Clone, Copy, Debug)]
struct Op {
    pc: Pc,
    op: JSOp,
}

/// Backward liveness of the frame slots before the operand stack: `this`
/// (always live: the caller's frame), formals, locals and rval, per pc.
fn liveness(script: &Script, nargs: u32, nlocals: u32) -> BTreeMap<Pc, Vec<bool>> {
    let n = (2 + nargs + nlocals) as usize;
    let rval = n - 1;
    let succs = layout::successors(script);
    // Each op's (uses, defs) over slot indices.
    let effect = |pc: Pc, op: JSOp| -> (Option<usize>, Option<usize>) {
        let mut p = script.parser();
        p.advance(usize::try_from(pc.get()).unwrap() + 1)
            .expect("op in range");
        match op {
            JSOp::GetLocal => (
                Some(1 + nargs as usize + p.next_uint24().unwrap() as usize),
                None,
            ),
            JSOp::SetLocal | JSOp::InitLexical => (
                None,
                Some(1 + nargs as usize + p.next_uint24().unwrap() as usize),
            ),
            JSOp::GetArg | JSOp::GetFrameArg => (Some(1 + usize::from(p.next_uint16().unwrap())), None),
            JSOp::SetArg => (None, Some(1 + usize::from(p.next_uint16().unwrap()))),
            JSOp::GetRval | JSOp::RetRval | JSOp::CheckReturn | JSOp::FinalYieldRval => (Some(rval), None),
            JSOp::SetRval => (None, Some(rval)),
            _ => (None, None),
        }
    };
    // Exception edges: an op a catch or finally covers may throw to its
    // handler, which baseline, resumed by an exit, can reach with the
    // frame as the exit wrote it.
    let handlers: Vec<(Pc, u32, Pc)> = script
        .try_notes
        .iter()
        .filter(|t| matches!(t.kind, crate::bytecode::TryNoteKind::Catch | crate::bytecode::TryNoteKind::Finally))
        .map(|t| (t.start, t.length, t.start + t.length))
        .collect();
    let mut live: BTreeMap<Pc, Vec<bool>> = succs.keys().map(|&pc| (pc, vec![false; n])).collect();
    let pcs: Vec<Pc> = succs.keys().copied().rev().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &pc in &pcs {
            let (op, ss) = &succs[&pc];
            let mut l = vec![false; n];
            let exc = handlers
                .iter()
                .filter(|&&(start, len, _)| pc >= start && pc < start + len)
                .map(|&(_, _, h)| h);
            for s in ss.iter().copied().chain(exc).collect::<Vec<_>>().iter() {
                if let Some(ls) = live.get(s) {
                    for (a, b) in l.iter_mut().zip(ls) {
                        *a |= *b;
                    }
                }
            }
            let (u, d) = effect(pc, *op);
            if let Some(d) = d.filter(|&d| d < n) {
                l[d] = false;
            }
            if let Some(u) = u.filter(|&u| u < n) {
                l[u] = true;
            }
            l[0] = true;
            if live[&pc] != l {
                live.insert(pc, l);
                changed = true;
            }
        }
    }
    live
}

/// The `Add`/`Sub` ops whose result is consumed, directly on the operand
/// stack within its basic block, only by truncating ops (ToInt32 of it)
/// or by other such adds and subs. A sum of int32s, and of such sums, is
/// exact as a double well within 2^53, and ToInt32 of it is the sum
/// modulo 2^32: the int32 wrapping add. (Not `Mul`: a double product can
/// round, which is what `Math.imul` is for.)
fn int32_demand(script: &Script, ops: &[Op]) -> std::collections::BTreeSet<Pc> {
    use std::collections::{BTreeMap, BTreeSet};
    let leaders = layout::leaders(script);
    // Per producer pc: its consumers' pcs, or `None` for a use the model
    // does not follow (a stack shuffle, a block boundary, a second use).
    let mut consumers: BTreeMap<Pc, Vec<Option<Pc>>> = BTreeMap::new();
    let mut stack: Vec<Option<Pc>> = vec![];
    for o in ops {
        if leaders.contains(&o.pc) {
            for p in stack.drain(..).flatten() {
                consumers.entry(p).or_default().push(None);
            }
        }
        let (Some(nuses), ndefs) = (o.op.nuses(), o.op.ndefs()) else {
            for p in stack.drain(..).flatten() {
                consumers.entry(p).or_default().push(None);
            }
            continue;
        };
        let nuses = nuses as usize;
        let simple = !matches!(
            o.op,
            JSOp::Dup | JSOp::Dup2 | JSOp::DupAt | JSOp::Swap | JSOp::Pick | JSOp::Unpick
        );
        if stack.len() < nuses {
            // Entered mid-stack (after a leader): the unknown values below.
            let missing = nuses - stack.len();
            stack.splice(0..0, std::iter::repeat_n(None, missing));
        }
        for p in stack.drain(stack.len() - nuses..).flatten() {
            consumers
                .entry(p)
                .or_default()
                .push(if simple { Some(o.pc) } else { None });
        }
        for _ in 0..ndefs {
            stack.push(if ndefs == 1 && simple {
                Some(o.pc)
            } else {
                None
            });
        }
    }
    for p in stack.drain(..).flatten() {
        consumers.entry(p).or_default().push(None);
    }
    let op_at: BTreeMap<Pc, JSOp> = ops.iter().map(|o| (o.pc, o.op)).collect();
    let truncating = |op: JSOp| {
        matches!(
            op,
            JSOp::BitOr
                | JSOp::BitAnd
                | JSOp::BitXor
                | JSOp::Lsh
                | JSOp::Rsh
                | JSOp::Ursh
                | JSOp::BitNot
        )
    };
    let mut ok: BTreeSet<Pc> = BTreeSet::new();
    // Consumers come after producers: walk backward so a consuming add's
    // verdict is known first.
    for o in ops.iter().rev() {
        if !matches!(o.op, JSOp::Add | JSOp::Sub) {
            continue;
        }
        let Some(cs) = consumers.get(&o.pc) else {
            continue;
        };
        let all = !cs.is_empty()
            && cs.iter().all(|c| match c {
                Some(c) => truncating(op_at[c]) || ok.contains(c),
                None => false,
            });
        if all {
            ok.insert(o.pc);
        }
    }
    ok
}

/// What the runs share: the script's decoded shape.
/// A callee build's context (`callee_in`): the script, the known closures
/// its formals receive, and the constructing `this` it receives, if any.
type CalleeKey = (ScriptId, Vec<Option<ScriptId>>, Option<(u32, u32, bool)>, InlineCtx);

/// Where a callee is built for inlining (bbv's segment context): its
/// depth, the sites it may splice itself, whether the root call site is
/// in a loop (which sets the depth cap), and the loop nest around it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct InlineCtx {
    depth: u32,
    budget: u32,
    root_in_loop: Option<bool>,
    outer_nest: u32,
    /// The call site entering a callee whose forward sites the analysis
    /// resolves per entry (`apply_targets_in`: a shared wrapper's
    /// `this.initialize.apply(this, arguments)`), for them; else `None`,
    /// so other callees are built once whatever the site.
    entry: Option<crate::ids::Site>,
}

impl InlineCtx {
    const ROOT: InlineCtx = InlineCtx {
        depth: 0,
        budget: MAX_INLINE_SITES,
        root_in_loop: None,
        outer_nest: 0,
        entry: None,
    };
}

struct Shape<'a> {
    ctx: &'a TranslateCtx<'a>,
    sid: ScriptId,
    script: &'a Script,
    nargs: u32,
    nlocals: u32,
    depths: StackDepths,
    ops: Vec<Op>,
    leaders: std::collections::BTreeSet<Pc>,
    /// Loop intervals `[header, end)`.
    loops: BTreeMap<Pc, Pc>,
    /// Per pc, which of the frame's first `frame_len` slots (`this`,
    /// formals, locals, rval) are live on entry to the op there: read
    /// before they are next written, on some path.
    live: BTreeMap<Pc, Vec<bool>>,
    /// The `Add`/`Sub` ops whose result only ever reaches ToInt32 (`|`,
    /// `&`, `^`, shifts, or another such add or sub): their int32 form can
    /// wrap instead of checking for overflow (§10.6's numeric demand).
    wrap_ok: std::collections::BTreeSet<Pc>,
    /// Per gcthing index naming a fused global: its fuse and literal.
    fused: BTreeMap<u32, crate::wasm::translate::FusedGname>,
    /// Per gcthing index naming a global: the analysis's likely type
    /// (`gname_types`), guarded at the def.
    gname_types: BTreeMap<u32, crate::facts::Claim>,
    /// Per gcthing index naming a syntactic global: its binding row
    /// (`syn_gnames`), for `check.binding`/`load_gname`/`store_gname`.
    syn_bids: BTreeMap<u32, u32>,
    names: Option<&'a crate::ids::Names>,
    /// The `T.apply(this, arguments)` sites whose arguments object is
    /// never observed (bbv's `compute_apply_fwd_pcs`), if the script has
    /// them.
    apply_fwd: Option<rustc_hash::FxHashSet<Pc>>,
    /// How deep in inlining this build is (0: a script's own).
    inline_depth: u32,
    /// Where this build is inlined (`InlineCtx::ROOT` for a script's own).
    ictx: InlineCtx,
    /// Callees built for inlining, by script; `None` if one cannot be.
    callees: std::cell::RefCell<BTreeMap<CalleeKey, Option<std::rc::Rc<super::inline::Callee>>>>,
    /// For a build for inlining at a call passing known closures: the
    /// formals holding one (`Ty::Fn`), by formal.
    formal_fns: Vec<Option<ScriptId>>,
    /// The object under construction the inlining call passes as `this`
    /// (`Ty::Ctor`: layout key, fields added, TYPES): the body is built
    /// for it, with no entry guard, as a context-sensitive callee build.
    this_ctor: Option<(u32, u32, bool)>,
    /// `name_classes`, by name, made on first use.
    #[allow(clippy::type_complexity)]
    name_classes: std::cell::RefCell<BTreeMap<crate::ids::NameId, std::rc::Rc<Vec<(u32, TagSet)>>>>,
    /// The layout rows' fields, by layout (`layout_field`), made on first
    /// use.
    #[allow(clippy::type_complexity)]
    layout_fields: std::cell::RefCell<Option<BTreeMap<u32, BTreeMap<crate::ids::NameId, (u32, crate::facts::Claim)>>>>,
}

impl<'a> Shape<'a> {
    fn of(
        ctx: &'a TranslateCtx<'a>,
        sid: ScriptId,
        script: &'a Script,
        fl: FrameLayout,
        depths: StackDepths,
    ) -> R<Shape<'a>> {
        let mut ops = vec![];
        let len = script.bytecode.len();
        let mut p = script.parser();
        loop {
            let pc = Pc::new(u32::try_from(len - p.remaining()).unwrap());
            let Some(op) = p.next_op() else { break };
            ops.push(Op { pc, op });
            let imm = usize::try_from(op.len()).unwrap() - 1;
            if imm > 0 && p.advance(imm).is_none() {
                return Err(format!("truncated {op:?} at {pc}"));
            }
        }
        let loops = crate::wasm::translate::scan_loop_intervals(script)
            .into_iter()
            .map(|(h, e)| (Pc::new(h), Pc::new(e)))
            .collect();
        let live = liveness(script, fl.nargs, fl.nlocals);
        let wrap_ok = int32_demand(script, &ops);
        Ok(Shape {
            ctx,
            sid,
            script,
            nargs: fl.nargs,
            nlocals: fl.nlocals,
            depths,
            ops,
            leaders: layout::leaders(script),
            loops,
            live,
            wrap_ok,
            fused: BTreeMap::new(),
            gname_types: BTreeMap::new(),
            syn_bids: BTreeMap::new(),
            names: None,
            apply_fwd: None,
            inline_depth: 0,
            ictx: InlineCtx::ROOT,
            callees: Default::default(),
            formal_fns: vec![],
            this_ctor: None,
            name_classes: Default::default(),
            layout_fields: Default::default(),
        })
    }

    /// The op at `pc`, if one starts there.
    fn op_at(&self, pc: Pc) -> Option<JSOp> {
        let i = self.ops.binary_search_by_key(&pc, |o| o.pc).ok()?;
        Some(self.ops[i].op)
    }

    /// A parser positioned just after the opcode at `pc`.
    fn imms(&self, pc: Pc) -> BytecodeParser<'a> {
        let mut p = self.script.parser();
        p.advance(usize::try_from(pc.get()).unwrap() + 1)
            .expect("op in range");
        p
    }

    /// Whether the op after the one at `pc` consumes its result as
    /// `typeof` does (a name lookup then does not throw when unbound).
    fn next_is_typeof(&self, pc: Pc, op: JSOp) -> bool {
        let next = usize::try_from((pc + op.len()).get()).unwrap();
        self.script
            .bytecode
            .get(next)
            .and_then(|&b| JSOp::from_byte(b))
            .is_some_and(|o| matches!(o, JSOp::Typeof | JSOp::TypeofEq | JSOp::TypeofExpr))
    }

    /// The entry type the analysis predicts for formal `i` (guard-at-defs).
    /// A formal some call leaves out takes none: its `undefined` would
    /// fail the entry guard on every such call.
    fn arg_claim(&self, i: u32) -> Ty {
        if self.ctx.facts.omitted_formals.contains(&(self.sid, i)) {
            return Ty::Val(TagSet::ALL);
        }
        let claim = self
            .ctx
            .facts
            .arg_types
            .get(&(self.sid, ArgIndex::new(i + 1)))
            .copied()
            .unwrap_or(Claim::NONE);
        num_claim_ty(claim, true).unwrap_or(Ty::Val(TagSet::ALL))
    }
}

/// One run of the builder over the script.
struct Run<'s, 'a> {
    s: &'s Shape<'a>,
    table: &'s BTreeMap<Pc, Vec<Ty>>,
    /// Loop-header slots this run guards on the way into their loop, to
    /// their narrow type (`Native`, `Ta`).
    hoist: &'s BTreeMap<(Pc, usize), Ty>,
    /// Loop-header slots whose back edges bring a narrow object type where
    /// the header has a `Val`: guarded on entry in the next run.
    hoist_req: BTreeMap<(Pc, usize), Ty>,
    /// The types flowing into each block this run (joined).
    out: BTreeMap<Pc, Vec<Ty>>,
    f: mir::Func,
    /// The module tables the function references (its atoms).
    mm: mir::Module,
    blocks: BTreeMap<Pc, mir::Block>,
    preheaders: BTreeMap<Pc, mir::Block>,
    /// The entry types of every block entered so far this run.
    entry_types: BTreeMap<Pc, Vec<Ty>>,
    /// Edges to blocks not entered yet: a trampoline block per edge, with
    /// the frame's types there and the edge's source pc. Entering the
    /// block joins them into its entry types, then fills each trampoline
    /// with the conversions and the jump.
    pending: BTreeMap<Pc, Vec<(mir::Block, Vec<Ty>, Option<Pc>)>>,
    /// Whether a back edge brought types wider than its loop header's: the
    /// run is not the last.
    widen: bool,
    cur: mir::Block,
    /// Whether `cur` is open.
    live: bool,
    /// The frame: `this`, formals, locals, rval, then the operand stack.
    st: Vec<Slot>,
    /// The value standing for the elided arguments object at an apply
    /// forward site (`apply_forward`), if `Arguments` has run.
    args_placeholder: Option<mir::Value>,
    /// The local the placeholder was stored into (the `arguments` binding,
    /// written once: `compute_apply_fwd_pcs`); tracked by slot, since
    /// block params rename the value.
    args_local: Option<usize>,
    /// The op being built, its state before it, and its shared exit and
    /// throw blocks.
    pc: Pc,
    pre: Vec<Slot>,
    exit_blk: Option<mir::Block>,
    throw_blk: Option<mir::Block>,
    /// Call sites this run has inlined into (`MAX_INLINE_SITES`), and the
    /// callee instructions they spliced (`MAX_INLINE_TOTAL_INSTS`).
    inline_sites: u32,
    /// The context the last admitted site's callees were built in.
    admitted: InlineCtx,
    /// This op's fence renamings of `Obj` values (`fence_params`), for
    /// `repush`.
    renames: Vec<(mir::Value, Slot)>,
    /// The pc after the op being built (`js_keep`'s exits).
    next_pc: Option<Pc>,
    /// The likely callees the next generic `call` gets (`attach_targets`).
    likely_targets: Vec<ScriptId>,
    /// Values read from a global by name, and the Math functions read off
    /// `Math` (`math_call`).
    gname_vals: BTreeMap<mir::Value, mir::entity::AtomId>,
    math_fns: BTreeMap<mir::Value, MathFn>,
    /// The element op being built is at an `elem_poly_sites` site.
    ta_poly_site: bool,
    /// The predicted type of the field the property store being built
    /// writes, for its TYPES maintenance (`field_mask` attachments).
    store_mask: Option<(Vec<(u32, TagSet)>, bool)>,
    /// Advisory classes (`hinted_site`): of values, and of the frame
    /// slots whose writes carry them.
    val_cls: BTreeMap<mir::Value, u32>,
    /// Boxed objects known to have been under construction for a layout
    /// (key, fields added, TYPES) when a fence demoted them from `Ctor`
    /// (§2.3), or as an inlined callee left them: a field add or a method
    /// call through one guards the construction state again
    /// (`guard.ctor`), and continues typed.
    ctor_hint: BTreeMap<mir::Value, (u32, u32, bool)>,
    /// Each constructed layout's fields and claims, registered in the
    /// module (`ctor_layout`); `None` where the table cannot hold them.
    ctor_layouts: BTreeMap<u32, Option<std::rc::Rc<Vec<(mir::entity::AtomId, MType)>>>>,
    /// The state `this` (a `Ctor`) is in at every return seen so far
    /// (`Callee::this_out`): `None` before the first, `Some(None)` once
    /// two disagree or one is anything else.
    this_out: Option<Option<(u32, u32, bool)>>,
    slot_cls: BTreeMap<usize, u32>,
    /// Values that are the frame's `this` (`FunctionThis`'s results),
    /// and the frame slots a write carries that to (`.this`).
    this_vals: std::collections::BTreeSet<mir::Value>,
    this_slots: std::collections::BTreeSet<usize>,
}

impl<'s, 'a> Run<'s, 'a> {
    fn new(
        s: &'s Shape<'a>,
        table: &'s BTreeMap<Pc, Vec<Ty>>,
        hoist: &'s BTreeMap<(Pc, usize), Ty>,
    ) -> Run<'s, 'a> {
        let frame = FrameShape {
            formals: s.nargs,
            locals: s.nlocals,
            depths: BTreeMap::new(),
        };
        let mut f = mir::Func::new(s.sid, frame);
        let cur = f.add_block();
        Run {
            s,
            table,
            hoist,
            hoist_req: BTreeMap::new(),
            out: BTreeMap::new(),
            f,
            mm: mir::Module {
                array_key_min: s.ctx.array_stamp_in.values().map(|&w| w & 0xFFFF).min(),
                ..mir::Module::default()
            },
            blocks: BTreeMap::new(),
            preheaders: BTreeMap::new(),
            entry_types: BTreeMap::new(),
            pending: BTreeMap::new(),
            widen: false,
            cur,
            live: true,
            st: vec![],
            args_placeholder: None,
            args_local: None,
            pc: Pc::new(0),
            pre: vec![],
            exit_blk: None,
            throw_blk: None,
            renames: vec![],
            next_pc: None,
            likely_targets: vec![],
            gname_vals: BTreeMap::new(),
            math_fns: BTreeMap::new(),
            ta_poly_site: false,
            store_mask: None,
            val_cls: BTreeMap::new(),
            ctor_hint: BTreeMap::new(),
            ctor_layouts: BTreeMap::new(),
            this_out: None,
            slot_cls: BTreeMap::new(),
            this_vals: Default::default(),
            this_slots: Default::default(),
            inline_sites: 0,
            admitted: InlineCtx::ROOT,
        }
    }

    fn finish(mut self) -> mir::Func {
        // Drop blocks nothing reaches (a run creates a block for every
        // leader with an entry type, and some are only reached from blocks
        // that turned out dead).
        let mut seen = std::collections::BTreeSet::new();
        let mut work: Vec<mir::Block> = self.f.roots.iter().map(|r| r.block).collect();
        while let Some(b) = work.pop() {
            if seen.insert(b) {
                work.extend(self.f.succs(b));
            }
        }
        self.f.layout.retain(|b| seen.contains(b));
        self.f.loops.retain(|l| seen.contains(&l.header));
        self.f
    }

    // --- emission ------------------------------------------------------------

    fn inst(&mut self, op: Opcode, args: Vec<mir::Value>, result: Option<MType>) -> mir::Value {
        self.retain_locals(&op);
        let tys: Vec<MType> = result.into_iter().collect();
        let (_, rs) = self.f.add_inst(self.cur, op, args, &tys, vec![]);
        rs.first()
            .copied()
            .unwrap_or_else(|| mir::Value::from_u32(0))
    }

    fn term(&mut self, op: Opcode, args: Vec<mir::Value>, mut succs: Vec<Edge>) {
        self.retain_locals(&op);
        self.fence_params(&op, &args, &mut succs);
        let (inst, _) = self.f.add_inst(self.cur, op, args, &[], succs);
        self.attach_targets(inst);
        self.live = false;
    }

    /// Give a generic `call` the site's likely callees (`likely_targets`),
    /// for its lowering's direct arms.
    fn attach_targets(&mut self, inst: mir::Inst) {
        if let Some((classes, complete)) = self.store_mask.clone() {
            if matches!(self.f.insts[inst].op, Opcode::StoreField(_) | Opcode::JsSetProp(..)) {
                let a = self.f.attachments.push(mir::func::Attachment {
                    site: Some(self.site(self.pc)),
                    field_types: classes.iter().map(|&(k, t)| (k, mir::func::encode_tags(t))).collect(),
                    field_types_complete: complete,
                    ..Default::default()
                });
                self.f.insts[inst].attach = Some(a);
                return;
            }
        }
        if self.ta_poly_site && matches!(self.f.insts[inst].op, Opcode::JsGetElem | Opcode::JsSetElem(..)) {
            let a = self.f.attachments.push(mir::func::Attachment {
                site: Some(self.site(self.pc)),
                ta_poly: true,
                ..Default::default()
            });
            self.f.insts[inst].attach = Some(a);
            return;
        }
        if self.f.insts[inst].op != Opcode::Call || self.likely_targets.is_empty() {
            return;
        }
        let targets = std::mem::take(&mut self.likely_targets);
        let a = self.f.attachments.push(mir::func::Attachment {
            site: Some(self.site(self.pc)),
            ic_cell: None,
            call_cell: None,
            slot: None,
            field_types: vec![],
            field_types_complete: false,
            targets,
            ta_poly: false,
        });
        self.f.insts[inst].attach = Some(a);
    }

    /// A terminator that may change what an `Obj` slot proves (a call, a
    /// generic op: it kills layout claims on an edge the build continues
    /// on) weakens each such slot's value to `obj` first, in the current
    /// block (§5's fence rule), and the slot continues as `ObjHint`.
    /// Operands the op popped are renamed the same way (`repush`). Throw
    /// exits need nothing: they only box.
    fn fence_params(&mut self, op: &Opcode, args: &[mir::Value], succs: &mut [Edge]) {
        let _ = succs;
        let tys: Vec<MType> = args.iter().map(|&v| self.f.ty(v)).collect();
        let fx = mir::ops::effects(op, &tys, &self.mm);
        if !matches!(
            op.kill_site(&fx),
            mir::ops::KillSite::OkEdge | mir::ops::KillSite::DirtyEdge
        ) {
            return;
        }
        let mut done: Vec<(mir::Value, Slot)> = vec![];
        let olds: Vec<Slot> = self.st.iter().chain(&self.pre).copied().collect();
        for x in olds {
            if !matches!(x.ty, Ty::Obj(..) | Ty::Ctor(..))
                || !fx.kill.matches(&x.ty.mir())
                || done.iter().any(|&(v, _)| v == x.v)
            {
                continue;
            }
            let y = self.demote(x);
            done.push((x.v, y));
        }
        if done.is_empty() {
            return;
        }
        for (v, y) in done {
            for x in self.st.iter_mut().chain(self.pre.iter_mut()).filter(|x| x.v == v) {
                *x = y;
            }
            self.renames.push((v, y));
        }
        // An exit at this op's pc made before the fence may be reached
        // after it: the next one is made from the renamed state.
        self.exit_blk = None;
    }

    /// Push `x`, an operand this op popped, back: as its fence renamed it,
    /// if one did (`fence_params`).
    /// `recv.length` as a typed op (§7 `length.{string,array}`), pushing
    /// the int32 it is: a proven string's length word; for a receiver the
    /// builder has evidence is an array (a native object its element
    /// accesses guarded, or an array layout's value class), its elements
    /// header's, guarded to an array and to int32 (a miss exits). False,
    /// with nothing emitted, for anything else (the generic read, whose
    /// lowering tests the same cases at run time).
    fn length_op(&mut self, recv: Slot) -> bool {
        if let Ty::Val(t) = recv.ty {
            if t.is_nonempty_subset_of(TagSet::STRING) {
                let s = self.inst(Opcode::Unbox(UnboxKind::Str), vec![recv.v], Some(MType::STR_TOP));
                let n = self.inst(Opcode::LengthString, vec![s], Some(MType::i32_range(0, (1 << 30) - 2)));
                self.push(n, Ty::I32);
                return true;
            }
        }
        let array_cls = |k: u32| self.mm.array_key_min.is_some_and(|min| k + 1 >= min);
        let evidence = recv.ty == Ty::Native || self.val_cls.get(&recv.v).is_some_and(|&k| array_cls(k));
        if !LENGTH_ARRAY || !evidence || !TagSet::OBJECT.subset_of(recv.ty.tags()) {
            return false;
        }
        let o = match recv.ty {
            Ty::Native | Ty::Obj(..) | Ty::ObjHint(_) | Ty::Ctor(..) => recv.v,
            Ty::Val(_) => self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![recv.v], MType::OBJ_TOP),
            _ => return false,
        };
        let arr = MType::Obj(ObjInfo::kind(ObjKind::Array));
        let o = self.guard(Opcode::GuardKind(ObjKind::Array), vec![o], arr);
        let len = self.inst(Opcode::LengthArray, vec![o], Some(MType::int_range(0, u32::MAX.into())));
        let n = self.guard(Opcode::IntToI32, vec![len], MType::i32_range(0, i64::from(i32::MAX)));
        self.push(n, Ty::I32);
        true
    }

    /// The module's binding for syntactic global `name` (row `slot`),
    /// declared on first use.
    fn binding(&mut self, name: mir::entity::AtomId, slot: u32) -> mir::entity::BindingId {
        if let Some((b, _)) = self.mm.bindings.iter().find(|(_, d)| d.slot == slot) {
            return b;
        }
        self.mm.bindings.push(mir::module::BindingDef {
            name,
            claim: MType::VAL_TOP,
            slot,
        })
    }

    /// The constant `v` is, if it is an `i32` constant.
    fn const_i32_of(&self, v: mir::Value) -> Option<i32> {
        match self.f.values[v].def {
            mir::func::ValueDef::Result(i, _) => match self.f.insts[i].op {
                Opcode::ConstI32(n) => Some(n),
                _ => None,
            },
            _ => None,
        }
    }

    fn repush(&mut self, x: Slot) {
        let y = self
            .renames
            .iter()
            .rev()
            .find(|(v, _)| *v == x.v)
            .map_or(x, |&(_, y)| y);
        self.st.push(y);
    }

    /// `x`, as `ObjHint` if it is an `Obj`; boxed if it is a `Ctor` (an
    /// object under construction that a fence may have reached: its state
    /// is unknown, and a published-layout hint would be wrong).
    fn demote(&mut self, x: Slot) -> Slot {
        match x.ty {
            Ty::Obj(k, ..) => Slot {
                v: self.weaken(x.v, MType::OBJ_TOP),
                ty: Ty::ObjHint(k),
            },
            Ty::Ctor(k, n, t) => {
                let v = self.boxed(x);
                self.ctor_hint.insert(v, (k, n, t));
                Slot {
                    v,
                    ty: Ty::Val(TagSet::OBJECT),
                }
            }
            _ => x,
        }
    }

    /// bbv's inlining admission (`Bbv::inline_candidates_for`, with its
    /// per-target rules): which of `sids` the site at `self.pc` inlines,
    /// each built by `build` where the site puts it, in order; `None` for
    /// none. Counts the site, and the sites its callees splice, against
    /// this function's budget.
    fn admit(
        &mut self,
        sids: &[ScriptId],
        construct: bool,
        build: &dyn Fn(&Shape<'a>, ScriptId, InlineCtx) -> Option<std::rc::Rc<super::inline::Callee>>,
    ) -> Option<Vec<(ScriptId, std::rc::Rc<super::inline::Callee>)>> {
        use crate::bytecode::TryNoteKind;
        let s = self.s;
        let pc = self.pc;
        let ictx = s.ictx;
        if sids.is_empty() {
            return None;
        }
        let local_nest = u32::try_from(s.loops.iter().filter(|(&h, &e)| h <= pc && pc < e).count()).unwrap();
        let root_in_loop = ictx.root_in_loop.unwrap_or(local_nest > 0);
        let max_depth = if root_in_loop { MAX_INLINE_DEPTH_LOOP } else { MAX_INLINE_DEPTH };
        if ictx.depth >= max_depth {
            return None;
        }
        let script = s.script;
        // bbv's rule (no splicing into a function that uses `arguments`,
        // mapped formals or actuals), except where `arguments` only feeds
        // `T.apply(this, arguments)` forwards (`apply_fwd`, never made):
        // the frame's actuals are read in place, whatever is spliced.
        let needs_args_obj = (crate::wasm::translate::uses_arguments(script) && s.apply_fwd.is_none())
            || (script.has_mapped_args && script.nargs > 0)
            || crate::wasm::translate::uses_actual_args(script);
        if needs_args_obj || self.inline_sites >= ictx.budget {
            return None;
        }
        let bytes = |k: ScriptId| match s.ctx.source.object(crate::source::SourceObjectId::new(k.get())) {
            crate::source::SourceObject::Script(ks) => Some(ks),
            _ => None,
        };
        let n = self.f.insts.len();
        if n >= SPLICE_FUEL_INSTS {
            let small = sids.iter().all(|&k| bytes(k).is_some_and(|ks| ks.bytecode.len() <= SMALL_SPLICE_BC));
            if !small || n >= SMALL_SPLICE_FUEL_INSTS {
                return None;
            }
        }
        if script
            .try_notes
            .iter()
            .any(|t| !matches!(t.kind, TryNoteKind::Loop) && pc >= t.start && pc < t.start + t.length)
        {
            return None;
        }
        if sids.len() > MAX_INLINE_TARGETS {
            return None;
        }
        let cap = match (sids.len(), root_in_loop) {
            (1, true) => 200,
            (1, false) => 150,
            _ => crate::constants::MAX_INLINE_POLY_BYTES,
        };
        let nest = ictx.outer_nest + local_nest;
        let allow_callee_loops = nest == 0;
        let picked: Vec<ScriptId> = sids
            .iter()
            .copied()
            .filter(|&k| {
                let Some(ks) = bytes(k) else { return false };
                !ks.bytecode.is_empty()
                    && ks.bytecode.len() <= cap
                    && !(construct && ks.is_class_ctor)
                    && !(!construct && ks.is_class_ctor)
                    && (allow_callee_loops || !ks.try_notes.iter().any(|t| t.kind == TryNoteKind::Loop))
            })
            .collect();
        if picked.is_empty() {
            return None;
        }
        if construct {
            if picked.len() != 1 {
                return None;
            }
            let room = crate::constants::CONSTRUCT_CLOSURE_CAP;
            let est = crate::wasm::bbv::splice_closure_cost(s.ctx, picked[0], max_depth - ictx.depth, room, Some(self.site(pc)));
            if est > room {
                return None;
            }
        }
        // Depth-first, as bbv's walk: each target is a spliced segment,
        // and may splice what the budget has left once it and the
        // segments before it count (bbv checks the budget per site, then
        // splices every target it picked).
        let mut used = self.inline_sites;
        let mut out = vec![];
        let mut admitted = None;
        for k in picked {
            let site = self.site(pc);
            let per_entry = bytes(k).is_some_and(layout::reads_actuals)
                && s.ctx.facts.apply_targets_in.keys().any(|&(e, a)| e == site && a.script == k);
            let at = InlineCtx {
                depth: ictx.depth + 1,
                budget: ictx.budget.saturating_sub(used + 1),
                root_in_loop: Some(root_in_loop),
                outer_nest: nest,
                entry: per_entry.then_some(site),
            };
            if let Some(c) = build(s, k, at) {
                used += 1 + c.sites;
                admitted.get_or_insert(at);
                out.push((k, c));
            }
        }
        if out.is_empty() {
            return None;
        }
        self.admitted = admitted.unwrap();
        self.inline_sites = used;
        Some(out)
    }

    /// At a layout constructor's return, the first stamp of its completed
    /// `this` (a no-op unless `this` is still under construction, so a
    /// call without `new` stamps nothing); an inlined copy stamps too.
    fn ctor_stamp(&mut self) {
        let Some(si) = self.s.ctx.stamp_ctors_in.get(&self.s.sid) else {
            return;
        };
        let op = Opcode::CtorStamp(
            si.layout_id,
            u32::try_from(si.fields.len()).unwrap(),
            crate::wasm::bbv::typed_keep_bits(self.s.ctx, si),
        );
        let t = self.boxed(self.st[0]);
        self.inst(op, vec![t], None);
    }

    /// `publish_layout` at its earliest point (MIR.md §2.3): before a call
    /// made while `this` may be under construction (`ctor_publish`), the
    /// stamp of each constructor whose early key it carries, once all of
    /// that constructor's fields are there. A method it calls on itself
    /// then finds a published object (its entry guard passes, and its
    /// stores keep TYPES), where it would otherwise exit to baseline and
    /// leave the object published without TYPES for good.
    fn publish_this(&mut self) {
        let ctx = self.s.ctx;
        let Some(ctors) = ctx.facts.ctor_publish.get(&self.s.sid) else {
            return;
        };
        let Some(&x) = self.st.first() else { return };
        if matches!(x.ty, Ty::Dead | Ty::Obj(..) | Ty::ObjHint(..) | Ty::Ctor(..)) {
            return;
        }
        let t = self.boxed(x);
        for c in ctors {
            let Some(si) = ctx.stamp_ctors_in.get(c) else { continue };
            let op = Opcode::CtorPublish(
                si.layout_id,
                u32::try_from(si.fields.len()).unwrap(),
                crate::wasm::bbv::typed_keep_bits(self.s.ctx, si),
            );
            self.inst(op, vec![t], None);
        }
    }

    /// At an init delegate's or a fill script's return, the two-phase
    /// restamp of `this` or the named formal (`deleg_restamps_in`,
    /// `arg_restamps_in`); an inlined copy's returns restamp its own.
    fn return_restamps(&mut self) {
        let ctx = self.s.ctx;
        let sid = self.s.sid;
        if let Some(si) = ctx.deleg_restamps_in.get(&sid) {
            if self.st[0].ty != Ty::Dead {
                let t = self.boxed(self.st[0]);
                self.restamp(si, t);
            }
        }
        if let Some((formal, si)) = ctx.arg_restamps_in.get(&sid) {
            if let Some(v) = self.formal_now(*formal) {
                self.restamp(si, v);
            }
        }
    }

    /// After the last add of a post-construction fill sequence
    /// (`local_restamps_in`), the restamp of the named local or formal.
    fn local_restamp(&mut self, pc: Pc) {
        let Some((local, si)) = self.s.ctx.local_restamps_in.get(&self.site(pc)) else {
            return;
        };
        let v = if local & crate::facts::RESTAMP_FORMAL != 0 {
            self.formal_now(local & !crate::facts::RESTAMP_FORMAL)
        } else {
            let x = self.st[self.local_ix(*local)];
            (x.ty != Ty::Dead).then(|| self.boxed(x))
        };
        if let Some(v) = v {
            self.restamp(si, v);
        }
    }

    /// Formal `n`'s current value, boxed; `None` if dead here (nothing
    /// reads it, so nothing reads the object through it).
    fn formal_now(&mut self, n: u32) -> Option<mir::Value> {
        if n >= self.s.nargs {
            return None;
        }
        if self.mapped() {
            return Some(self.inst(Opcode::ArgsMapped(n), vec![], Some(MType::VAL_TOP)));
        }
        let x = self.st[self.arg_ix(n)];
        (x.ty != Ty::Dead).then(|| self.boxed(x))
    }

    fn restamp(&mut self, si: &StampCtorIn, v: mir::Value) {
        let Some(r) = crate::wasm::bbv::typed_restamp_args(self.s.ctx, si) else {
            return;
        };
        let i = u32::try_from(self.mm.restamps.len()).unwrap();
        self.mm.restamps.push(r);
        self.inst(Opcode::Restamp(i), vec![v], None);
    }

    /// Whether an element store at `pc` of `v` owes the array stamp's
    /// RANGES and TYPES claims a clear (bbv's `emit_elem_store_duty`): the
    /// site's claim, or the intersection of every claim for a receiver
    /// the analysis did not place, unless `v` is proven an int32 inside it
    /// (an element claim is an int32 range). No claim, no duty.
    fn ranges_duty(&self, pc: Pc, v: Slot) -> bool {
        let ctx = self.s.ctx;
        let claim = ctx.array_elem_in.get(&self.site(pc)).map(|a| a.range).or(ctx.array_any_claim);
        let Some(r) = claim else { return false };
        let inside = |lo: i64, hi: i64| lo >= r.lo && hi <= r.hi;
        let proven = match self.f.ty(v.v) {
            MType::I32(ir) | MType::Int(ir) => inside(ir.lo, ir.hi),
            MType::Val(s) if s.tags.is_nonempty_subset_of(TagSet::INT32) => {
                s.num.range.is_some_and(|x| inside(x.lo, x.hi))
            }
            _ => false,
        };
        !proven
    }

    /// Whether atom `a` is `s`.
    fn atom_is(&self, a: mir::entity::AtomId, s: &str) -> bool {
        self.mm.atoms[a].chars().iter().copied().eq(s.encode_utf16())
    }

    /// `Math.<fn>(args)` of a function with a typed op (`math_fns`), with
    /// `argc` its arity: the callee checked to be the pristine native, the
    /// arguments to be numbers (exiting at the call on a miss: the site
    /// runs in baseline then), and the op on raw f64s, whose result is a
    /// raw f64 rather than a boxed value to guard. False if not such a
    /// call (nothing emitted).
    fn math_call(&mut self, argc: usize) -> bool {
        let n = self.st.len();
        let Some(&m) = self.math_fns.get(&self.st[n - argc - 2].v) else {
            return false;
        };
        if !MATH_CALLS || argc != m.arity() {
            return false;
        }
        let operands: Vec<Slot> = self.st.drain(n - argc - 2..).collect();
        let callee = self.boxed(operands[0]);
        let name = format!("Math.{}", math_fn_name(m));
        let found = self.mm.natives.iter().find(|(_, d)| d.name == name).map(|(id, _)| id);
        let nid = match found {
            Some(id) => id,
            None => self.mm.natives.push(mir::module::NativeDef { name }),
        };
        self.guard(
            Opcode::CheckNative(nid),
            vec![callee],
            MType::Fact(mir::types::FactKind::NativeIntact(nid)),
        );
        let mut args = vec![];
        for x in &operands[2..] {
            let f = if x.ty.num().is_some() {
                self.as_f64(*x)
            } else {
                let b = self.boxed(*x);
                self.guard(Opcode::GuardUnbox(UnboxKind::F64Num), vec![b], MType::F64_TOP)
            };
            args.push(f);
        }
        let r = self.inst(Opcode::Math(m), args, Some(MType::F64_TOP));
        self.push(r, Ty::F64);
        true
    }

    /// Whether the script's formals are its mapped `arguments` object's.
    fn mapped(&self) -> bool {
        self.s.script.has_mapped_args && self.s.nargs > 0
    }

    /// Every `Obj` slot, as `ObjHint`: in the state and in this op's
    /// pre-state (which its exits are made from; exits made before are
    /// dropped, an inlined callee's reaching its caller's through
    /// `exit.inline`), for `repush` too.
    fn demote_objs(&mut self) {
        let mut done: Vec<(mir::Value, Slot)> = vec![];
        let olds: Vec<Slot> = self.st.iter().chain(&self.pre).copied().collect();
        for x in olds {
            if !matches!(x.ty, Ty::Obj(..) | Ty::Ctor(..)) || done.iter().any(|&(v, _)| v == x.v) {
                continue;
            }
            let y = self.demote(x);
            done.push((x.v, y));
        }
        if done.is_empty() {
            return;
        }
        for (v, y) in done {
            for x in self.st.iter_mut().chain(self.pre.iter_mut()).filter(|x| x.v == v) {
                *x = y;
            }
            self.renames.push((v, y));
        }
        self.exit_blk = None;
        self.throw_blk = None;
    }

    fn goto(block: mir::Block) -> Edge {
        Edge {
            block,
            args: vec![],
        }
    }

    fn new_block(&mut self) -> mir::Block {
        self.f.add_block()
    }

    /// Continue in `b` (opened by the caller's terminator).
    fn at(&mut self, b: mir::Block) {
        self.cur = b;
        self.live = true;
    }

    /// Before an op that may GC: write each managed local (formal, local,
    /// rval) to the frame, where the GC sees it. A local's value then stays
    /// alive until the local is overwritten, as in baseline, whose frame
    /// holds it (a `WeakMap` key held only by a dead local must survive);
    /// MIR otherwise roots only what is live. Emitted before every such op:
    /// the lowering writes them only where the op can GC (a slow path, or
    /// the call), and drops a store of what the frame holds on the path.
    fn retain_locals(&mut self, op: &Opcode) {
        use mir::ops::SuccRole;
        let may_gc = op.roles().iter().any(|r| matches!(r, SuccRole::Err | SuccRole::OkDirty));
        if may_gc {
            self.retain_all();
        }
    }

    /// `retain_locals` unconditionally: before an inlined callee, whose
    /// GC points are its own ops.
    fn retain_all(&mut self) {
        for ix in 1..self.frame_len().min(self.st.len()) {
            let x = self.st[ix];
            let managed = matches!(
                x.ty,
                Ty::Val(_) | Ty::Fn(_) | Ty::Obj(..) | Ty::ObjHint(_) | Ty::Ctor(..) | Ty::Native | Ty::Ta(_)
            );
            if !managed {
                continue;
            }
            self.f.add_inst(self.cur, Opcode::FrameStore(u32::try_from(ix).unwrap()), vec![x.v], &[], vec![]);
        }
    }

    fn const_val(&mut self, c: ConstVal) -> mir::Value {
        let t = mir::ops::const_val_type(c);
        self.inst(Opcode::ConstVal(c), vec![], Some(t))
    }

    fn const_i32(&mut self, n: i32) -> mir::Value {
        let t = MType::i32_range(n.into(), n.into());
        self.inst(Opcode::ConstI32(n), vec![], Some(t))
    }

    fn const_f64(&mut self, x: f64) -> mir::Value {
        let t = MType::F64(mir::types::NumInfo::exact(x));
        self.inst(Opcode::ConstF64(x.to_bits()), vec![], Some(t))
    }

    fn weaken(&mut self, v: mir::Value, t: MType) -> mir::Value {
        if self.f.ty(v) == t {
            return v;
        }
        self.inst(Opcode::Weaken, vec![v], Some(t))
    }

    /// `x` as a boxed value, of type `Val(x.ty.tags())`.
    fn boxed(&mut self, x: Slot) -> mir::Value {
        let v = match x.ty {
            Ty::Val(_) | Ty::Fn(_) => return x.v,
            _ => {
                let t = mir::ops::box_type(&self.f.ty(x.v)).expect("raw values box");
                self.inst(Opcode::Box, vec![x.v], Some(t))
            }
        };
        self.weaken(v, MType::val(x.ty.tags()))
    }

    /// `x` converted to type `to`, which it fits.
    fn convert(&mut self, x: Slot, to: Ty) -> mir::Value {
        match (x.ty, to) {
            (a, b) if a == b => x.v,
            (Ty::I32, Ty::F64) => self.inst(Opcode::I32ToF64, vec![x.v], Some(MType::F64_TOP)),
            (Ty::Obj(..), Ty::Obj(..) | Ty::ObjHint(_))
            | (Ty::ObjHint(_), Ty::ObjHint(_))
            | (Ty::Ctor(..), Ty::Ctor(..)) => self.weaken(x.v, to.mir()),
            (_, Ty::Val(t)) => {
                let v = self.boxed(x);
                self.weaken(v, MType::val(t))
            }
            (a, b) => unreachable!("convert {a:?} to {b:?}"),
        }
    }

    fn as_i32(&mut self, x: Slot) -> mir::Value {
        match x.ty {
            Ty::I32 => x.v,
            Ty::Val(_) => self.inst(
                Opcode::Unbox(UnboxKind::I32),
                vec![x.v],
                Some(MType::I32_TOP),
            ),
            t => unreachable!("as_i32 {t:?}"),
        }
    }

    fn as_f64(&mut self, x: Slot) -> mir::Value {
        match x.ty {
            Ty::F64 => x.v,
            Ty::I32 => self.inst(Opcode::I32ToF64, vec![x.v], Some(MType::F64_TOP)),
            Ty::Val(_) => self.inst(
                Opcode::Unbox(UnboxKind::F64Num),
                vec![x.v],
                Some(MType::F64_TOP),
            ),
            t => unreachable!("as_f64 {t:?}"),
        }
    }

    /// A number as an int32, by ToInt32.
    fn to_int32(&mut self, x: Slot) -> mir::Value {
        match x.ty.num() {
            Some(Num::I32) => self.as_i32(x),
            _ => {
                let f = self.as_f64(x);
                self.inst(Opcode::ToInt32, vec![f], Some(MType::I32_TOP))
            }
        }
    }

    // --- exits ---------------------------------------------------------------

    /// The frame `st` as exit operands at `pc`, all `Val(⊤)`, recording the
    /// stack depth there.
    fn exit_operands(&mut self, pc: Pc, st: &[Slot]) -> Vec<mir::Value> {
        // Baseline has no elided arguments object: an exit whose state
        // holds the placeholder makes the real one first (into the frame
        // slots that hold it, and in the operands), at the exit's own cost.
        let mut st = st.to_vec();
        let ph = self.args_placeholder;
        let holds = |i: usize, x: &Slot| Some(x.v) == ph || Some(i) == self.args_local;
        if ph.is_some() && st.iter().enumerate().any(|(i, x)| holds(i, x)) {
            let ok = self.new_block();
            let obj = self.f.add_param(ok, MType::val(TagSet::OBJECT));
            let err = self.new_block();
            // Retained as the exit has them (a dirty exit's are weakened).
            let live = std::mem::replace(&mut self.st, st.clone());
            self.retain_locals(&Opcode::ArgsObject);
            self.st = live;
            let (t, _) = self.f.add_inst(
                self.cur,
                Opcode::ArgsObject,
                vec![],
                &[],
                vec![
                    Edge {
                        block: ok,
                        args: vec![EdgeArg::Out(0)],
                    },
                    Self::goto(err),
                ],
            );
            self.f.witnesses[t] = Some(mir::func::Witness {
                may_kill: mir::types::KillPattern::ALL,
            });
            // Out of memory making it: throw with the state as it is.
            self.at(err);
            let saved = self.args_placeholder.take();
            let ops = self.exit_operands(pc, &st);
            let eop = self.exit_op(pc, true);
            self.term(eop, ops, vec![]);
            self.args_placeholder = saved;
            self.at(ok);
            for (i, x) in st.iter_mut().enumerate() {
                if Some(x.v) == ph || Some(i) == self.args_local {
                    if self.write_through(i) {
                        self.inst(Opcode::FrameStore(u32::try_from(i).unwrap()), vec![obj], None);
                    }
                    *x = Slot {
                        v: obj,
                        ty: Ty::Val(TagSet::OBJECT),
                    };
                }
            }
        }
        let st = &st[..];
        let depth = st.len() - self.frame_len();
        self.f
            .frame
            .depths
            .insert(pc, u32::try_from(depth).unwrap());
        // A slot dead at the exit's pc goes as `const.val dead`: baseline
        // never reads it before writing it, so the frame keeps whatever
        // (valid) value it has.
        let live = self.s.live.get(&pc).cloned();
        let mut dead = None;
        let mut ops = vec![];
        for (i, &x) in st.iter().enumerate() {
            // A written-through slot is already in the frame.
            let in_frame = self.write_through(i);
            let is_dead = in_frame
                || x.ty == Ty::Dead
                || live.as_ref().is_some_and(|l| i < l.len() && !l[i]);
            if is_dead {
                let d = *dead.get_or_insert_with(|| self.const_val(ConstVal::Dead));
                ops.push(d);
            } else {
                // As it is: the lowering boxes it at the exit hub.
                ops.push(x.v);
            }
        }
        ops
    }

    fn exit_op(&self, pc: Pc, throw: bool) -> Opcode {
        let (nargs, nlocals) = (self.s.nargs, self.s.nlocals);
        if throw {
            Opcode::ExitThrow { pc, nargs, nlocals }
        } else {
            Opcode::Exit { pc, nargs, nlocals }
        }
    }

    /// The op's shared exit (or throw) block: the state before the op.
    fn exit_block(&mut self, throw: bool) -> mir::Block {
        let slot = if throw { self.throw_blk } else { self.exit_blk };
        if let Some(b) = slot {
            return b;
        }
        let saved = (self.cur, self.live);
        let b = self.new_block();
        self.at(b);
        let pre = self.pre.clone();
        let ops = if throw && self.s.throws_uncaught() {
            // Baseline's landing for it only returns the error: no state.
            self.f
                .frame
                .depths
                .insert(self.pc, u32::try_from(pre.len() - self.frame_len()).unwrap());
            let d = self.const_val(ConstVal::Dead);
            vec![d; pre.len()]
        } else {
            self.exit_operands(self.pc, &pre)
        };
        let op = self.exit_op(self.pc, throw);
        self.term(op, ops, vec![]);
        (self.cur, self.live) = saved;
        if throw {
            self.throw_blk = Some(b);
        } else {
            self.exit_blk = Some(b);
        }
        b
    }

    /// Guard-at-defs (§8) for the result of the op just built, on top of
    /// the stack: guard it to the analysis's prediction `claim`. The op has
    /// happened, so a failure exits at `next`, the successor pc, with the
    /// result unguarded on the stack (§5.1's resume rule).
    fn guard_result(&mut self, claim: crate::facts::Claim, next: Pc, int_first: bool) {
        let prims = claim.prims();
        if claim.is_none() || claim.is_object() || prims.is_empty() {
            return;
        }
        let (op, ty) = match num_claim_ty(claim, int_first) {
            Some(Ty::I32) => (Opcode::GuardUnbox(UnboxKind::I32), Ty::I32),
            Some(Ty::F64) => (Opcode::GuardUnbox(UnboxKind::F64Num), Ty::F64),
            _ => return,
        };
        let x = self.top();
        if !matches!(x.ty, Ty::Val(_)) {
            return;
        }
        let depth = self.st.len() - self.frame_len();
        if self.s.depths.at(next) != Some(u32::try_from(depth).unwrap()) {
            return;
        }
        let st = self.st.clone();
        let saved = (self.cur, self.live);
        let fail = self.new_block();
        self.at(fail);
        let ops = self.exit_operands(next, &st);
        let eop = self.exit_op(next, false);
        self.term(eop, ops, vec![]);
        (self.cur, self.live) = saved;
        let ok = self.new_block();
        let p = self.f.add_param(ok, ty.mir());
        self.term(
            op,
            vec![x.v],
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fail),
            ],
        );
        self.at(ok);
        self.st.pop();
        self.push(p, ty);
    }

    fn site(&self, pc: Pc) -> crate::ids::Site {
        crate::ids::Site::new(self.s.sid, pc)
    }

    /// A fallible check: continue on success with its output (of type
    /// `out`), exit at the op's pc on failure.
    /// Layout `key`'s fields in slot order, each with its claim (MIR.md
    /// §2.3: the row a constructor builds, `stamp_ctors_in`), registered
    /// in the module's layout table for `init_field` and `publish_layout`.
    /// `None` if no constructor builds it, or the table already describes
    /// one of its slots otherwise.
    fn ctor_layout(&mut self, key: u32) -> Option<std::rc::Rc<Vec<(mir::entity::AtomId, MType)>>> {
        if let Some(l) = self.ctor_layouts.get(&key) {
            return l.clone();
        }
        let l = self.make_ctor_layout(key).map(std::rc::Rc::new);
        self.ctor_layouts.insert(key, l.clone());
        l
    }

    fn make_ctor_layout(&mut self, key: u32) -> Option<Vec<(mir::entity::AtomId, MType)>> {
        let ctx = self.s.ctx;
        // A constructor's row, or, for a construct through a shared
        // wrapper (`Class.create`'s), the site's or its init delegate's.
        let si = ctx
            .stamp_ctors_in
            .values()
            .chain(ctx.construct_sites_in.values())
            .chain(ctx.deleg_restamps_in.values())
            .find(|si| si.layout_id == key)?;
        let names = self.s.names?;
        let claims = ctx.layout_field_types_in.get(&crate::ids::LayoutKey::new(key).stamp());
        let out: Vec<(mir::entity::AtomId, MType)> = si
            .fields
            .iter()
            .map(|&n| {
                let a = self.mm.intern_atom(names.get(n).chars());
                let claim = match claims.and_then(|m| m.get(&n)).filter(|c| !c.is_none()) {
                    Some(&c) => MType::val(claim_tags(c)),
                    None => MType::VAL_TOP,
                };
                (a, claim)
            })
            .collect();
        let l = self.mm.layouts.entry(crate::ids::LayoutKey::new(key)).or_default();
        if l.fields.len() > out.len() {
            return None;
        }
        l.fields.resize(out.len(), None);
        for (i, &(a, claim)) in out.iter().enumerate() {
            match &l.fields[i] {
                None => l.fields[i] = Some(mir::module::FieldDef { name: a, claim }),
                Some(f) if f.name == a && f.claim == claim => {}
                Some(_) => return None,
            }
        }
        Some(out)
    }

    /// The layout a constructor `k`'s `this` is under construction for,
    /// and its TYPES, when a construct allocates it with `word`: the
    /// sentinel with `k`'s own early key (`CTOR_TYPES`).
    fn ctor_of_word(&mut self, k: ScriptId, word: u32) -> Option<(u32, bool)> {
        if !CTOR_TYPES || word & crate::wasm::bbv::CLASS_WORD_SENTINEL == 0 {
            return None;
        }
        let early = (word >> crate::wasm::bbv::abi::EARLY_KEY_SHIFT) & 0xFFF;
        // A shared wrapper constructor has no row of its own: the site's
        // (`construct_sites_in`) put its key in the word.
        let key = match self.s.ctx.stamp_ctors_in.get(&k) {
            Some(si) => si.layout_id,
            None => early.checked_sub(1)?,
        };
        if early != key + 1 {
            return None;
        }
        self.ctor_layout(key)?;
        Some((key, word & crate::wasm::bbv::CLASS_WORD_SHALLOW != 0))
    }

    /// `recv.f` for an object under construction (§2.3) whose field `f`
    /// is already added: the field, typed by its claim where TYPES holds.
    /// `false` (nothing built) for any other access.
    fn ctor_get(&mut self, next: Pc, a: mir::entity::AtomId, recv: Slot) -> bool {
        let Ty::Ctor(key, n, t) = recv.ty else { return false };
        let Some(fields) = self.ctor_layout(key) else { return false };
        let Some(i) = fields.iter().position(|&(f, _)| f == a) else {
            return false;
        };
        if i >= n as usize {
            return false;
        }
        let claim = if t { fields[i].1 } else { MType::VAL_TOP };
        let r = self
            .js_dirty_exits(Opcode::LoadField(a), vec![recv.v], Some(claim), next, None)
            .unwrap();
        let tags = match claim {
            MType::Val(s) => s.tags,
            _ => TagSet::ALL,
        };
        let r = self.weaken(r, MType::val(tags));
        self.push(r, Ty::Val(tags));
        true
    }

    /// `recv.f = v` for an object under construction (§2.3): the add of
    /// the next field its layout predicts is an `init_field` (its value
    /// guarded to the field's claim, exiting here on a miss), advancing
    /// `recv` and every copy of it, and publishing the layout
    /// (`publish_layout`) once every field is there; a store to a field
    /// already added is a typed `store_field`. A boxed object a fence
    /// demoted from under construction (`ctor_hint`) is guarded back to
    /// the state the add expects (`guard.ctor`) first. `false` (nothing
    /// built) for any other store.
    fn ctor_set(&mut self, next: Pc, a: mir::entity::AtomId, recv: Slot, v: Slot) -> bool {
        let (key, t, hinted) = match recv.ty {
            Ty::Ctor(key, _, t) => (key, t, false),
            Ty::Val(_) => match self.ctor_hint.get(&recv.v) {
                Some(&(key, _, t)) => (key, t, true),
                None => return false,
            },
            _ => return false,
        };
        let Some(fields) = self.ctor_layout(key) else { return false };
        let Some(i) = fields.iter().position(|&(f, _)| f == a) else {
            return false;
        };
        let recv = if hinted {
            // The add of field `i` expects exactly `i` fields.
            let o = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![recv.v], MType::OBJ_TOP);
            let g = Opcode::GuardCtor {
                key: crate::ids::LayoutKey::new(key),
                n: u32::try_from(i).unwrap(),
                types: t,
            };
            let ty = Ty::Ctor(key, u32::try_from(i).unwrap(), t);
            let c = self.guard(g, vec![o], ty.mir());
            let s = Slot { v: c, ty };
            self.replace_slot(recv.v, s);
            s
        } else {
            recv
        };
        let Ty::Ctor(_, n, _) = recv.ty else { unreachable!() };
        let n = n as usize;
        if i > n {
            return false;
        }
        // The value, of the field's claim: statically, or guarded here.
        let claim = fields[i].1;
        let ctags = match claim {
            MType::Val(s) => s.tags,
            _ => TagSet::ALL,
        };
        let x = self.boxed(v);
        let x = if v.ty.tags().is_nonempty_subset_of(ctags) {
            self.weaken(x, claim)
        } else {
            self.guard(Opcode::GuardTags(ctags), vec![x], claim)
        };
        if i < n {
            let x = if t { x } else { self.weaken(x, MType::VAL_TOP) };
            self.store_mask = Some((vec![(key + 1, ctags)], false));
            self.js_dirty_exits(Opcode::StoreField(a), vec![recv.v, x], None, next, Some(v));
            return true;
        }
        let ty = Ty::Ctor(key, u32::try_from(n + 1).unwrap(), t);
        let o = self.guard(Opcode::InitField(a), vec![recv.v, x], ty.mir());
        let s = Slot { v: o, ty };
        self.replace_slot(recv.v, s);
        if n + 1 == fields.len() {
            // Every field is there: the stamp. It ends construction, so it
            // kills the claims on the object under construction, as its
            // prediction witness says (§4.5); every copy of it is
            // replaced by the published one.
            let pty = Ty::Obj(KeyRange::one(crate::ids::LayoutKey::new(key)), t, true);
            let (inst, rs) = self.f.add_inst(self.cur, Opcode::PublishLayout, vec![o], &[pty.mir()], vec![]);
            self.f.witnesses[inst] = Some(mir::func::Witness {
                may_kill: mir::types::KillPattern::of(mir::types::KillSet::CONSTRUCTING),
            });
            self.replace_slot(o, Slot { v: rs[0], ty: pty });
        }
        true
    }

    /// An object under construction `x` passed as a callee's `this`
    /// (`inline_call_this`): the callee, built for it, gets `x` itself;
    /// this frame continues with `boxed` (its boxed copy), hinted
    /// (`ctor_hint`), since the callee may add fields or publish it.
    fn ctor_pass(&mut self, x: Slot, boxed: mir::Value) -> mir::Value {
        let Ty::Ctor(k, n, t) = x.ty else { unreachable!("ctor_pass of {:?}", x.ty) };
        self.ctor_hint.insert(boxed, (k, n, t));
        let y = Slot {
            v: boxed,
            ty: Ty::Val(TagSet::OBJECT),
        };
        for s in self.st.iter_mut().chain(self.pre.iter_mut()).filter(|s| s.v == x.v) {
            *s = y;
        }
        self.renames.push((x.v, y));
        x.v
    }

    /// At a return, the construction state `this` is left in
    /// (`this_out`).
    fn note_this_out(&mut self) {
        let now = match self.st.first().map(|x| x.ty) {
            Some(Ty::Ctor(k, n, t)) => Some((k, n, t)),
            _ => None,
        };
        self.this_out = Some(match self.this_out {
            None => now,
            Some(prev) if prev == now => now,
            Some(_) => None,
        });
    }

    /// The state of an object under construction `boxed`, passed to
    /// inlined `targets` as `this`, after them: every callee's `this_out`,
    /// where they agree, is its next use's guard (`ctor_hint`).
    fn ctor_after(&mut self, targets: &[(ScriptId, std::rc::Rc<super::inline::Callee>)], boxed: mir::Value) {
        let outs: Vec<Option<(u32, u32, bool)>> = targets.iter().map(|(_, c)| c.this_out).collect();
        match outs.first() {
            Some(&Some(o)) if outs.iter().all(|&x| x == Some(o)) => {
                self.ctor_hint.insert(boxed, o);
            }
            _ => {
                self.ctor_hint.remove(&boxed);
            }
        }
    }

    /// A boxed receiver `x` a fence demoted from under construction
    /// (`ctor_hint`), guarded back to the state it was left in, for a call
    /// whose callees are built for it; exiting here on a miss.
    fn ctor_reguard(&mut self, x: Slot) -> Option<Slot> {
        let &(k, n, t) = self.ctor_hint.get(&x.v)?;
        if !matches!(x.ty, Ty::Val(_)) {
            return None;
        }
        let o = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![x.v], MType::OBJ_TOP);
        let g = Opcode::GuardCtor {
            key: crate::ids::LayoutKey::new(k),
            n,
            types: t,
        };
        let ty = Ty::Ctor(k, n, t);
        let c = self.guard(g, vec![o], ty.mir());
        let s = Slot { v: c, ty };
        self.replace_slot(x.v, s);
        Some(s)
    }

    /// Replace every copy of `old` in the state with `new` (the receiver
    /// of an `init_field`, advanced; published). For an object under
    /// construction, every slot of its layout's constructing type is it:
    /// a builder run's only such object is its own `this` (another's, an
    /// inlined `new`'s, lives in that callee's run, and leaves it boxed),
    /// though a join may have given it a second value (an operand copy
    /// made a block param), whose claim the add has made stale.
    fn replace_slot(&mut self, old: mir::Value, new: Slot) {
        let key = match new.ty {
            Ty::Ctor(k, ..) => Some(k),
            Ty::Obj(keys, ..) if keys.lo == keys.hi => Some(keys.lo.get()),
            _ => None,
        };
        let mut olds = vec![old];
        for x in self.st.iter_mut() {
            let same = x.v == old || matches!(x.ty, Ty::Ctor(k, ..) if Some(k) == key);
            if same && x.v != new.v {
                if !olds.contains(&x.v) {
                    olds.push(x.v);
                }
                *x = new;
            }
        }
        for o in olds {
            self.renames.push((o, new));
        }
    }

    /// A guard whose failure cannot happen (it restates what the op before
    /// it made so): its fail edge is unreachable.
    fn assert_guard(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        let ok = self.new_block();
        let p = self.f.add_param(ok, out);
        let never = self.new_block();
        self.term(
            op,
            args,
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(never),
            ],
        );
        self.at(never);
        self.term(Opcode::Unreachable, vec![], vec![]);
        self.at(ok);
        p
    }

    fn guard(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        let ok = self.new_block();
        let p = self.f.add_param(ok, out);
        let fail = self.exit_block(false);
        self.term(
            op,
            args,
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fail),
            ],
        );
        self.at(ok);
        p
    }

    /// A method's `this`, guarded once to the layouts the analysis
    /// predicts for it (`this_layouts`), exiting here (nothing has
    /// happened yet) on a miss. Its field accesses then fold their own
    /// guards into this one while no fence intervenes (§10.1), and their
    /// IC fallbacks go with them.
    fn guard_this_layout(&mut self) {
        if !THIS_ENTRY_GUARD {
            return;
        }
        let ctx = self.s.ctx;
        let sid = self.s.sid;
        let Some(&(lo, hi)) = ctx.facts.this_layouts.get(&sid) else {
            return;
        };
        // A constructor's `this` is still being built: known so where the
        // inlining `new` passed it (`Ctor`), else left unguarded; so is a
        // method a constructor calls on it (`ctor_publish`: early
        // publication stamps it only once every field is there), whose
        // accesses guard it each, reading through the IC on a miss, as
        // bbv's lazy class facts do.
        if matches!(self.top().ty, Ty::Ctor(..))
            || ctx.stamp_ctors_in.contains_key(&sid)
            || ctx.deleg_restamps_in.contains_key(&sid)
            || ctx.facts.ctor_publish.contains_key(&sid)
            || ctx.this_layouts_in.get(&sid).is_some_and(|l| l.init_home)
        {
            return;
        }
        let x = self.top();
        let v = self.boxed(x);
        let o = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![v], MType::OBJ_TOP);
        let keys = KeyRange { lo, hi };
        // Identity and TYPES are what OPT means (§4.3): where the layouts
        // type their fields, the guard proves TYPES too, and `this`'s
        // field reads are of their predicted types unchecked.
        let types = (lo.get()..=hi.get()).all(|k| self.s.types_bit(k) != 0);
        // SLOTS too: `this`'s accesses have slot predictions.
        let ty = Ty::Obj(keys, types, true);
        let g = self.guard(Opcode::GuardLayout { keys, types, slots: true }, vec![o], ty.mir());
        self.st.pop();
        self.push(g, ty);
    }

    /// Boxed `v` as narrow object type `t` (`Native`, `Ta`): unboxed, then
    /// its kind guarded, branching to `fail` on a miss.
    fn guard_narrow(&mut self, v: mir::Value, t: Ty, fail: mir::Block) -> mir::Value {
        let kind = match t {
            Ty::Native => ObjKind::Native,
            Ty::Ta(k) => ObjKind::TypedArray(k),
            t => unreachable!("guard_narrow to {t:?}"),
        };
        let ok = self.new_block();
        let u = self.f.add_param(ok, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![v],
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fail),
            ],
        );
        self.at(ok);
        let ok = self.new_block();
        let o = self.f.add_param(ok, t.mir());
        self.term(
            Opcode::GuardKind(kind),
            vec![u],
            vec![
                Edge {
                    block: ok,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fail),
            ],
        );
        self.at(ok);
        o
    }

    /// An element access at `pc` the analysis predicts on a typed array of
    /// kind k (`ta_elem_sites`), with an int32 key: the receiver as that
    /// typed array (proven by its slot, or guarded here, exiting on a
    /// miss, every slot holding it refined), the raw index and the kind.
    /// Not a Uint32Array (its elements are not int32s).
    fn ta_elem(&mut self, pc: Pc, recv: Slot, key: Slot) -> Option<(mir::Value, mir::Value, crate::opsem::TaKind)> {
        let k = match recv.ty {
            Ty::Ta(k) => k,
            _ => *self.s.ctx.facts.ta_elem_sites.get(&self.site(pc))?,
        };
        if !TA_ELEMS || k == crate::opsem::TaKind::Uint32 || key.ty.num() != Some(Num::I32) {
            return None;
        }
        let o = match recv.ty {
            Ty::Ta(_) => recv.v,
            Ty::Obj(..) | Ty::ObjHint(_) | Ty::Native => {
                self.guard(Opcode::GuardKind(ObjKind::TypedArray(k)), vec![recv.v], Ty::Ta(k).mir())
            }
            Ty::Val(t) if TagSet::OBJECT.subset_of(t) => {
                let u = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![recv.v], MType::OBJ_TOP);
                let o = self.guard(Opcode::GuardKind(ObjKind::TypedArray(k)), vec![u], Ty::Ta(k).mir());
                for x in self.st.iter_mut() {
                    if x.v == recv.v {
                        *x = Slot { v: o, ty: Ty::Ta(k) };
                    }
                }
                o
            }
            _ => return None,
        };
        let i = self.as_i32(key);
        Some((o, i, k))
    }

    /// An element access at `pc` the analysis predicts on an array with an
    /// int32 key: the receiver as a native object (proven by its slot, or
    /// guarded here, exiting on a miss, and every slot holding it then
    /// refined) and the raw index. `None` for anything else.
    fn native_elem(&mut self, pc: Pc, recv: Slot, key: Slot) -> Option<(mir::Value, mir::Value)> {
        // The analysis saw the site read numbers or objects (not a
        // string's characters), or write, or knows the array's class.
        let site = self.site(pc);
        let facts = &self.s.ctx.facts;
        let predicted = self.s.ctx.array_elem_in.contains_key(&site)
            || facts.elem_write_sites.contains_key(&site)
            || facts.elem_sites.get(&site).is_some_and(|c| {
                c.is_object() || (!c.prims().is_empty() && c.prims().subset_of(crate::opsem::NUM))
            });
        if !NATIVE_ELEMS
            || (recv.ty != Ty::Native && !predicted)
            || key.ty.num() != Some(Num::I32)
            || !TagSet::OBJECT.subset_of(recv.ty.tags())
        {
            return None;
        }
        let i = self.as_i32(key);
        let o = match recv.ty {
            Ty::Native => recv.v,
            Ty::Obj(..) | Ty::ObjHint(_) => self.guard(
                Opcode::GuardKind(ObjKind::Native),
                vec![recv.v],
                Ty::Native.mir(),
            ),
            Ty::Val(_) => {
                let u = self.guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![recv.v], MType::OBJ_TOP);
                let o = self.guard(Opcode::GuardKind(ObjKind::Native), vec![u], Ty::Native.mir());
                for x in self.st.iter_mut() {
                    if x.v == recv.v {
                        *x = Slot { v: o, ty: Ty::Native };
                    }
                }
                o
            }
            _ => return None,
        };
        Some((o, i))
    }

    /// Receiver `recv` of a typed site, when its slot type proves the
    /// site's layouts: the object (for an `ObjHint`, guarded again,
    /// exiting here on a miss, and every slot holding it refined), and
    /// the site as it applies to it: with TYPES only if the slot has the
    /// bit proven (a site that would guard for the bit reads under
    /// identity alone, and its claim is guarded at the def).
    fn proven_recv(&mut self, recv: Slot, site: &TypedSite) -> Option<(mir::Value, TypedSite)> {
        let (keys, types, slots) = match recv.ty {
            Ty::Obj(keys, types, slots) => (keys, Some(types), slots),
            Ty::ObjHint(keys) => (keys, None, false),
            _ => return None,
        };
        let want = KeyRange {
            lo: crate::ids::LayoutKey::new(site.lo),
            hi: crate::ids::LayoutKey::new(site.hi),
        };
        if !want.contains(&keys) {
            return None;
        }
        let site = TypedSite {
            types: site.types && types == Some(true),
            ..*site
        };
        // A field with a slot prediction needs SLOTS proven: a receiver
        // proven without it (or only hinted) is guarded (again) with it.
        let o = match types {
            Some(_) if slots || !site.slotted => recv.v,
            _ => {
                let t = types.unwrap_or(false);
                let s = site.slotted;
                let ty = Ty::Obj(keys, t, s);
                let g = self.guard(Opcode::GuardLayout { keys, types: t, slots: s }, vec![recv.v], ty.mir());
                for x in self.st.iter_mut() {
                    if x.v == recv.v {
                        *x = Slot { v: g, ty };
                    }
                }
                g
            }
        };
        Some((o, site))
    }

    /// A fused global's read (§3): while its fuse is armed the read is the
    /// literal, else exit here. False (nothing emitted) for a literal that
    /// is not a primitive constant.
    fn fused_gname(&mut self, name: mir::entity::AtomId, fg: crate::wasm::translate::FusedGname) -> bool {
        use crate::wasm::translate::{TAG_BOOLEAN, TAG_CLEAR, TAG_INT32, TAG_NULL, TAG_UNDEFINED};
        let (tag, payload) = (fg.boxed >> 32, fg.boxed as u32);
        if !(tag == TAG_INT32
            || tag < u64::from(TAG_CLEAR)
            || tag == TAG_BOOLEAN
            || tag == TAG_NULL
            || tag == TAG_UNDEFINED)
        {
            return false;
        }
        let found = self.mm.fuses.iter().find(|(_, d)| d.addr == fg.fuse_addr).map(|(f, _)| f);
        let fid = match found {
            Some(f) => f,
            None => self.mm.fuses.push(mir::module::FuseDef {
                name: self.mm.atoms[name].to_string(),
                addr: fg.fuse_addr,
            }),
        };
        self.guard(Opcode::CheckFuse(fid), vec![], MType::Fact(mir::types::FactKind::Fuse(fid)));
        let (v, ty) = if tag == TAG_INT32 {
            (self.const_i32(payload as i32), Ty::I32)
        } else if tag < u64::from(TAG_CLEAR) {
            (self.const_f64(f64::from_bits(fg.boxed)), Ty::F64)
        } else if tag == TAG_BOOLEAN {
            (self.inst(Opcode::ConstBool(payload != 0), vec![], Some(MType::Bool)), Ty::Bool)
        } else if tag == TAG_NULL {
            (self.const_val(ConstVal::Null), Ty::Val(TagSet::prims(PRIM_NULL)))
        } else {
            (self.const_val(ConstVal::Undefined), Ty::Val(TagSet::prims(PRIM_UNDEFINED)))
        };
        self.push(v, ty);
        true
    }

    /// The environment `hops` links up the chain from the activation's
    /// (which is fixed: see `build`).
    fn env_at(&mut self, hops: u16) -> mir::Value {
        let env = MType::Obj(ObjInfo::kind(ObjKind::Env));
        let mut e = self.inst(Opcode::EnvCurrent, vec![], Some(env.clone()));
        for _ in 0..hops {
            e = self.inst(Opcode::EnvParent, vec![e], Some(env.clone()));
        }
        e
    }

    /// The atom for gcthing `index` (a name), in the module's table.
    fn atom(&mut self, index: u32) -> R<mir::entity::AtomId> {
        let gc = *self
            .s
            .script
            .gcthings
            .get(usize::try_from(index).unwrap())
            .ok_or_else(|| format!("name index {index} out of range"))?;
        match self.s.ctx.source.object(gc) {
            crate::source::SourceObject::String(s) => Ok(self.mm.intern_atom(s.chars())),
            _ => Err(format!("name index {index} is not a string")),
        }
    }

    /// The analysis's layout prediction for the property access at `pc`
    /// (`prop_sites`), with its field recorded in the module's layouts;
    /// `None` without one, or when it disagrees with another site's
    /// description of the same slot.
    fn typed_site(&mut self, pc: Pc, name: mir::entity::AtomId) -> Option<TypedSite> {
        let ps = *self
            .s
            .ctx
            .prop_sites_in
            .get(&crate::ids::Site::new(self.s.sid, pc))?;
        self.site_for(ps.layout_id, ps.hi_layout_id, ps.slot, ps.claim, ps.shallow_possible, name)
    }

    /// The classes a store of field `name` at `pc` through `recv` checks
    /// its value against (`FIELD_MASKS`), each with its own predicted type
    /// for the field, as an IC validating the object's class before it
    /// stores: every class typing the field (complete) where they are few,
    /// else those the receiver is predicted of (the site row's, the hinted
    /// class, or, through `this`, the script's own row or the layout its
    /// constructor builds).
    fn field_claim(&mut self, pc: Pc, name: mir::entity::AtomId, recv: Slot) -> Option<(Vec<(u32, TagSet)>, bool)> {
        if !FIELD_MASKS {
            return None;
        }
        let n = self.s.names?.lookup(self.mm.atoms[name].chars())?;
        let all = self.s.name_classes(n);
        if all.len() <= MAX_STORE_CLASSES {
            return Some((all.to_vec(), true));
        }
        let site = crate::ids::Site::new(self.s.sid, pc);
        let (lo, hi) = if let Some(ps) = self.s.ctx.prop_sites_in.get(&site) {
            (ps.layout_id, ps.hi_layout_id)
        } else if let Some(&cls) = self.val_cls.get(&recv.v) {
            (cls, cls)
        } else if recv.v == self.st.first().map(|x| x.v)? || self.this_vals.contains(&recv.v) {
            let ctx = self.s.ctx;
            let sid = self.s.sid;
            if let Some(li) = ctx.this_layouts_in.get(&sid) {
                (li.layout_id, li.hi_layout_id)
            } else if let Some(si) = ctx.stamp_ctors_in.get(&sid).or_else(|| ctx.deleg_restamps_in.get(&sid)) {
                (si.layout_id, si.layout_id)
            } else if let Some(ctors) = ctx.facts.ctor_publish.get(&sid) {
                // A construction delegate (`ctor_publish`): the layouts
                // of the constructors whose objects it may be building.
                let keys: Vec<u32> = ctors
                    .iter()
                    .filter_map(|c| Some(ctx.stamp_ctors_in.get(c)?.layout_id + 1))
                    .collect();
                let some: Vec<(u32, TagSet)> = all.iter().copied().filter(|(k, _)| keys.contains(k)).collect();
                return Some((some, false));
            } else {
                return None;
            }
        } else {
            return None;
        };
        let some: Vec<(u32, TagSet)> = all.iter().copied().filter(|&(k, _)| k > lo && k <= hi + 1).collect();
        Some((some, false))
    }

    /// A property access with no site row, through a receiver the analysis
    /// hints one class for (`val_cls`: bbv's advisory tier, from
    /// `arg_cls` and `field_cls_sites`): that class's field, from its
    /// layout row (`this_layouts_in`). The hint is unchecked; the typed
    /// access guards it, reading through the IC on a miss.
    fn hinted_site(&mut self, recv: mir::Value, name: mir::entity::AtomId) -> Option<TypedSite> {
        if !CLS_HINTS {
            return None;
        }
        let cls = *self.val_cls.get(&recv)?;
        let n = self.s.names?.lookup(self.mm.atoms[name].chars())?;
        let (slot, claim) = self.s.layout_field(cls, n)?;
        self.site_for(cls, cls, slot, claim, true, name)
    }

    /// The accessor an accessor-site property access calls (bbv's
    /// `accessor_sites`, the modeled `Object.defineProperty` accessors):
    /// the site's resolved getter or setter, or, for a name registered as
    /// an accessor somewhere, `None` (probed without a static target).
    /// `None` outright where neither applies.
    fn accessor_site(&self, pc: Pc, a: mir::entity::AtomId, set: bool) -> Option<Option<ScriptId>> {
        let facts = &self.s.ctx.facts;
        match facts.accessor_sites.get(&self.site(pc)) {
            Some(&(k, kind)) if kind == u8::from(set) => return Some(Some(k)),
            _ => {}
        }
        let n = self.s.names?.lookup(self.mm.atoms[a].chars())?;
        facts.accessor_names.contains(&n).then_some(None)
    }

    /// `recv.a` at an accessor site: the receiver's shape probed in the
    /// runtime's accessor-call cache (`accessor.probe`), the getter it
    /// finds called with `recv` as `this` (directly, where the site
    /// resolves it); any other receiver reads through the IC.
    fn accessor_get(&mut self, pc: Pc, a: mir::entity::AtomId, recv: Slot) -> bool {
        let Some(target) = self.accessor_site(pc, a, false) else {
            return false;
        };
        let x = self.boxed(recv);
        let r = self.accessor_call(a, false, target, vec![x], MType::VAL_TOP, Opcode::JsGetProp(a));
        self.push(r, Ty::Val(TagSet::ALL));
        let claim = self.s.ctx.facts.field_sites.get(&self.site(pc)).copied();
        self.guard_result(claim.unwrap_or_default(), pc + JSOp::GetProp.len(), false);
        true
    }

    /// `recv.a = v` at an accessor site: the setter the probe finds
    /// called with `recv` and `v`; any other receiver stores through the
    /// IC. The value stays on the stack.
    fn accessor_set(&mut self, pc: Pc, a: mir::entity::AtomId, recv: Slot, v: Slot, strict: bool) -> bool {
        let Some(target) = self.accessor_site(pc, a, true) else {
            return false;
        };
        let (x, y) = (self.boxed(recv), self.boxed(v));
        self.accessor_call(a, true, target, vec![x, y], MType::VAL_TOP, Opcode::JsSetProp(a, strict));
        true
    }

    /// The probe-and-call diamond of `accessor_get`/`accessor_set`:
    /// `vals` the receiver (and the value); `generic` the IC op on a miss.
    /// A getter's result, or (for a setter) the call's, unused.
    fn accessor_call(
        &mut self,
        a: mir::entity::AtomId,
        set: bool,
        target: Option<ScriptId>,
        vals: Vec<mir::Value>,
        out: MType,
        generic: Opcode,
    ) -> mir::Value {
        // Arms that fence meet at `join`: `Obj` slots go in as `ObjHint`.
        if !self.keepable(1) {
            self.demote_objs();
        }
        let join = self.new_block();
        let jr = self.f.add_param(join, out);
        let (hit, miss) = (self.new_block(), self.new_block());
        let callee = self.f.add_param(hit, MType::val(TagSet::OBJECT));
        self.term(
            Opcode::AccessorProbe(a, set),
            vec![vals[0]],
            vec![
                Edge {
                    block: hit,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(miss),
            ],
        );
        self.at(hit);
        let mut call = vec![callee];
        call.extend(&vals);
        self.likely_targets = match target {
            Some(k) if DIRECT_CALLS && self.s.direct_ok(k) => vec![k],
            _ => vec![],
        };
        let r = if set {
            // The stack after the op holds the stored value, not the
            // setter's result.
            self.js_void_keep(Opcode::Call, call, Slot { v: vals[1], ty: Ty::Val(TagSet::ALL) });
            vals[1]
        } else {
            self.js(Opcode::Call, call, out)
        };
        self.likely_targets.clear();
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(r)],
            }],
        );
        self.at(miss);
        let r = if set {
            self.js_void_keep(generic, vals.clone(), Slot { v: vals[1], ty: Ty::Val(TagSet::ALL) });
            vals[1]
        } else {
            self.js(generic, vals, out)
        };
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(r)],
            }],
        );
        self.at(join);
        jr
    }

    /// A field of a receiver proven with TYPES whose layouts all type it
    /// but predict no slot for it (added outside the constructors): read
    /// or written through an IC for the slot, of its predicted type.
    /// Registered in the module's layouts as a named field.
    fn named_site(&mut self, recv: Slot, name: mir::entity::AtomId) -> Option<TypedSite> {
        let Ty::Obj(keys, true, _) = recv.ty else { return None };
        let n = self.s.names?.lookup(self.mm.atoms[name].chars())?;
        let (lo, hi) = (keys.lo.get(), keys.hi.get());
        let mut masks = vec![];
        for k in lo..=hi {
            if self.s.layout_field(k, n).is_some() {
                return None;
            }
            let c = *self.s.ctx.layout_field_types_in.get(&crate::ids::LayoutKey::new(k).stamp())?.get(&n)?;
            if c.is_none() {
                return None;
            }
            masks.push(claim_tags(c));
        }
        for (i, k) in (lo..=hi).enumerate() {
            let def = mir::module::FieldDef {
                name,
                claim: MType::val(masks[i]),
            };
            let l = self.mm.layouts.entry(crate::ids::LayoutKey::new(k)).or_default();
            if l.field(name).is_some() {
                return None;
            }
            match l.named_field(name) {
                None => l.named.push(def),
                Some(f) if *f == def => {}
                Some(_) => return None,
            }
        }
        Some(TypedSite {
            lo,
            hi,
            types: true,
            claim: crate::facts::Claim::NONE,
            load_tags: masks.iter().fold(TagSet::NONE, |a, &m| a.union(m)),
            store_tags: masks.iter().fold(TagSet::ALL, |a, &m| a.intersect(m)),
            slotted: false,
        })
    }

    fn site_for(
        &mut self,
        lo: u32,
        hi: u32,
        slot: u32,
        claim_in: crate::facts::Claim,
        shallow_possible: bool,
        name: mir::entity::AtomId,
    ) -> Option<TypedSite> {
        // TYPES (§4.6): each layout's predicted type for the field, where
        // the receivers can carry the bit and every layout predicts one.
        let n = self.s.names.and_then(|ns| ns.lookup(self.mm.atoms[name].chars()));
        let masks: Vec<TagSet> = (lo..=hi)
            .filter_map(|k| {
                let c = *self.s.ctx.layout_field_types_in.get(&crate::ids::LayoutKey::new(k).stamp())?.get(&n?)?;
                (!c.is_none()).then(|| claim_tags(c))
            })
            .collect();
        let types = shallow_possible && masks.len() == (hi - lo + 1) as usize;
        let load_tags = masks.iter().fold(TagSet::NONE, |a, &m| a.union(m));
        let store_tags = masks.iter().fold(TagSet::ALL, |a, &m| a.intersect(m));
        let site = TypedSite {
            lo,
            hi,
            types,
            claim: claim_in,
            load_tags,
            store_tags,
            slotted: true,
        };
        let slot = usize::try_from(slot).unwrap();
        for (i, k) in (site.lo..=site.hi).enumerate() {
            let claim = if types { MType::val(masks[i]) } else { MType::VAL_TOP };
            let l = self
                .mm
                .layouts
                .entry(crate::ids::LayoutKey::new(k))
                .or_default();
            if l.fields.len() <= slot {
                l.fields.resize(slot + 1, None);
            }
            match &l.fields[slot] {
                None => {
                    l.fields[slot] = Some(mir::module::FieldDef { name, claim });
                }
                Some(f) if f.name == name && f.claim == claim => {}
                Some(_) => return None,
            }
        }
        Some(site)
    }

    /// Guard boxed receiver `x` to an object of the site's layouts (§4.3):
    /// an object tag test, then the stamp compare, branching to `fallback`
    /// (no params) when either fails.
    fn guard_layout_or(&mut self, x: mir::Value, site: &TypedSite, fallback: mir::Block) -> mir::Value {
        let ob = self.new_block();
        let o = self.f.add_param(ob, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![x],
            vec![
                Edge {
                    block: ob,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fallback),
            ],
        );
        self.at(ob);
        let keys = KeyRange {
            lo: crate::ids::LayoutKey::new(site.lo),
            hi: crate::ids::LayoutKey::new(site.hi),
        };
        let t = MType::Obj(ObjInfo {
            layout: Some(LayoutClaim {
                keys,
                types: site.types,
                slots: site.slotted,
                state: LayoutState::Published,
            }),
            ..ObjInfo::TOP
        });
        let lb = self.new_block();
        let lo = self.f.add_param(lb, t);
        self.term(
            Opcode::GuardLayout {
                keys,
                types: site.types,
                slots: site.slotted,
            },
            vec![o],
            vec![
                Edge {
                    block: lb,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fallback),
            ],
        );
        self.at(lb);
        lo
    }

    /// A generic op with a static kill (`ok`, `err`): the builder attaches
    /// its prediction witness (§4.5), which for a generic op is "may kill
    /// anything".
    fn js_static(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        let ok = self.new_block();
        let p = self.f.add_param(ok, out);
        let err = self.exit_block(true);
        let mut succs = vec![
            Edge {
                block: ok,
                args: vec![EdgeArg::Out(0)],
            },
            Self::goto(err),
        ];
        self.retain_locals(&op);
        self.fence_params(&op, &args, &mut succs);
        let (inst, _) = self.f.add_inst(self.cur, op, args, &[], succs);
        self.f.witnesses[inst] = Some(mir::func::Witness {
            may_kill: mir::types::KillPattern::ALL,
        });
        self.live = false;
        self.at(ok);
        p
    }

    /// A generic op with no output: both success edges continue; an
    /// exception goes to the op's throw block.
    /// A typed field access (`load_field`/`store_field`) whose `ok_dirty`
    /// edge (its IC arm reported dirt: a SLOTS miss) exits at `next`, the
    /// successor pc, with `post` on the stack (the op has happened). The
    /// clean path then keeps every fact, so the accesses after it fold
    /// their guards (§4.2). Returns the result, if `out`. Without a stack
    /// depth at `next`, both edges continue, as `js` has them.
    fn js_dirty_exits(
        &mut self,
        op: Opcode,
        args: Vec<mir::Value>,
        out: Option<MType>,
        next: Pc,
        post: Option<Slot>,
    ) -> Option<mir::Value> {
        debug_assert_eq!(self.next_pc, Some(next));
        let dirty = if DIRTY_EXITS { self.dirty_exit(out, post) } else { None };
        let Some(dirty) = dirty else {
            // Nowhere to exit to: a fence.
            return match out {
                Some(t) => Some(self.js_fence(op, args, t)),
                None => {
                    self.js_void(op, args);
                    None
                }
            };
        };
        let ok = self.new_block();
        let p = out.map(|t| self.f.add_param(ok, t));
        let clean = Edge {
            block: ok,
            args: p.map(|_| vec![EdgeArg::Out(0)]).unwrap_or_default(),
        };
        let err = self.exit_block(true);
        // Not `term`: the clean edge is no fence.
        self.retain_locals(&op);
        let (inst, _) = self.f.add_inst(self.cur, op, args, &[], vec![clean, dirty, Self::goto(err)]);
        self.attach_targets(inst);
        self.live = false;
        self.at(ok);
        p
    }

    /// `js_void` for an op that leaves `post` on the stack (a store's
    /// value), keeping facts on its clean edge (`js_keep`).
    fn js_void_keep(&mut self, op: Opcode, args: Vec<mir::Value>, post: Slot) {
        if self.js_keep(op, args.clone(), None, Some(post)).is_none() {
            self.js_void(op, args);
        }
    }

    /// A generic op that keeps the frame's proven layouts on its clean
    /// edge (bbv's epoch keep: the lowering takes `ok_clean` when the
    /// stamp epoch did not move across the op's helper, so no class word
    /// was demoted), its dirty edge exiting at the next pc with the op's
    /// result (`out`) or the value it leaves (`post`). Only where there is
    /// something to keep and the stack at the next pc is this op's
    /// result; else `None`, and the caller fences as before.
    fn js_keep(
        &mut self,
        op: Opcode,
        args: Vec<mir::Value>,
        out: Option<MType>,
        post: Option<Slot>,
    ) -> Option<Option<mir::Value>> {
        use mir::ops::KillSite;
        // A callee built for inlining keeps with no `Obj` of its own: its
        // caller's facts ride on its every kill exiting.
        if self.s.inline_depth == 0 && !self.st.iter().chain(&self.pre).any(|x| matches!(x.ty, Ty::Obj(..))) {
            return None;
        }
        let tys: Vec<MType> = args.iter().map(|&v| self.f.ty(v)).collect();
        let fx = mir::ops::effects(&op, &tys, &self.mm);
        if op.kill_site(&fx) != KillSite::DirtyEdge {
            return None;
        }
        let dirty = self.dirty_exit(out, post)?;
        let ok = self.new_block();
        let p = out.map(|t| self.f.add_param(ok, t));
        let clean = Edge {
            block: ok,
            args: p.map(|_| vec![EdgeArg::Out(0)]).unwrap_or_default(),
        };
        let err = self.exit_block(true);
        self.retain_locals(&op);
        let (inst, _) = self.f.add_inst(self.cur, op, args, &[], vec![clean, dirty, Self::goto(err)]);
        self.attach_targets(inst);
        self.live = false;
        self.at(ok);
        Some(p)
    }

    /// Whether a kill here can exit at the next pc (`dirty_exit`), with
    /// `results` values there on top of the frame as it is now.
    fn keepable(&self, results: usize) -> bool {
        KEEP_ON_CLEAN
            && self
                .next_pc
                .and_then(|next| self.s.depths.at(next))
                .is_some_and(|d| d as usize == self.st.len() - self.frame_len() + results)
    }

    /// The dirty edge of a kill that keeps facts on its clean one: an exit
    /// at the next pc with the frame as it is now plus the op's result
    /// (`out`, the edge's `Out(0)`) or the value it leaves (`post`). `Obj`
    /// slots reach it through weaker params, or, for an inline splice
    /// (`weakened`), as weakened copies made here: the callee's dirty
    /// exits name the edge's args in blocks after the kill, where no fact
    /// may be live. `None` where there is no such exit (`keepable`).
    fn dirty_exit(&mut self, out: Option<MType>, post: Option<Slot>) -> Option<Edge> {
        self.dirty_exit_as(out, post, false)
    }

    fn dirty_exit_as(&mut self, out: Option<MType>, post: Option<Slot>, weakened: bool) -> Option<Edge> {
        if !self.keepable(usize::from(post.is_some() || out.is_some())) {
            return None;
        }
        let next = self.next_pc?;
        let out_ty = match out {
            None => None,
            Some(MType::Bool) => Some(Ty::Bool),
            Some(MType::Val(v)) => Some(Ty::Val(v.tags)),
            Some(_) => return None,
        };
        let olds: Vec<Slot> = self.st.iter().chain(&post).copied().collect();
        let mut copies: Vec<(mir::Value, mir::Value)> = vec![];
        if weakened {
            for x in &olds {
                if matches!(x.ty, Ty::Obj(..) | Ty::Ctor(..)) && !copies.iter().any(|&(v, _)| v == x.v) {
                    let w = self.weaken(x.v, MType::OBJ_TOP);
                    copies.push((x.v, w));
                }
            }
        }
        let saved = (self.cur, self.live);
        let b = self.new_block();
        let dp = out.map(|t| self.f.add_param(b, t));
        let mut objs: Vec<(mir::Value, mir::Value)> = vec![];
        for x in &olds {
            if matches!(x.ty, Ty::Obj(..) | Ty::Ctor(..)) && !objs.iter().any(|&(v, _)| v == x.v) {
                let p = match copies.iter().find(|&&(v, _)| v == x.v) {
                    Some(&(_, w)) => w,
                    None => self.f.add_param(b, MType::OBJ_TOP),
                };
                objs.push((x.v, p));
            }
        }
        self.at(b);
        let weaker = |x: Slot, objs: &[(mir::Value, mir::Value)]| match (x.ty, objs.iter().find(|&&(v, _)| v == x.v)) {
            (Ty::Obj(k, ..), Some(&(_, p))) => Slot {
                v: p,
                ty: Ty::ObjHint(k),
            },
            // The block only exits, which boxes it.
            (Ty::Ctor(k, ..), Some(&(_, p))) => Slot {
                v: p,
                ty: Ty::ObjHint(KeyRange::one(crate::ids::LayoutKey::new(k))),
            },
            _ => x,
        };
        let mut st: Vec<Slot> = self.st.iter().map(|&x| weaker(x, &objs)).collect();
        match (dp, post) {
            (Some(v), _) => st.push(Slot {
                v,
                ty: out_ty.unwrap(),
            }),
            (None, Some(x)) => st.push(weaker(x, &objs)),
            (None, None) => {}
        }
        let ops = self.exit_operands(next, &st);
        let eop = self.exit_op(next, false);
        self.term(eop, ops, vec![]);
        (self.cur, self.live) = saved;
        let mut dargs: Vec<EdgeArg> = dp.map(|_| vec![EdgeArg::Out(0)]).unwrap_or_default();
        if !weakened {
            dargs.extend(objs.iter().map(|&(v, _)| EdgeArg::Value(v)));
        }
        Some(Edge { block: b, args: dargs })
    }

    fn js_void(&mut self, op: Opcode, args: Vec<mir::Value>) {
        let ok = self.new_block();
        let err = self.exit_block(true);
        self.term(
            op,
            args,
            vec![Self::goto(ok), Self::goto(ok), Self::goto(err)],
        );
        self.at(ok);
    }

    /// A call whose predicted targets are inlined (§5.5): the callee
    /// guarded to each target's script in turn, each target's MIR spliced
    /// in on its hit; the ordinary call when none matches. Returns the
    /// result, at the continuation. With `this_raw` (an object under
    /// construction, `ctor_pass`), the callees receive it as their `this`,
    /// built for it.
    fn inline_call_this(
        &mut self,
        targets: &[(ScriptId, std::rc::Rc<super::inline::Callee>)],
        vals: &[mir::Value],
        fallback: Option<(Opcode, Vec<mir::Value>)>,
        this_raw: Option<mir::Value>,
    ) -> mir::Value {
        // Facts are fixed: with every kill in the callees exiting (none
        // fenced), a kill leaves for baseline at the call's next pc, and
        // this frame's `Obj` slots keep their facts through the splice.
        // A fenced callee's continue as `ObjHint`.
        let keep = !targets.iter().any(|(_, c)| c.fenced) && self.keepable(1);
        if !keep {
            self.demote_objs();
        }
        let dirty = if keep {
            self.dirty_exit_as(Some(MType::VAL_TOP), None, true)
        } else {
            None
        };
        let join = self.new_block();
        let result = self.f.add_param(join, MType::VAL_TOP);
        let err = self.exit_block(true);
        let generic = self.new_block();
        let obj_b = self.new_block();
        let obj = self.f.add_param(obj_b, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![vals[0]],
            vec![
                Edge {
                    block: obj_b,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(generic),
            ],
        );
        self.at(obj_b);
        for (k, callee) in targets {
            let hit = self.new_block();
            let kt = MType::Obj(ObjInfo::kind(ObjKind::Function(Some(*k))));
            let kobj = self.f.add_param(hit, kt);
            let miss = self.new_block();
            self.term(
                Opcode::GuardScript(*k),
                vec![obj],
                vec![
                    Edge {
                        block: hit,
                        args: vec![EdgeArg::Out(0)],
                    },
                    Self::goto(miss),
                ],
            );
            self.at(hit);
            let nformals = callee.f.frame.formals as usize;
            let mut operands = vec![kobj, this_raw.unwrap_or(vals[1])];
            let undef = self.const_val(ConstVal::Undefined);
            // A callee reading its actuals gets them all.
            let argc = callee.reads_actuals.then(|| u32::try_from(vals.len() - 2).unwrap());
            let n = nformals.max(argc.map_or(0, |a| a as usize));
            for i in 0..n {
                operands.push(vals.get(2 + i).copied().unwrap_or(undef));
            }
            let saved_mm = self.mm.clone();
            let saved_frames = self.f.inline_frames.len();
            self.retain_all();
            match super::inline::splice(&mut self.mm, &mut self.f, callee, 0, hit, &operands, None, argc, join, dirty.clone(), err) {
                Ok(()) => {
                    self.mm.script_addrs.insert(*k, callee.mm.script_addrs[k]);
                }
                Err(_) => {
                    // Not this one after all: the hit takes the ordinary call
                    // (the guard stays, so its script's address does too).
                    self.mm = saved_mm;
                    self.mm.script_addrs.insert(*k, callee.mm.script_addrs[k]);
                    self.f.inline_frames.truncate(saved_frames);
                    self.term(Opcode::Jump, vec![], vec![Self::goto(generic)]);
                }
            }
            self.at(miss);
        }
        self.term(Opcode::Jump, vec![], vec![Self::goto(generic)]);
        self.at(generic);
        let e = Edge {
            block: join,
            args: vec![EdgeArg::Out(0)],
        };
        let (op, args) = fallback.unwrap_or((Opcode::Call, vals.to_vec()));
        match dirty {
            Some(d) => {
                // Not `term`: the clean edge is no fence.
                self.retain_locals(&op);
                self.f.add_inst(self.cur, op, args, &[], vec![e, d, Self::goto(err)]);
                self.live = false;
            }
            None => self.term(op, args, vec![e.clone(), e, Self::goto(err)]),
        }
        self.at(join);
        result
    }

    /// `new F(args…)` of the site's one constructor inlined (§5.5): with
    /// the callee that script's function, `this` is made as a direct
    /// construct makes it (`create_this`), the body is spliced with its
    /// frame's new.target, and the result is the body's value if an
    /// object, else `this`; any other callee takes the generic construct.
    /// Operands `callee, is_constructing, args…, new.target`.
    fn inline_construct(
        &mut self,
        k: ScriptId,
        callee: &std::rc::Rc<super::inline::Callee>,
        vals: &[mir::Value],
        nslots: u32,
        word: u32,
    ) -> mir::Value {
        self.demote_objs();
        let nt = vals[vals.len() - 1];
        let join = self.new_block();
        let result = self.f.add_param(join, MType::val(TagSet::OBJECT));
        let err = self.exit_block(true);
        let generic = self.new_block();
        let obj_b = self.new_block();
        let obj = self.f.add_param(obj_b, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![vals[0]],
            vec![
                Edge {
                    block: obj_b,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(generic),
            ],
        );
        self.at(obj_b);
        let hit = self.new_block();
        let kt = MType::Obj(ObjInfo::kind(ObjKind::Function(Some(k))));
        let kobj = self.f.add_param(hit, kt);
        self.term(
            Opcode::GuardScript(k),
            vec![obj],
            vec![
                Edge {
                    block: hit,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(generic),
            ],
        );
        self.at(hit);
        // Not a constructor (an arrow function, a method): the generic
        // construct throws.
        let is_ctor = self.inst(Opcode::FnIsCtor, vec![kobj], Some(MType::Bool));
        let ctor = self.new_block();
        self.term(Opcode::Br, vec![is_ctor], vec![Self::goto(ctor), Self::goto(generic)]);
        self.at(ctor);
        // A fence: the next pc's value is the construct's, not `this`, so
        // a kill here has nowhere to exit to.
        let this = self.js_fence(Opcode::CreateThis(nslots, word), vec![vals[0], nt], MType::val(TagSet::OBJECT));
        // The object `create_this` made carries `word` (§2.3): under
        // construction for the constructor's own layout, with no field
        // yet. The body is built for that `this`, whose adds are then
        // `init_field`s and whose methods see its construction state.
        let mut callee = callee.clone();
        let mut this_op = this;
        if let Some((key, t)) = self.ctor_of_word(k, word) {
            if let Some(c) = self.s.callee_ctx(k, &[], Some((key, 0, t)), self.admitted) {
                self.inline_sites = (self.inline_sites + c.sites).saturating_sub(callee.sites);
                let o = self.assert_guard(Opcode::GuardUnbox(UnboxKind::Obj), vec![this], MType::OBJ_TOP);
                let g = Opcode::GuardCtor {
                    key: crate::ids::LayoutKey::new(key),
                    n: 0,
                    types: t,
                };
                this_op = self.assert_guard(g, vec![o], Ty::Ctor(key, 0, t).mir());
                callee = c;
            }
        }
        let nformals = callee.f.frame.formals as usize;
        let nargs = vals.len() - 3;
        let mut operands = vec![kobj, this_op];
        let undef = self.const_val(ConstVal::Undefined);
        // A constructor reading its actuals gets them all.
        let argc = callee.reads_actuals.then(|| u32::try_from(nargs).unwrap());
        for i in 0..nformals.max(argc.map_or(0, |a| a as usize)) {
            operands.push(if i < nargs { vals[2 + i] } else { undef });
        }
        // The body's value, then the construct's result rule.
        let ret = self.new_block();
        let r = self.f.add_param(ret, MType::VAL_TOP);
        let saved_mm = self.mm.clone();
        let saved_frames = self.f.inline_frames.len();
        let here = self.cur;
        self.retain_all();
        match super::inline::splice(&mut self.mm, &mut self.f, &callee, 0, here, &operands, Some(nt), argc, ret, None, err) {
            Ok(()) => {
                self.mm.script_addrs.insert(k, callee.mm.script_addrs[&k]);
                self.live = false;
                self.at(ret);
                let t = self.new_block();
                self.term(
                    Opcode::GuardTags(TagSet::OBJECT),
                    vec![r],
                    vec![
                        Edge {
                            block: join,
                            args: vec![EdgeArg::Out(0)],
                        },
                        Self::goto(t),
                    ],
                );
                self.at(t);
                self.term(
                    Opcode::Jump,
                    vec![],
                    vec![Edge {
                        block: join,
                        args: vec![EdgeArg::Value(this)],
                    }],
                );
            }
            Err(_) => {
                self.mm = saved_mm;
                self.mm.script_addrs.insert(k, callee.mm.script_addrs[&k]);
                self.f.inline_frames.truncate(saved_frames);
                self.term(Opcode::Jump, vec![], vec![Self::goto(generic)]);
            }
        }
        self.at(generic);
        let e = Edge {
            block: join,
            args: vec![EdgeArg::Out(0)],
        };
        self.term(Opcode::Construct(nslots, word), vals.to_vec(), vec![e.clone(), e, Self::goto(err)]);
        self.at(join);
        result
    }

    /// `target.apply(this, arguments)` at a proven forward site (bbv's
    /// `compute_apply_fwd_pcs`: the arguments object feeds only such calls,
    /// so it was never made), operands `apply, target, this, placeholder`.
    /// With the `.apply` the pristine builtin, the site's known targets
    /// are inlined, their formals read from this frame's actuals; any other
    /// target, or another `.apply`, forwards through the runtime.
    fn apply_forward(&mut self, vals: &[mir::Value], this_ctor: Option<((u32, u32, bool), Slot)>) -> mir::Value {
        let site = self.site(self.pc);
        let facts = &self.s.ctx.facts;
        // Resolved for the site that entered this copy where the analysis
        // has it per entry (bbv's `seg_entry_site`).
        let per_entry = self.s.ictx.entry.and_then(|e| facts.apply_targets_in.get(&(e, site)));
        let sids: Vec<ScriptId> = match per_entry.or_else(|| facts.apply_targets.get(&site)) {
            Some(&k) => vec![k],
            None => facts.apply_target_sets.get(&site).cloned().unwrap_or_default(),
        };
        let helper = (Opcode::ApplyFwd, vec![vals[0], vals[1], vals[2]]);
        // A target reading its actuals would need this frame's count. A
        // `this` under construction (a wrapper constructor's forward to its
        // `initialize`): targets built for it, as `call_forward`'s.
        let tc = this_ctor.map(|(c, _)| c);
        let build = |s: &Shape<'a>, k, ictx| s.callee_ctx(k, &[], tc, ictx).filter(|c| !c.reads_actuals);
        let Some(targets) = self.admit(&sids, false, &build) else {
            return self.js(helper.0, helper.1, MType::VAL_TOP);
        };
        let raw = this_ctor.map(|(_, x)| self.ctor_pass(x, vals[2]));
        // Arms with fences meet at `join`: `Obj` slots go in as `ObjHint`.
        // Without one (both arms keep), they keep their facts.
        if targets.iter().any(|(_, c)| c.fenced) || !self.keepable(1) {
            self.demote_objs();
        }
        let join = self.new_block();
        let result = self.f.add_param(join, MType::VAL_TOP);
        let (fast, slow) = (self.new_block(), self.new_block());
        let is_apply = self.inst(
            Opcode::JsIsBuiltin(crate::wasm::translate::BC_FUN_APPLY),
            vec![vals[0]],
            Some(MType::Bool),
        );
        self.term(Opcode::Br, vec![is_apply], vec![Self::goto(fast), Self::goto(slow)]);
        self.at(fast);
        let n = targets.iter().map(|(_, c)| c.f.frame.formals).max().unwrap_or(0);
        let mut call = vec![vals[1], vals[2]];
        for k in 0..n {
            call.push(self.inst(Opcode::ActualArgOr(k), vec![], Some(MType::VAL_TOP)));
        }
        let r = self.inline_call_this(&targets, &call, Some(helper.clone()), raw);
        if raw.is_some() {
            self.ctor_after(&targets, vals[2]);
        }
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(r)],
            }],
        );
        self.at(slow);
        let r = self.js(helper.0, helper.1, MType::VAL_TOP);
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(r)],
            }],
        );
        self.at(join);
        result
    }

    /// `target.call(thisArg, args…)` at a site whose target the analysis
    /// resolved (`apply_targets`, `apply_target_sets`), operands `call,
    /// target, thisArg, args…`: with the `.call` the pristine builtin, the
    /// targets are inlined with `thisArg` as their `this` (a delegating
    /// constructor's `Super.call(this, …)`), built knowing the closures
    /// `fns` the call passes; any other target, or another `.call`, calls
    /// generically. `None` where nothing can be inlined.
    fn call_forward(
        &mut self,
        vals: &[mir::Value],
        fns: &[Option<ScriptId>],
        this_ctor: Option<((u32, u32, bool), Slot, mir::Value)>,
    ) -> Option<mir::Value> {
        if !CALL_FWD {
            return None;
        }
        let site = self.site(self.pc);
        let facts = &self.s.ctx.facts;
        if facts.apply_sites.get(&site) != Some(&crate::facts::CallForm::Call) {
            return None;
        }
        let sids: Vec<ScriptId> = match facts.apply_targets.get(&site) {
            Some(&k) => vec![k],
            None => facts.apply_target_sets.get(&site).cloned().unwrap_or_default(),
        };
        let tc = this_ctor.map(|(c, ..)| c);
        let targets = self.admit(&sids, false, &|s, k, ictx| s.callee_ctx(k, fns, tc, ictx))?;
        let raw = this_ctor.map(|(_, x, boxed)| self.ctor_pass(x, boxed));
        let generic = (Opcode::Call, vals.to_vec());
        // Arms with fences meet at `join`: `Obj` slots go in as `ObjHint`.
        if targets.iter().any(|(_, c)| c.fenced) || !self.keepable(1) {
            self.demote_objs();
        }
        let join = self.new_block();
        let result = self.f.add_param(join, MType::VAL_TOP);
        let (fast, slow) = (self.new_block(), self.new_block());
        let is_call = self.inst(
            Opcode::JsIsBuiltin(crate::wasm::translate::BC_FUN_CALL),
            vec![vals[0]],
            Some(MType::Bool),
        );
        self.term(Opcode::Br, vec![is_call], vec![Self::goto(fast), Self::goto(slow)]);
        self.at(fast);
        let r = self.inline_call_this(&targets, &vals[1..], Some(generic.clone()), raw);
        if raw.is_some() {
            self.ctor_after(&targets, vals[2]);
        }
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(r)],
            }],
        );
        self.at(slow);
        let r = self.js(generic.0, generic.1, MType::VAL_TOP);
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: join,
                args: vec![EdgeArg::Value(r)],
            }],
        );
        self.at(join);
        Some(result)
    }

    /// A generic op: both success edges continue with its output (of type
    /// `out`); an exception goes to the op's throw block.
    fn js(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        if let Some(r) = self.js_keep(op, args.clone(), Some(out), None) {
            return r.unwrap();
        }
        self.js_fence(op, args, out)
    }

    /// A generic op whose both success edges continue (a fence).
    fn js_fence(&mut self, op: Opcode, args: Vec<mir::Value>, out: MType) -> mir::Value {
        let ok = self.new_block();
        let p = self.f.add_param(ok, out);
        let err = self.exit_block(true);
        let e = Edge {
            block: ok,
            args: vec![EdgeArg::Out(0)],
        };
        self.term(op, args, vec![e.clone(), e, Self::goto(err)]);
        self.at(ok);
        p
    }

    // --- control flow ----------------------------------------------------------

    /// The MIR block for leader `pc`, entered from `from` (a pc, or `None`
    /// for the entry root): a loop's preheader when the edge comes from
    /// outside the loop.
    fn block_for(&mut self, pc: Pc, from: Option<Pc>) -> Option<mir::Block> {
        let tys = self.entry_types.get(&pc)?.clone();
        let make = |r: &mut Self| {
            let b = r.new_block();
            for t in tys.iter().filter(|&&t| t != Ty::Dead) {
                r.f.add_param(b, t.mir());
            }
            b
        };
        let h = match self.blocks.get(&pc) {
            Some(&b) => b,
            None => {
                let b = make(self);
                self.blocks.insert(pc, b);
                b
            }
        };
        let Some(&end) = self.s.loops.get(&pc) else {
            return Some(h);
        };
        if from.is_some_and(|f| f >= pc && f < end) {
            return Some(h);
        }
        if let Some(&p) = self.preheaders.get(&pc) {
            return Some(p);
        }
        let p = make(self);
        self.preheaders.insert(pc, p);
        let depth = u32::try_from(tys.len() - self.frame_len()).unwrap();
        self.f.frame.depths.entry(pc).or_insert(depth);
        self.f.loops.push(LoopDecl {
            header: h,
            preheader: p,
            entry: Some(mir::func::LoopEntry {
                pc,
                slots: tys.iter().map(|&t| t != Ty::Dead).collect(),
                state: vec![],
            }),
        });
        let saved = (self.cur, self.live);
        self.at(p);
        let args = self.f.blocks[p]
            .params
            .iter()
            .map(|&v| EdgeArg::Value(v))
            .collect();
        self.term(Opcode::Jump, vec![], vec![Edge { block: h, args }]);
        (self.cur, self.live) = saved;
        Some(p)
    }

    /// The edge from the current point (the op at `from`) to leader `to`.
    /// - `to` not entered yet (a forward edge): a trampoline that `to`'s
    ///   entry fills in.
    /// - `to` entered (a loop's back edge): convert the frame to its entry
    ///   types. `None` when they are narrower than the frame's: the run is
    ///   then not the last (`widen`), and the edge is left out.
    fn edge_to(&mut self, to: Pc, from: Option<Pc>) -> Option<Edge> {
        // A formal a mapped `arguments` aliases is written through the
        // frame (`ArgsMappedSet`), which leaves its slot dead on this path;
        // where the target takes a value for it, the current one, read
        // back (else the target's entry types never settle).
        if self.mapped() {
            if let Some(want) = self.entry_types.get(&to).cloned() {
                for n in 0..self.s.nargs {
                    let ix = self.arg_ix(n);
                    if self.st.get(ix).is_some_and(|x| x.ty == Ty::Dead) && want.get(ix).is_some_and(|&t| t != Ty::Dead) {
                        let v = self.inst(Opcode::ArgsMapped(n), vec![], Some(MType::VAL_TOP));
                        self.st[ix] = Slot {
                            v,
                            ty: Ty::Val(TagSet::ALL),
                        };
                    }
                }
            }
        }
        let tys: Vec<Ty> = self.st.iter().map(|x| x.ty).collect();
        match self.out.get_mut(&to) {
            Some(o) => {
                for (a, b) in o.iter_mut().zip(&tys) {
                    *a = a.join(*b);
                }
            }
            None => {
                self.out.insert(to, tys.clone());
            }
        }
        let Some(want) = self.entry_types.get(&to).cloned() else {
            let t = self.new_block();
            let args = self
                .st
                .clone()
                .iter()
                .filter(|x| x.ty != Ty::Dead)
                .map(|x| {
                    self.f.add_param(t, x.ty.mir());
                    EdgeArg::Value(x.v)
                })
                .collect();
            self.pending.entry(to).or_default().push((t, tys, from));
            return Some(Edge { block: t, args });
        };
        if want.len() != tys.len() || !tys.iter().zip(&want).all(|(a, b)| a.fits(*b)) {
            self.widen = true;
            return None;
        }
        if HOIST_NATIVE && self.s.loops.contains_key(&to) {
            for (i, (&a, &b)) in tys.iter().zip(&want).enumerate() {
                if matches!(a, Ty::Native | Ty::Ta(_)) && matches!(b, Ty::Val(t) if TagSet::OBJECT.subset_of(t)) {
                    self.hoist_req.insert((to, i), a);
                }
            }
        }
        let block = self.block_for(to, from)?;
        let st = self.st.clone();
        let args = st
            .iter()
            .zip(&want)
            .enumerate()
            .filter(|(_, (_, &t))| t != Ty::Dead)
            .map(|(_, (&x, &t))| EdgeArg::Value(self.convert(x, t)))
            .collect();
        Some(Edge { block, args })
    }

    fn jump_to(&mut self, to: Pc, from: Option<Pc>) {
        match self.edge_to(to, from) {
            Some(e) => self.term(Opcode::Jump, vec![], vec![e]),
            None => self.term(Opcode::Unreachable, vec![], vec![]),
        }
    }

    /// Narrowing from a dynamic test (§4.4): a test of whether `x`'s tag
    /// is in `tags` (negated if `negate`) that the next op branches on,
    /// fused with that branch into one `guard.tags` whose ok edge carries
    /// `x` narrowed to the branch it takes, every slot holding it
    /// replaced there, and whose fail edge is the other branch. False
    /// (nothing emitted) unless the next op is a `JumpIfTrue` or
    /// `JumpIfFalse` that no other edge reaches and `x` is a boxed value
    /// the test can narrow.
    fn fuse_test(&mut self, x: Slot, tags: TagSet, negate: bool) -> bool {
        let Ty::Val(have) = x.ty else { return false };
        let narrowed = have.intersect(tags);
        if !NARROW_TESTS || narrowed.is_empty() || narrowed == have {
            return false;
        }
        let Some(bpc) = self.next_pc else { return false };
        if self.s.leaders.contains(&bpc) {
            return false;
        }
        let Some(bop) = self.s.op_at(bpc) else { return false };
        if !matches!(bop, JSOp::JumpIfTrue | JSOp::JumpIfFalse) {
            return false;
        }
        let off = self.s.imms(bpc).next_int32().unwrap();
        let (taken, fall) = (bpc.branch(off), bpc + bop.len());
        // Where control goes when the tag is in `tags`, and when not.
        let cond_true = if bop == JSOp::JumpIfTrue { taken } else { fall };
        let cond_false = if bop == JSOp::JumpIfTrue { fall } else { taken };
        let (inside, outside) = if negate { (cond_false, cond_true) } else { (cond_true, cond_false) };
        // Narrow the side that learns something: a value that is not null
        // or undefined, rather than one that is.
        let nullish = TagSet::prims(PRIM_NULL | PRIM_UNDEFINED);
        let (tags, narrowed, inside, outside) = if tags.subset_of(nullish) {
            let rest = have.minus(tags);
            (rest, rest, outside, inside)
        } else {
            (tags, narrowed, inside, outside)
        };
        let v = self.boxed(x);
        let (nb, fb) = (self.new_block(), self.new_block());
        let nv = self.f.add_param(nb, MType::val(narrowed));
        self.term(
            Opcode::GuardTags(tags),
            vec![v],
            vec![
                Edge {
                    block: nb,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(fb),
            ],
        );
        self.at(nb);
        let saved = self.st.clone();
        for y in self.st.iter_mut().filter(|y| y.v == x.v) {
            *y = Slot {
                v: nv,
                ty: Ty::Val(narrowed),
            };
        }
        self.jump_to(inside, Some(bpc));
        self.st = saved;
        self.at(fb);
        self.jump_to(outside, Some(bpc));
        true
    }

    /// Branch on raw bool `c` to leaders `then` and `els`.
    fn branch(&mut self, c: mir::Value, then: Pc, els: Pc) {
        let from = Some(self.pc);
        match (self.edge_to(then, from), self.edge_to(els, from)) {
            (Some(t), Some(e)) => self.term(Opcode::Br, vec![c], vec![t, e]),
            _ => self.term(Opcode::Unreachable, vec![], vec![]),
        }
    }

    /// ToBoolean of `x` as a raw bool.
    fn truthy(&mut self, x: Slot) -> mir::Value {
        match x.ty {
            Ty::Dead => unreachable!("a dead slot is never read"),
            Ty::Bool => x.v,
            // A closure never emulates `undefined`.
            Ty::Obj(..) | Ty::ObjHint(_) | Ty::Ctor(..) | Ty::Native | Ty::Ta(_) | Ty::Fn(_) => {
                self.inst(Opcode::ConstBool(true), vec![], Some(MType::Bool))
            }
            Ty::I32 => {
                let z = self.const_i32(0);
                self.inst(
                    Opcode::Cmp(NumRepr::I32, Cc::Ne),
                    vec![x.v, z],
                    Some(MType::Bool),
                )
            }
            // Neither ±0 nor NaN: |x| > 0.
            Ty::F64 => {
                let a = self.inst(Opcode::Math(MathFn::Abs), vec![x.v], Some(MType::F64_TOP));
                let z = self.const_f64(0.0);
                self.inst(
                    Opcode::Cmp(NumRepr::F64, Cc::Gt),
                    vec![a, z],
                    Some(MType::Bool),
                )
            }
            // A boolean (a generic compare's or `instanceof`'s): its bit.
            Ty::Val(t) if t.is_nonempty_subset_of(TagSet::BOOLEAN) => {
                self.inst(Opcode::Unbox(UnboxKind::Bool), vec![x.v], Some(MType::Bool))
            }
            Ty::Val(_) => self.inst(Opcode::JsToBool, vec![x.v], Some(MType::Bool)),
        }
    }

    /// Whether boxed `x`'s tag is in `tags`, as a raw bool: a `guard.tags`
    /// whose failure edge merges back rather than exiting.
    fn tag_test(&mut self, x: mir::Value, tags: TagSet) -> mir::Value {
        let (t, e, j) = (self.new_block(), self.new_block(), self.new_block());
        let p = self.f.add_param(j, MType::Bool);
        self.f.add_param(t, MType::val(tags));
        self.term(
            Opcode::GuardTags(tags),
            vec![x],
            vec![
                Edge {
                    block: t,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(e),
            ],
        );
        for (b, val) in [(t, true), (e, false)] {
            self.at(b);
            let k = self.inst(Opcode::ConstBool(val), vec![], Some(MType::Bool));
            self.term(
                Opcode::Jump,
                vec![],
                vec![Edge {
                    block: j,
                    args: vec![EdgeArg::Value(k)],
                }],
            );
        }
        self.at(j);
        p
    }

    /// `!c` for a raw bool: a diamond.
    /// `x == null`: null or undefined, or an object that emulates
    /// `undefined`.
    fn loose_nullish(&mut self, x: Slot) -> mir::Value {
        let tags = x.ty.tags();
        let nullish = TagSet::prims(PRIM_NULL | PRIM_UNDEFINED);
        let v = self.boxed(x);
        if tags.intersect(TagSet::OBJECT).is_empty() {
            return self.tag_test(v, nullish);
        }
        let (o, prim, j) = (self.new_block(), self.new_block(), self.new_block());
        let r = self.f.add_param(j, MType::Bool);
        let ob = self.f.add_param(o, MType::OBJ_TOP);
        self.term(
            Opcode::GuardUnbox(UnboxKind::Obj),
            vec![v],
            vec![
                Edge {
                    block: o,
                    args: vec![EdgeArg::Out(0)],
                },
                Self::goto(prim),
            ],
        );
        self.at(o);
        let e = self.inst(Opcode::ObjEmulatesUndef, vec![ob], Some(MType::Bool));
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: j,
                args: vec![EdgeArg::Value(e)],
            }],
        );
        self.at(prim);
        let t = self.tag_test(v, nullish);
        self.term(
            Opcode::Jump,
            vec![],
            vec![Edge {
                block: j,
                args: vec![EdgeArg::Value(t)],
            }],
        );
        self.at(j);
        r
    }

    fn not(&mut self, c: mir::Value) -> mir::Value {
        let (t, e, j) = (self.new_block(), self.new_block(), self.new_block());
        let p = self.f.add_param(j, MType::Bool);
        self.term(Opcode::Br, vec![c], vec![Self::goto(t), Self::goto(e)]);
        for (b, val) in [(t, false), (e, true)] {
            self.at(b);
            let k = self.inst(Opcode::ConstBool(val), vec![], Some(MType::Bool));
            self.term(
                Opcode::Jump,
                vec![],
                vec![Edge {
                    block: j,
                    args: vec![EdgeArg::Value(k)],
                }],
            );
        }
        self.at(j);
        p
    }

    // --- the stack -------------------------------------------------------------

    fn push(&mut self, v: mir::Value, ty: Ty) {
        self.st.push(Slot { v, ty });
    }

    fn pop(&mut self) -> Slot {
        self.st.pop().expect("stack underflow")
    }

    fn top(&self) -> Slot {
        *self.st.last().expect("empty stack")
    }

    /// Slots before the operand stack: `this`, formals, locals, rval.
    fn frame_len(&self) -> usize {
        (2 + self.s.nargs + self.s.nlocals) as usize
    }

    /// Whether frame slot `ix` is written through: only the formals of a
    /// mapped `arguments`, which aliases them. Its frame copy then always
    /// holds its value, so exits leave it (§5.1). Everything else stays in
    /// its own representation, and exits write it.
    fn write_through(&self, ix: usize) -> bool {
        self.mapped() && ix >= 1 && ix <= self.s.nargs as usize
    }

    /// Assign frame slot `ix`, writing it through to the frame.
    fn set_frame_slot(&mut self, ix: usize, x: Slot) {
        if self.this_vals.contains(&x.v) {
            self.this_slots.insert(ix);
        } else {
            self.this_slots.remove(&ix);
        }
        match self.val_cls.get(&x.v) {
            Some(&c) => self.slot_cls.insert(ix, c),
            None => self.slot_cls.remove(&ix),
        };
        if self.args_placeholder == Some(x.v) {
            self.args_local = Some(ix);
        }
        if x.ty != Ty::Dead && self.write_through(ix) {
            self.inst(Opcode::FrameStore(u32::try_from(ix).unwrap()), vec![x.v], None);
        }
        self.st[ix] = x;
    }

    fn arg_ix(&self, n: u32) -> usize {
        1 + n as usize
    }

    fn local_ix(&self, n: u32) -> usize {
        1 + (self.s.nargs + n) as usize
    }

    fn rval_ix(&self) -> usize {
        1 + (self.s.nargs + self.s.nlocals) as usize
    }

    // --- the walk ---------------------------------------------------------------

    fn build(&mut self) -> R<()> {
        self.entry();
        let ops = self.s.ops.clone();
        let mut i = 0;
        while i < ops.len() {
            let Op { pc, op } = ops[i];
            if self.s.leaders.contains(&pc) {
                if self.live {
                    let from = if i > 0 { Some(ops[i - 1].pc) } else { None };
                    self.jump_to(pc, from);
                }
                if let Some(tys) = self.enter(pc) {
                    let b = self.block_for(pc, Some(pc)).unwrap();
                    let mut params = self.f.blocks[b].params.clone().into_iter();
                    self.st = tys
                        .iter()
                        .map(|&ty| match ty {
                            Ty::Dead => Slot::dead(),
                            ty => Slot {
                                v: params.next().unwrap(),
                                ty,
                            },
                        })
                        .collect();
                    self.at(b);
                }
            }
            if self.live {
                if self.s.depths.at(pc)
                    != Some(u32::try_from(self.st.len() - self.frame_len()).unwrap())
                {
                    return Err(format!("BUG: stack depth at {pc} disagrees"));
                }
                self.pc = pc;
                self.pre = self.st.clone();
                self.renames.clear();
                self.exit_blk = None;
                self.throw_blk = None;
                self.op(op)?;
                if self.live {
                    self.local_restamp(pc);
                    if op == JSOp::FunctionThis {
                        let v = self.top().v;
                        self.this_vals.insert(v);
                    }
                    // A property read's value class, hinted (bbv's
                    // `attach_likely_cls`).
                    if matches!(op, JSOp::GetProp | JSOp::GetElem) {
                        if let Some(&(lo, hi)) = self.s.ctx.facts.field_cls_sites.get(&self.site(pc)) {
                            if lo == hi {
                                let v = self.top().v;
                                self.val_cls.insert(v, lo.get());
                            }
                        }
                    }
                }
            }
            i += 1;
        }
        if self.live {
            self.term(Opcode::Unreachable, vec![], vec![]);
        }
        let headers: Vec<Pc> = self.preheaders.keys().copied().collect();
        for h in headers {
            if self.wants_onramp(h) {
                self.onramp_root(h);
            }
        }
        Ok(())
    }

    /// The onramp-root policy (`docs/BASELINE.md` §7): every outermost
    /// loop gets a root, which needs no code duplication. An inner loop's
    /// root side-enters every loop around it, which waffle's reducifier
    /// pays for by duplicating code, so it gets one only when its
    /// outermost enclosing loop is small.
    fn wants_onramp(&self, h: Pc) -> bool {
        let outer = self
            .s
            .loops
            .iter()
            .filter(|&(&hh, &e)| hh < h && h < e)
            .map(|(&hh, &e)| e.get() - hh.get())
            .max();
        match outer {
            None => true,
            // Inlined callees make the loops around it bigger than their
            // bytecode says, and the duplication with them.
            Some(_) if !self.f.inline_frames.is_empty() => false,
            Some(len) => len <= self.s.ctx.opts.inner_onramp_bytes(),
        }
    }

    /// The onramp root `O` for loop header `h` (§5.2): the frame at `h`,
    /// all `Val(⊤)`, guarded up to the preheader's param types. On
    /// success it enters the preheader; on failure it re-deopts at `h`
    /// with its own params.
    fn onramp_root(&mut self, h: Pc) {
        let tys = self.entry_types[&h].clone();
        let p = self.preheaders[&h];
        let o = self.new_block();
        self.f.roots.push(Root {
            kind: RootKind::Onramp(h),
            block: o,
        });
        let params: Vec<mir::Value> = tys
            .iter()
            .map(|_| self.f.add_param(o, MType::VAL_TOP))
            .collect();
        let depth = tys.len() - self.frame_len();
        self.f.frame.depths.insert(h, u32::try_from(depth).unwrap());
        let fail = self.new_block();
        self.at(fail);
        let (nargs, nlocals) = (self.s.nargs, self.s.nlocals);
        self.term(
            Opcode::Exit {
                pc: h,
                nargs,
                nlocals,
            },
            params.clone(),
            vec![],
        );
        self.at(o);
        let args = self.guard_to(&params, &tys, fail).into_iter().map(EdgeArg::Value).collect();
        self.term(Opcode::Jump, vec![], vec![Edge { block: p, args }]);
    }

    /// The `Resume` root for resume index `index` at landing `pc`: the
    /// frame as the resume restored it, all `Val(⊤)`, guarded up to the
    /// types the slots had at the yield (`before`, whose top `popped`
    /// values the yield consumed; the landing's three resume values are
    /// `Val(⊤)`). The walk goes on from there; a miss exits at the landing.
    fn resume_root(&mut self, index: u32, pc: Pc, before: &[Slot], popped: usize) -> R<()> {
        let fl = self.frame_len();
        let depth = self.s.depths.at(pc).ok_or("resume landing without a stack depth")? as usize;
        let saved = before.len() - fl - popped;
        if depth != saved + 3 {
            return Err(format!("BUG: resume landing {pc} at depth {depth}, not {}", saved + 3));
        }
        let live = self.s.live.get(&pc).cloned();
        let mut tys: Vec<Ty> = before[..fl + saved].iter().map(|x| x.ty).collect();
        for (i, t) in tys.iter_mut().enumerate().take(fl) {
            if live.as_ref().is_some_and(|l| i < l.len() && !l[i]) {
                *t = Ty::Dead;
            }
        }
        tys.extend([Ty::Val(TagSet::ALL); 3]);
        let o = self.new_block();
        self.f.roots.push(Root {
            kind: RootKind::Resume { index, pc },
            block: o,
        });
        let params: Vec<mir::Value> = tys.iter().map(|_| self.f.add_param(o, MType::VAL_TOP)).collect();
        self.f.frame.depths.insert(pc, u32::try_from(depth).unwrap());
        let fail = self.new_block();
        self.at(fail);
        let (nargs, nlocals) = (self.s.nargs, self.s.nlocals);
        self.term(Opcode::Exit { pc, nargs, nlocals }, params.clone(), vec![]);
        self.at(o);
        let mut vals = self.guard_to(&params, &tys, fail).into_iter();
        self.st = tys
            .iter()
            .map(|&ty| match ty {
                Ty::Dead => Slot::dead(),
                ty => Slot {
                    v: vals.next().unwrap(),
                    ty,
                },
            })
            .collect();
        self.live = true;
        Ok(())
    }

    /// Guard root params `params` (all `Val(⊤)`, the frame) up to slot
    /// types `tys`, exiting to `fail` on a miss: one value per slot that is
    /// not dead, with `cur` at the block past the last guard.
    fn guard_to(&mut self, params: &[mir::Value], tys: &[Ty], fail: mir::Block) -> Vec<mir::Value> {
        let mut args = vec![];
        for (&v, &t) in params.iter().zip(tys) {
            let op = match t {
                Ty::Dead => continue,
                Ty::I32 => Some(Opcode::GuardUnbox(UnboxKind::I32)),
                Ty::F64 => Some(Opcode::GuardUnbox(UnboxKind::F64Num)),
                Ty::Bool => Some(Opcode::GuardUnbox(UnboxKind::Bool)),
                Ty::Val(tags) if tags == TagSet::ALL => None,
                Ty::Val(tags) => Some(Opcode::GuardTags(tags)),
                Ty::ObjHint(_) => Some(Opcode::GuardUnbox(UnboxKind::Obj)),
                Ty::Fn(k) => {
                    // An object, a function of script `k`; passed boxed.
                    let obj = TagSet::OBJECT;
                    let (b1, b2, b3) = (self.new_block(), self.new_block(), self.new_block());
                    let bv = self.f.add_param(b1, MType::val(obj));
                    self.term(
                        Opcode::GuardTags(obj),
                        vec![v],
                        vec![
                            Edge {
                                block: b1,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(fail),
                        ],
                    );
                    self.at(b1);
                    let o = self.f.add_param(b2, MType::OBJ_TOP);
                    self.term(
                        Opcode::GuardUnbox(UnboxKind::Obj),
                        vec![bv],
                        vec![
                            Edge {
                                block: b2,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(fail),
                        ],
                    );
                    self.at(b2);
                    self.f.add_param(b3, MType::Obj(ObjInfo::kind(ObjKind::Function(Some(k)))));
                    // The guard compares against the script's address.
                    if let crate::source::SourceObject::Script(ks) =
                        self.s.ctx.source.object(crate::source::SourceObjectId::new(k.get()))
                    {
                        self.mm.script_addrs.insert(k, ks.addr);
                    }
                    self.term(
                        Opcode::GuardScript(k),
                        vec![o],
                        vec![
                            Edge {
                                block: b3,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(fail),
                        ],
                    );
                    self.at(b3);
                    args.push(bv);
                    continue;
                }
                Ty::Native | Ty::Ta(_) => {
                    let o = self.guard_narrow(v, t, fail);
                    args.push(o);
                    continue;
                }
                Ty::Obj(keys, types, slots) => {
                    // Unbox, then the layout.
                    let ok = self.new_block();
                    let o = self.f.add_param(ok, MType::OBJ_TOP);
                    self.term(
                        Opcode::GuardUnbox(UnboxKind::Obj),
                        vec![v],
                        vec![
                            Edge {
                                block: ok,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(fail),
                        ],
                    );
                    self.at(ok);
                    let ok = self.new_block();
                    let out = self.f.add_param(ok, t.mir());
                    self.term(
                        Opcode::GuardLayout { keys, types, slots },
                        vec![o],
                        vec![
                            Edge {
                                block: ok,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(fail),
                        ],
                    );
                    self.at(ok);
                    args.push(out);
                    continue;
                }
                Ty::Ctor(key, n, types) => {
                    // Unbox, then the construction state (§2.3).
                    let ok = self.new_block();
                    let o = self.f.add_param(ok, MType::OBJ_TOP);
                    self.term(
                        Opcode::GuardUnbox(UnboxKind::Obj),
                        vec![v],
                        vec![
                            Edge {
                                block: ok,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(fail),
                        ],
                    );
                    self.at(ok);
                    let ok = self.new_block();
                    let out = self.f.add_param(ok, t.mir());
                    self.term(
                        Opcode::GuardCtor {
                            key: crate::ids::LayoutKey::new(key),
                            n,
                            types,
                        },
                        vec![o],
                        vec![
                            Edge {
                                block: ok,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(fail),
                        ],
                    );
                    self.at(ok);
                    args.push(out);
                    continue;
                }
            };
            let Some(op) = op else {
                args.push(v);
                continue;
            };
            let ok = self.new_block();
            let out = self.f.add_param(ok, t.mir());
            self.term(
                op,
                vec![v],
                vec![
                    Edge {
                        block: ok,
                        args: vec![EdgeArg::Out(0)],
                    },
                    Self::goto(fail),
                ],
            );
            self.at(ok);
            args.push(out);
        }
        args
    }

    /// Enter leader `pc`: its entry types are the table's (what back edges
    /// brought in earlier runs) joined with every forward edge of this run.
    /// Fills the pending trampolines. `None` if nothing reaches it.
    fn enter(&mut self, pc: Pc) -> Option<Vec<Ty>> {
        let pending = self.pending.remove(&pc).unwrap_or_default();
        let mut tys = self.table.get(&pc).cloned();
        for (_, t, _) in &pending {
            tys = Some(match tys {
                None => t.clone(),
                Some(mut a) => {
                    for (x, y) in a.iter_mut().zip(t) {
                        *x = x.join(*y);
                    }
                    a
                }
            });
        }
        let mut tys = tys?;
        self.s.depths.at(pc)?;
        // Slots guarded on the way into the loop (§10.2): native objects in
        // the loop, however they came in.
        for (i, t) in tys.iter_mut().enumerate() {
            if let Some(&n) = self.hoist.get(&(pc, i)) {
                if matches!(*t, Ty::Val(u) if TagSet::OBJECT.subset_of(u)) {
                    *t = n;
                }
            }
        }
        // Slots dead here take no param.
        let live = &self.s.live[&pc];
        for (t, &l) in tys.iter_mut().zip(live) {
            if !l {
                *t = Ty::Dead;
            }
        }
        self.entry_types.insert(pc, tys.clone());
        let saved = (self.cur, self.live);
        for (t, ttys, from) in pending {
            let target = self.block_for(pc, from).unwrap();
            self.at(t);
            let params = self.f.blocks[t].params.clone();
            let mut params = params.into_iter();
            // The edge's frame, for a hoisted guard's exit (at `pc`,
            // before the loop runs).
            let frame: Vec<Slot> = {
                let mut ps = self.f.blocks[t].params.clone().into_iter();
                ttys.iter()
                    .map(|&ty| match ty {
                        Ty::Dead => Slot::dead(),
                        ty => Slot {
                            v: ps.next().unwrap(),
                            ty,
                        },
                    })
                    .collect()
            };
            let mut exit_b = None;
            let mut args = vec![];
            for (&from_ty, &to_ty) in ttys.iter().zip(&tys) {
                let v = if from_ty == Ty::Dead {
                    None
                } else {
                    params.next()
                };
                if to_ty == Ty::Dead {
                    continue;
                }
                let v = v.expect("a slot live at a block is live on each edge into it");
                if matches!((from_ty, to_ty), (Ty::Val(_), Ty::Native | Ty::Ta(_))) {
                    let fail = *exit_b.get_or_insert_with(|| {
                        let here = self.cur;
                        let b = self.new_block();
                        self.at(b);
                        let ops = self.exit_operands(pc, &frame);
                        let eop = self.exit_op(pc, false);
                        self.term(eop, ops, vec![]);
                        self.at(here);
                        b
                    });
                    let o = self.guard_narrow(v, to_ty, fail);
                    args.push(EdgeArg::Value(o));
                    continue;
                }
                args.push(EdgeArg::Value(self.convert(Slot { v, ty: from_ty }, to_ty)));
            }
            self.term(
                Opcode::Jump,
                vec![],
                vec![Edge {
                    block: target,
                    args,
                }],
            );
        }
        (self.cur, self.live) = saved;
        Some(tys)
    }

    /// The entry root: callee, `this`, formals. Formals with a claim are
    /// guarded at their definition; locals and rval start undefined.
    fn entry(&mut self) {
        let b0 = self.cur;
        self.f.roots.push(Root {
            kind: RootKind::Entry,
            block: b0,
        });
        let callee = MType::Obj(ObjInfo::kind(ObjKind::Function(Some(self.s.sid))));
        self.f.add_param(b0, callee);
        let all = Ty::Val(TagSet::ALL);
        // An object under construction the inlining `new` or call passes.
        let this_ty = match self.s.this_ctor {
            Some((k, n, t)) => Ty::Ctor(k, n, t),
            None => all,
        };
        let this = self.f.add_param(b0, this_ty.mir());
        self.st.push(Slot { v: this, ty: this_ty });
        for i in 0..self.s.nargs {
            // A closure the inlining call passes (`formal_fns`).
            let ty = match self.s.formal_fns.get(i as usize) {
                Some(&Some(k)) => Ty::Fn(k),
                _ => all,
            };
            let v = self.f.add_param(b0, ty.mir());
            self.st.push(Slot { v, ty });
            // The formal's advisory class (bbv's lazy tier: unguarded
            // until a typed access checks it).
            let key = (self.s.sid, ArgIndex::new(i + 1));
            if let Some(&(lo, hi)) = self.s.ctx.facts.arg_cls.get(&key) {
                if lo == hi && !self.s.script.has_mapped_args {
                    self.slot_cls.insert(self.st.len() - 1, lo.get());
                }
            }
        }
        let undef = self.const_val(ConstVal::Undefined);
        let uty = Ty::Val(TagSet::prims(PRIM_UNDEFINED));
        for _ in 0..=self.s.nlocals {
            self.st.push(Slot { v: undef, ty: uty });
        }
        self.pc = Pc::new(0);
        self.pre = self.st.clone();
        if self.mapped() {
            // First, before anything can exit: baseline, resumed, reads
            // the formals through it.
            self.js_static(Opcode::ArgsObject, vec![], MType::val(TagSet::OBJECT));
        }
        for i in 0..self.s.nargs {
            if self.mapped() {
                break;
            }
            let (op, ty) = match self.s.arg_claim(i) {
                Ty::I32 => (Opcode::GuardUnbox(UnboxKind::I32), Ty::I32),
                Ty::F64 => (Opcode::GuardUnbox(UnboxKind::F64Num), Ty::F64),
                _ => continue,
            };
            let ix = self.arg_ix(i);
            let v = self.guard(op, vec![self.st[ix].v], ty.mir());
            self.st[ix] = Slot { v, ty };
        }
        self.jump_to(Pc::new(0), None);
    }

    fn op(&mut self, op: JSOp) -> R<()> {
        use JSOp::*;
        let pc = self.pc;
        self.next_pc = Some(pc + op.len());
        self.ta_poly_site = false;
        self.store_mask = None;
        let mut p = self.s.imms(pc);
        let int_ty = Ty::I32;
        match op {
            // (`DebugLeaveLexicalEnv` only matters to a debugger; so does
            // `Debugger`, a no-op with none attached, as in baseline.)
            Nop | Lineno | JumpTarget | LoopHead | NopDestructuring | NopIsAssignOp
            | DebugLeaveLexicalEnv | Debugger => {}
            // A try block's code is ordinary code: a throw in it exits
            // (`exit.throw`) and baseline takes the pc's handler. The catch
            // code, entered only by a throw, is never reached here.
            Try | TryDestructuring => {}
            // A finally block's start: a marker. MIR runs only its normal
            // entry (a throw exits, and baseline's unwind enters it
            // throwing), whose rethrow arm is therefore baseline's too.
            Finally => {}
            ThrowWithStack => {
                let b = self.exit_block(false);
                self.term(Opcode::Jump, vec![], vec![Self::goto(b)]);
            }

            Undefined => {
                let v = self.const_val(ConstVal::Undefined);
                self.push(v, Ty::Val(TagSet::prims(PRIM_UNDEFINED)));
            }
            Null => {
                let v = self.const_val(ConstVal::Null);
                self.push(v, Ty::Val(TagSet::prims(PRIM_NULL)));
            }
            True | False => {
                let v = self.inst(Opcode::ConstBool(op == True), vec![], Some(MType::Bool));
                self.push(v, Ty::Bool);
            }
            Zero | One | Int8 | Uint16 | Uint24 | Int32 => {
                let n: i32 = match op {
                    Zero => 0,
                    One => 1,
                    Int8 => p.next_int8().unwrap().into(),
                    Uint16 => p.next_uint16().unwrap().into(),
                    Uint24 => p.next_uint24().unwrap() as i32,
                    _ => p.next_int32().unwrap(),
                };
                let v = self.const_i32(n);
                self.push(v, int_ty);
            }
            Double => {
                let x = f64::from_bits(p.next_uint64().unwrap());
                let v = self.const_f64(x);
                self.push(v, Ty::F64);
            }
            Uninitialized => {
                let v = self.const_val(ConstVal::Uninitialized);
                self.push(v, Ty::Val(TagSet::MAGIC));
            }
            Void => {
                self.pop();
                let v = self.const_val(ConstVal::Undefined);
                self.push(v, Ty::Val(TagSet::prims(PRIM_UNDEFINED)));
            }

            // --- frame ---
            GetLocal => {
                let n = p.next_uint24().unwrap();
                let ix = self.local_ix(n);
                let x = self.st[ix];
                if let Some(&c) = self.slot_cls.get(&ix) {
                    self.val_cls.insert(x.v, c);
                }
                if self.this_slots.contains(&ix) {
                    self.this_vals.insert(x.v);
                }
                self.st.push(x);
            }
            SetLocal | InitLexical => {
                let n = p.next_uint24().unwrap();
                let ix = self.local_ix(n);
                let x = self.top();
                self.set_frame_slot(ix, x);
            }
            // With an unmapped `arguments` (or none to map), a formal's
            // frame slot is the formal.
            // A mapped `arguments` object aliases the formals: they are
            // its (baseline's reads and writes too).
            GetArg if self.mapped() => {
                let n = u32::from(p.next_uint16().unwrap());
                let v = self.inst(Opcode::ArgsMapped(n), vec![], Some(MType::VAL_TOP));
                self.push(v, Ty::Val(TagSet::ALL));
            }
            GetArg | GetFrameArg => {
                let n = u32::from(p.next_uint16().unwrap());
                let ix = self.arg_ix(n);
                let x = self.st[ix];
                if let Some(&c) = self.slot_cls.get(&ix) {
                    self.val_cls.insert(x.v, c);
                }
                self.st.push(x);
            }
            ToString if RT_OPS => {
                // A string is its own ToString.
                let v = self.top();
                if !v.ty.tags().is_nonempty_subset_of(TagSet::STRING) {
                    let v = self.pop();
                    let x = self.boxed(v);
                    let r = self.js(Opcode::JsRt(RtOp::ToString), vec![x], MType::val(TagSet::STRING));
                    self.push(r, Ty::Val(TagSet::STRING));
                }
            }
            BuiltinObject if RT_OPS => {
                let kind = u32::from(p.next_uint8().unwrap());
                let r = self.js(Opcode::JsRt(RtOp::BuiltinObject(kind)), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            Symbol if RT_OPS => {
                let code = u32::from(p.next_uint8().unwrap());
                let sym = TagSet::prims(crate::opsem::PRIM_SYMBOL);
                let r = self.js(Opcode::JsRt(RtOp::Symbol(code)), vec![], MType::val(sym));
                self.push(r, Ty::Val(sym));
            }
            GetIntrinsic if RT_OPS => {
                // A realm constant, from its cell once armed (bbv's
                // `emit_get_intrinsic`).
                let a = self.atom(p.next_uint32().unwrap())?;
                let r = self.js(Opcode::JsRt(RtOp::Intrinsic(a)), vec![], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            RegExp if RT_OPS => {
                let idx = p.next_uint32().unwrap();
                let r = self.js(Opcode::JsRt(RtOp::RegExp(idx)), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            InitPropGetter | InitHiddenPropGetter | InitPropSetter | InitHiddenPropSetter if RT_OPS => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let kind = u32::from(matches!(op, InitPropSetter | InitHiddenPropSetter))
                    | (u32::from(matches!(op, InitHiddenPropGetter | InitHiddenPropSetter)) << 1);
                let f = self.pop();
                let o = self.top();
                let (x, y) = (self.boxed(o), self.boxed(f));
                self.js_void(Opcode::JsRt(RtOp::InitPropGetSet(a, kind)), vec![x, y]);
            }
            SetArg if self.mapped() => {
                let n = u32::from(p.next_uint16().unwrap());
                let x = self.top();
                let v = self.boxed(x);
                self.inst(Opcode::ArgsMappedSet(n), vec![v], None);
            }
            SetArg => {
                let n = u32::from(p.next_uint16().unwrap());
                let ix = self.arg_ix(n);
                let x = self.top();
                self.set_frame_slot(ix, x);
            }
            GetRval => {
                let x = self.st[self.rval_ix()];
                self.st.push(x);
            }
            SetRval => {
                let x = self.pop();
                let ix = self.rval_ix();
                self.set_frame_slot(ix, x);
            }
            GetAliasedVar | GetAliasedDebugVar => {
                let hops = p.next_uint16().unwrap();
                let slot = p.next_uint24().unwrap();
                let e = self.env_at(hops);
                let v = self.inst(
                    Opcode::EnvLoad(crate::ids::EnvSlot::new(slot)),
                    vec![e],
                    Some(MType::VAL_TOP),
                );
                self.push(v, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.aliased_sites.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len(), true);
            }
            SetAliasedVar | InitAliasedLexical => {
                let hops = p.next_uint16().unwrap();
                let slot = p.next_uint24().unwrap();
                let x = self.top();
                let v = self.boxed(x);
                let e = self.env_at(hops);
                self.inst(Opcode::EnvStore(crate::ids::EnvSlot::new(slot)), vec![e, v], None);
            }
            Lambda => {
                let index = p.next_uint32().unwrap();
                let e = self.env_at(0);
                let r = self.js_static(Opcode::JsLambda(index), vec![e], MType::val(TagSet::OBJECT));
                let ty = match self.s.script.gcthings.get(index as usize) {
                    Some(&gc) if !gc.is_other() && CALL_KNOWN_FNS => match self.s.ctx.source.object(gc) {
                        // The function gcthing names its script.
                        crate::source::SourceObject::Object(o) => match o.script {
                            Some(k) => Ty::Fn(ScriptId::new(k.id())),
                            None => Ty::Val(TagSet::OBJECT),
                        },
                        crate::source::SourceObject::Script(_) => Ty::Fn(ScriptId::new(gc.id())),
                        _ => Ty::Val(TagSet::OBJECT),
                    },
                    _ => Ty::Val(TagSet::OBJECT),
                };
                self.push(r, ty);
            }
            CheckLexical | CheckAliasedLexical => {
                // The top may be the TDZ sentinel only if its type admits
                // magic; then guard it away (baseline throws on failure).
                let x = self.top();
                if let Ty::Val(t) = x.ty {
                    if t.magic {
                        let js = TagSet { magic: false, ..t };
                        if js.is_empty() {
                            // Always uninitialized: baseline throws the
                            // ReferenceError at this pc.
                            let b = self.exit_block(false);
                            self.term(Opcode::Jump, vec![], vec![Self::goto(b)]);
                            return Ok(());
                        }
                        let v = self.guard(Opcode::GuardTags(js), vec![x.v], MType::val(js));
                        self.st.pop();
                        self.push(v, Ty::Val(js));
                    }
                }
            }

            // --- stack ---
            Pop => {
                self.pop();
            }
            PopN => {
                let n = p.next_uint16().unwrap();
                for _ in 0..n {
                    self.pop();
                }
            }
            Dup => {
                let x = self.top();
                self.st.push(x);
            }
            Dup2 => {
                let n = self.st.len();
                let (a, b) = (self.st[n - 2], self.st[n - 1]);
                self.st.push(a);
                self.st.push(b);
            }
            DupAt => {
                let n = p.next_uint24().unwrap() as usize;
                let x = self.st[self.st.len() - 1 - n];
                self.st.push(x);
            }
            Swap => {
                let n = self.st.len();
                self.st.swap(n - 1, n - 2);
            }
            Pick => {
                let n = usize::from(p.next_uint8().unwrap());
                let ix = self.st.len() - 1 - n;
                let x = self.st.remove(ix);
                self.st.push(x);
            }
            Unpick => {
                let n = usize::from(p.next_uint8().unwrap());
                let x = self.pop();
                let ix = self.st.len() - n;
                self.st.insert(ix, x);
            }

            // --- arithmetic ---
            Add | Sub | Mul => {
                let b = self.pop();
                let a = self.pop();
                let arith = match op {
                    Add => ArithOp::Add,
                    Sub => ArithOp::Sub,
                    _ => ArithOp::Mul,
                };
                match (a.ty.num(), b.ty.num()) {
                    (Some(Num::I32), Some(Num::I32))
                        if arith != ArithOp::Mul && self.s.wrap_ok.contains(&pc) =>
                    {
                        // Only ToInt32 of the result is ever observed.
                        let (x, y) = (self.as_i32(a), self.as_i32(b));
                        let r = self.inst(Opcode::I32Wrap(arith), vec![x, y], Some(MType::I32_TOP));
                        self.push(r, Ty::I32);
                    }
                    (Some(Num::I32), Some(Num::I32)) => {
                        let (x, y) = (self.as_i32(a), self.as_i32(b));
                        let r = self.guard(Opcode::I32Ovf(arith), vec![x, y], MType::I32_TOP);
                        self.push(r, Ty::I32);
                    }
                    (Some(_), Some(_)) => {
                        let (x, y) = (self.as_f64(a), self.as_f64(b));
                        let fop = match arith {
                            ArithOp::Add => F64Op::Add,
                            ArithOp::Sub => F64Op::Sub,
                            ArithOp::Mul => F64Op::Mul,
                        };
                        let r = self.inst(Opcode::F64Arith(fop), vec![x, y], Some(MType::F64_TOP));
                        self.push(r, Ty::F64);
                    }
                    _ => {
                        let (x, y) = (self.boxed(a), self.boxed(b));
                        // Neither operand a BigInt or an object (whose
                        // valueOf might give one): a Number, or a TypeError.
                        // For `+`, neither a string or an object either (no
                        // concatenation) for a numeric result.
                        let free = |s: Slot, t: TagSet| s.ty.tags().intersect(t).is_empty();
                        let big = TagSet::prims(PRIM_BIGINT).union(TagSet::OBJECT);
                        let no_big = free(a, big) || free(b, big);
                        let strish = TagSet::STRING.union(TagSet::OBJECT);
                        let numeric = TagSet::prims(crate::opsem::NUM | PRIM_BIGINT);
                        let arith = if no_big { TagSet::NUMBER } else { numeric };
                        let (jop, tags) = match op {
                            Add if free(a, strish) && free(b, strish) => (Opcode::JsAdd, arith),
                            Add => (Opcode::JsAdd, numeric.union(TagSet::STRING)),
                            Sub => (Opcode::JsBinop(JsBinop::Sub), arith),
                            _ => (Opcode::JsBinop(JsBinop::Mul), arith),
                        };
                        let r = self.js(jop, vec![x, y], MType::val(tags));
                        self.push(r, Ty::Val(tags));
                    }
                }
            }
            Div => {
                let b = self.pop();
                let a = self.pop();
                if a.ty.num().is_some() && b.ty.num().is_some() {
                    let (x, y) = (self.as_f64(a), self.as_f64(b));
                    let r = self.inst(
                        Opcode::F64Arith(F64Op::Div),
                        vec![x, y],
                        Some(MType::F64_TOP),
                    );
                    self.push(r, Ty::F64);
                } else {
                    self.js_binop(JsBinop::Div, a, b);
                }
            }
            Mod | Pow => {
                let b = self.pop();
                let a = self.pop();
                let k = if op == Mod {
                    JsBinop::Mod
                } else {
                    JsBinop::Pow
                };
                self.js_binop(k, a, b);
            }
            BitAnd | BitOr | BitXor | Lsh | Rsh => {
                let b = self.pop();
                let a = self.pop();
                if a.ty.num().is_some() && b.ty.num().is_some() {
                    let (x, y) = (self.to_int32(a), self.to_int32(b));
                    let bop = match op {
                        BitAnd => BitOp::And,
                        BitOr => BitOp::Or,
                        BitXor => BitOp::Xor,
                        Lsh => BitOp::Shl,
                        _ => BitOp::Shr,
                    };
                    let r = self.inst(Opcode::I32Bit(bop), vec![x, y], Some(MType::I32_TOP));
                    self.push(r, Ty::I32);
                } else {
                    let k = match op {
                        BitAnd => JsBinop::BitAnd,
                        BitOr => JsBinop::BitOr,
                        BitXor => JsBinop::BitXor,
                        Lsh => JsBinop::Lsh,
                        _ => JsBinop::Rsh,
                    };
                    self.js_binop(k, a, b);
                }
            }
            Ursh => {
                let b = self.pop();
                let a = self.pop();
                if a.ty.num().is_some() && b.ty.num().is_some() {
                    let (x, y) = (self.to_int32(a), self.to_int32(b));
                    let t = MType::int_range(0, u32::MAX.into());
                    let r = self.inst(Opcode::I32Ushr, vec![x, y], Some(t));
                    let f = self.inst(Opcode::IntToF64, vec![r], Some(MType::F64_TOP));
                    self.push(f, Ty::F64);
                } else {
                    self.js_binop(JsBinop::Ursh, a, b);
                }
            }
            Inc | Dec => {
                let a = self.pop();
                match a.ty.num() {
                    Some(Num::I32) => {
                        let x = self.as_i32(a);
                        let one = self.const_i32(1);
                        let k = if op == Inc {
                            ArithOp::Add
                        } else {
                            ArithOp::Sub
                        };
                        let r = self.guard(Opcode::I32Ovf(k), vec![x, one], MType::I32_TOP);
                        self.push(r, Ty::I32);
                    }
                    Some(Num::F64) => {
                        let x = self.as_f64(a);
                        let one = self.const_f64(1.0);
                        let k = if op == Inc { F64Op::Add } else { F64Op::Sub };
                        let r = self.inst(Opcode::F64Arith(k), vec![x, one], Some(MType::F64_TOP));
                        self.push(r, Ty::F64);
                    }
                    None => {
                        let u = if op == Inc { JsUnop::Inc } else { JsUnop::Dec };
                        self.js_unop(u, a);
                    }
                }
            }
            Neg => {
                let a = self.pop();
                match a.ty.num() {
                    // -x as x * -1: fails on INT32_MIN and on 0 (-0).
                    Some(Num::I32) => {
                        let x = self.as_i32(a);
                        let m1 = self.const_i32(-1);
                        let r =
                            self.guard(Opcode::I32Ovf(ArithOp::Mul), vec![x, m1], MType::I32_TOP);
                        self.push(r, Ty::I32);
                    }
                    Some(Num::F64) => {
                        let x = self.as_f64(a);
                        let r = self.inst(Opcode::F64Neg, vec![x], Some(MType::F64_TOP));
                        self.push(r, Ty::F64);
                    }
                    None => self.js_unop(JsUnop::Neg, a),
                }
            }
            BitNot => {
                let a = self.pop();
                if a.ty.num().is_some() {
                    let x = self.to_int32(a);
                    let m1 = self.const_i32(-1);
                    let r = self.inst(
                        Opcode::I32Bit(BitOp::Xor),
                        vec![x, m1],
                        Some(MType::I32_TOP),
                    );
                    self.push(r, Ty::I32);
                } else {
                    self.js_unop(JsUnop::BitNot, a);
                }
            }
            Pos | ToNumeric => {
                let a = self.top();
                if a.ty.num().is_none() {
                    self.pop();
                    if op == Pos {
                        self.js_unop(JsUnop::Pos, a);
                    } else {
                        let tags = TagSet::prims(crate::opsem::NUM | PRIM_BIGINT);
                        let x = self.boxed(a);
                        let r = self.js(Opcode::JsToNumeric, vec![x], MType::val(tags));
                        self.push(r, Ty::Val(tags));
                    }
                }
            }

            // --- compares ---
            Lt | Le | Gt | Ge | Eq | Ne | StrictEq | StrictNe => {
                let b = self.pop();
                let a = self.pop();
                let (cc, jcc) = match op {
                    Lt => (Cc::Lt, JsCc::Lt),
                    Le => (Cc::Le, JsCc::Le),
                    Gt => (Cc::Gt, JsCc::Gt),
                    Ge => (Cc::Ge, JsCc::Ge),
                    Eq => (Cc::Eq, JsCc::Eq),
                    Ne => (Cc::Ne, JsCc::Ne),
                    StrictEq => (Cc::Eq, JsCc::StrictEq),
                    _ => (Cc::Ne, JsCc::StrictNe),
                };
                // Against a null or undefined constant: tag tests, which
                // run no user code (no fence), as bbv's.
                let nullish = |t: Ty| {
                    let tags = t.tags();
                    !tags.is_empty() && tags.subset_of(TagSet::prims(PRIM_NULL | PRIM_UNDEFINED))
                };
                let equality = matches!(op, Eq | Ne | StrictEq | StrictNe);
                let konst = if equality && nullish(b.ty) {
                    Some((a, b))
                } else if equality && nullish(a.ty) {
                    Some((b, a))
                } else {
                    None
                };
                if let Some((x, k)) = konst {
                    let negate = matches!(op, Ne | StrictNe);
                    let exact = if matches!(op, StrictEq | StrictNe) {
                        Some(k.ty.tags())
                    } else if x.ty.tags().intersect(TagSet::OBJECT).is_empty() {
                        Some(TagSet::prims(PRIM_NULL | PRIM_UNDEFINED))
                    } else {
                        None
                    };
                    if exact.is_some_and(|t| self.fuse_test(x, t, negate)) {
                        return Ok(());
                    }
                    let r = if matches!(op, StrictEq | StrictNe) {
                        let v = self.boxed(x);
                        self.tag_test(v, k.ty.tags())
                    } else {
                        self.loose_nullish(x)
                    };
                    let r = if matches!(op, Ne | StrictNe) { self.not(r) } else { r };
                    self.push(r, Ty::Bool);
                    return Ok(());
                }
                let r = match (a.ty.num(), b.ty.num()) {
                    (Some(Num::I32), Some(Num::I32)) => {
                        let (x, y) = (self.as_i32(a), self.as_i32(b));
                        self.inst(Opcode::Cmp(NumRepr::I32, cc), vec![x, y], Some(MType::Bool))
                    }
                    (Some(_), Some(_)) => {
                        let (x, y) = (self.as_f64(a), self.as_f64(b));
                        self.inst(Opcode::Cmp(NumRepr::F64, cc), vec![x, y], Some(MType::Bool))
                    }
                    _ => {
                        let (x, y) = (self.boxed(a), self.boxed(b));
                        self.js(Opcode::JsCompare(jcc), vec![x, y], MType::Bool)
                    }
                };
                self.push(r, Ty::Bool);
            }
            Not => {
                let a = self.pop();
                let t = self.truthy(a);
                let r = self.not(t);
                self.push(r, Ty::Bool);
            }

            // --- control ---
            Goto => {
                let off = p.next_int32().unwrap();
                self.jump_to(pc.branch(off), Some(pc));
            }
            JumpIfFalse | JumpIfTrue => {
                let off = p.next_int32().unwrap();
                let c = self.pop();
                let t = self.truthy(c);
                let (target, next) = (pc.branch(off), pc + op.len());
                if op == JumpIfTrue {
                    self.branch(t, target, next);
                } else {
                    self.branch(t, next, target);
                }
            }
            And | Or => {
                let off = p.next_int32().unwrap();
                let c = self.top();
                let t = self.truthy(c);
                let (target, next) = (pc.branch(off), pc + op.len());
                if op == Or {
                    self.branch(t, target, next);
                } else {
                    self.branch(t, next, target);
                }
            }
            Return => {
                let x = self.pop();
                let v = self.boxed(x);
                self.note_this_out();
                self.ctor_stamp();
                self.return_restamps();
                self.term(Opcode::Return, vec![v], vec![]);
            }
            RetRval => {
                let x = self.st[self.rval_ix()];
                let v = self.boxed(x);
                self.note_this_out();
                self.ctor_stamp();
                self.return_restamps();
                self.term(Opcode::Return, vec![v], vec![]);
            }

            FunctionThis => {
                let x = self.st[0];
                if self.s.script.strict || x.ty.tags().is_nonempty_subset_of(TagSet::OBJECT) {
                    self.st.push(x);
                } else {
                    // Sloppy: an object `this` is itself; anything else is
                    // boxed (null and undefined become the global `this`).
                    if !self.keepable(1) {
                        self.demote_objs();
                    }
                    let obj = TagSet::OBJECT;
                    let (t, e, j) = (self.new_block(), self.new_block(), self.new_block());
                    let p = self.f.add_param(t, MType::val(obj));
                    let r = self.f.add_param(j, MType::val(obj));
                    let v = self.boxed(x);
                    self.term(
                        Opcode::GuardTags(obj),
                        vec![v],
                        vec![
                            Edge {
                                block: t,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(e),
                        ],
                    );
                    self.at(t);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: j,
                            args: vec![EdgeArg::Value(p)],
                        }],
                    );
                    self.at(e);
                    let b = self.js(Opcode::JsBoxThis, vec![v], MType::val(obj));
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: j,
                            args: vec![EdgeArg::Value(b)],
                        }],
                    );
                    self.at(j);
                    self.push(r, Ty::Val(obj));
                }
                self.guard_this_layout();
            }
            String => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let s = self.inst(
                    Opcode::ConstStr(a),
                    vec![],
                    Some(MType::Str(mir::types::StrInfo { atom: Some(a) })),
                );
                let x = Slot {
                    v: s,
                    ty: Ty::Val(TagSet::STRING),
                };
                let t = mir::ops::box_type(&self.f.ty(s)).expect("strings box");
                let v = self.inst(Opcode::Box, vec![x.v], Some(t));
                let v = self.weaken(v, MType::val(TagSet::STRING));
                self.push(v, Ty::Val(TagSet::STRING));
            }
            BindUnqualifiedGName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let r = self.js(Opcode::JsBindGName(a), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            SetGName | StrictSetGName => {
                let index = p.next_uint32().unwrap();
                let a = self.atom(index)?;
                let v = self.pop();
                let env = self.pop();
                let (e, y) = (self.boxed(env), self.boxed(v));
                match self.s.syn_bids.get(&index) {
                    Some(&slot) if TYPED_GNAMES => {
                        // §3: `check.binding.write`, then a leaf store of
                        // the slot; a miss exits here.
                        let b = self.binding(a, slot);
                        let fact = self.guard(
                            Opcode::CheckBinding(b, true),
                            vec![],
                            MType::Fact(mir::types::FactKind::Binding(b)),
                        );
                        let (t, _) = self.f.add_inst(self.cur, Opcode::StoreGName(b), vec![fact, y], &[], vec![]);
                        self.f.witnesses[t] = Some(mir::func::Witness {
                            may_kill: mir::types::KillPattern::of(mir::types::KillSet::FUSE),
                        });
                    }
                    _ => self.js_void_keep(Opcode::JsSetName(a, op == StrictSetGName), vec![e, y], v),
                }
                self.repush(v);
            }
            TableSwitch => {
                let default_off = p.next_int32().unwrap();
                let low = p.next_int32().unwrap();
                let high = p.next_int32().unwrap();
                let first = p.next_uint24().unwrap() as usize;
                let x = self.pop();
                let n = usize::try_from((i64::from(high) - i64::from(low) + 1).max(0)).unwrap();
                let default = pc.branch(default_off);
                let mut targets = vec![];
                for k in 0..n {
                    let t = *self
                        .s
                        .script
                        .resume_offsets
                        .get(first + k)
                        .ok_or("TableSwitch resume index out of range")?;
                    targets.push(t);
                }
                // An int32, or a double that is exactly one, selects a case;
                // anything else takes the default.
                let i = match x.ty {
                    Ty::I32 => x.v,
                    Ty::F64 | Ty::Val(_) | Ty::Fn(_) => {
                        let f = match x.ty {
                            Ty::F64 => x.v,
                            _ => {
                                let d = self.new_block();
                                let o = self.f.add_param(d, MType::F64_TOP);
                                let Some(de) = self.edge_to(default, Some(pc)) else {
                                    self.term(Opcode::Unreachable, vec![], vec![]);
                                    return Ok(());
                                };
                                self.term(
                                    Opcode::GuardUnbox(UnboxKind::F64Num),
                                    vec![x.v],
                                    vec![
                                        Edge {
                                            block: d,
                                            args: vec![EdgeArg::Out(0)],
                                        },
                                        de,
                                    ],
                                );
                                self.at(d);
                                o
                            }
                        };
                        // -0 selects case 0 as +0 does: `x + 0` is +0 for
                        // either zero and `x` otherwise.
                        let z = self.const_f64(0.0);
                        let f = self.inst(
                            Opcode::F64Arith(F64Op::Add),
                            vec![f, z],
                            Some(MType::F64_TOP),
                        );
                        let d = self.new_block();
                        let o = self.f.add_param(d, MType::I32_TOP);
                        let Some(de) = self.edge_to(default, Some(pc)) else {
                            self.term(Opcode::Unreachable, vec![], vec![]);
                            return Ok(());
                        };
                        self.term(
                            Opcode::F64ToIntExact,
                            vec![f],
                            vec![
                                Edge {
                                    block: d,
                                    args: vec![EdgeArg::Out(0)],
                                },
                                de,
                            ],
                        );
                        self.at(d);
                        o
                    }
                    Ty::Bool | Ty::Obj(..) | Ty::ObjHint(_) | Ty::Ctor(..) | Ty::Native | Ty::Ta(_) => {
                        self.jump_to(default, Some(pc));
                        return Ok(());
                    }
                    Ty::Dead => unreachable!("a dead slot is never read"),
                };
                let lo = self.const_i32(low);
                let idx = self.inst(
                    Opcode::I32Wrap(ArithOp::Sub),
                    vec![i, lo],
                    Some(MType::I32_TOP),
                );
                let mut edges = vec![];
                for t in targets.into_iter().chain([default]) {
                    match self.edge_to(t, Some(pc)) {
                        Some(e) => edges.push(e),
                        None => {
                            self.term(Opcode::Unreachable, vec![], vec![]);
                            return Ok(());
                        }
                    }
                }
                self.term(Opcode::Switch(u32::try_from(n).unwrap()), vec![idx], edges);
            }
            Case => {
                // [lval, cond]: true pops both and jumps; false keeps lval.
                let off = p.next_int32().unwrap();
                let c = self.pop();
                let t = self.truthy(c);
                let (target, next) = (pc.branch(off), pc + op.len());
                let ne = self.edge_to(next, Some(pc));
                let lval = self.pop();
                let te = self.edge_to(target, Some(pc));
                self.st.push(lval);
                match (te, ne) {
                    (Some(te), Some(ne)) => self.term(Opcode::Br, vec![t], vec![te, ne]),
                    _ => self.term(Opcode::Unreachable, vec![], vec![]),
                }
            }
            Default => {
                let off = p.next_int32().unwrap();
                self.pop();
                self.jump_to(pc.branch(off), Some(pc));
            }
            StrictConstantEq | StrictConstantNe => {
                let operand = p.next_uint16().unwrap();
                let a = self.pop();
                // Against undefined or null: a tag test.
                let exact = match (operand >> 8) & 0xFF {
                    3 => Some(TagSet::prims(PRIM_UNDEFINED)),
                    4 => Some(TagSet::prims(PRIM_NULL)),
                    _ => None,
                };
                if exact.is_some_and(|t| self.fuse_test(a, t, op == StrictConstantNe)) {
                    return Ok(());
                }
                let x = self.boxed(a);
                let mut r = self.inst(
                    Opcode::JsConstantStrictEq(operand),
                    vec![x],
                    Some(MType::Bool),
                );
                if op == StrictConstantNe {
                    r = self.not(r);
                }
                self.push(r, Ty::Bool);
            }
            IsNullOrUndefined => {
                // [v] -> [v, v is null or undefined], decided by the tags
                // when they say, else by a tag test merging both ways.
                let a = self.top();
                let nullish = TagSet::prims(PRIM_NULL | PRIM_UNDEFINED);
                let tags = a.ty.tags();
                let r = if tags.subset_of(nullish) {
                    self.inst(Opcode::ConstBool(true), vec![], Some(MType::Bool))
                } else if tags.intersect(nullish).is_empty() {
                    self.inst(Opcode::ConstBool(false), vec![], Some(MType::Bool))
                } else {
                    if self.fuse_test(a, nullish, false) {
                        return Ok(());
                    }
                    let x = self.boxed(a);
                    self.tag_test(x, nullish)
                };
                self.push(r, Ty::Bool);
            }
            TypeofEq => {
                let operand = p.next_uint8().unwrap();
                let a = self.pop();
                // A type whose values are exactly some tags (no object is
                // one): a tag test.
                let exact = match operand & 0x0f {
                    3 => Some(TagSet::STRING),
                    4 => Some(TagSet::NUMBER),
                    5 => Some(TagSet::BOOLEAN),
                    6 => Some(TagSet::prims(crate::opsem::PRIM_SYMBOL)),
                    7 => Some(TagSet::prims(PRIM_BIGINT)),
                    _ => None,
                };
                if exact.is_some_and(|t| self.fuse_test(a, t, operand & 0x80 != 0)) {
                    return Ok(());
                }
                let x = self.boxed(a);
                let r = self.inst(Opcode::JsTypeofEq(operand), vec![x], Some(MType::Bool));
                self.push(r, Ty::Bool);
            }

            // --- generic names, properties, elements and calls ---
            GetGName => {
                let index = p.next_uint32().unwrap();
                if self.s.next_is_typeof(pc, op) {
                    // `typeof name`: an unbound global reads as undefined.
                    let a = self.atom(index)?;
                    let r = self.js(Opcode::JsRt(RtOp::GetNameTypeof(a)), vec![], MType::VAL_TOP);
                    self.push(r, Ty::Val(TagSet::ALL));
                    return Ok(());
                }
                let a = self.atom(index)?;
                if let Some(&fg) = self.s.fused.get(&index) {
                    if self.fused_gname(a, fg) {
                        return Ok(());
                    }
                }
                let r = match self.s.syn_bids.get(&index) {
                    Some(&slot) if TYPED_GNAMES => {
                        // §3: `check.binding`, then a leaf load of the
                        // slot. A syntactic global is a non-configurable
                        // data property, so the check holds once resolved;
                        // a miss exits here.
                        let b = self.binding(a, slot);
                        let fact = self.guard(
                            Opcode::CheckBinding(b, false),
                            vec![],
                            MType::Fact(mir::types::FactKind::Binding(b)),
                        );
                        self.inst(Opcode::LoadGName(b), vec![fact], Some(MType::VAL_TOP))
                    }
                    _ => self.js(Opcode::JsGetName(a), vec![], MType::VAL_TOP),
                };
                self.gname_vals.insert(r, a);
                self.push(r, Ty::Val(TagSet::ALL));
                if let Some(&claim) = self.s.gname_types.get(&index) {
                    self.guard_result(claim, pc + op.len(), true);
                }
            }
            GetProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let recv = self.pop();
                // A typed array's length: its length slot.
                if let (Ty::Ta(_), true) = (recv.ty, LENGTH_TA) {
                    if self.mm.atoms[a].chars() == "length".encode_utf16().collect::<Vec<u16>>().as_slice() {
                        let n = self.inst(Opcode::LengthTa, vec![recv.v], Some(MType::i32_range(0, i64::from(i32::MAX))));
                        self.push(n, Ty::I32);
                        return Ok(());
                    }
                }
                if self.mm.atoms[a].chars() == "length".encode_utf16().collect::<Vec<u16>>().as_slice()
                    && self.length_op(recv)
                {
                    return Ok(());
                }
                if self.ctor_get(pc + op.len(), a, recv) {
                    return Ok(());
                }
                if self.accessor_get(pc, a, recv) {
                    return Ok(());
                }
                let site = self
                    .typed_site(pc, a)
                    .or_else(|| self.hinted_site(recv.v, a))
                    .or_else(|| self.named_site(recv, a));
                if let Some((o, site)) = site.and_then(|site| self.proven_recv(recv, &site)) {
                    let r = self
                        .js_dirty_exits(Opcode::LoadField(a), vec![o], Some(site.claim_ty()), pc + op.len(), None)
                        .unwrap();
                    let r = self.weaken(r, MType::VAL_TOP);
                    self.push(r, Ty::Val(TagSet::ALL));
                    self.guard_result(site.claim, pc + op.len(), false);
                } else if let Some(site) = site {
                    // The predicted layout: guard the receiver's class
                    // locally, then load the field (§4.3). A receiver of
                    // another layout reads through the IC instead of
                    // exiting: a prediction that is wrong for some receivers
                    // must not send the rest of the activation to baseline
                    // every time. The claim is guarded after the join. The
                    // IC arm keeps facts, a kill exiting; where it cannot,
                    // it is a fence, and `Obj` slots meet as `ObjHint`.
                    if !self.keepable(1) {
                        self.demote_objs();
                    }
                    let x = self.boxed(recv);
                    let join = self.new_block();
                    let jr = self.f.add_param(join, MType::VAL_TOP);
                    let generic = self.new_block();
                    let o = self.guard_layout_or(x, &site, generic);
                    let r = self
                        .js_dirty_exits(Opcode::LoadField(a), vec![o], Some(site.claim_ty()), pc + op.len(), None)
                        .unwrap();
                    let r = self.weaken(r, MType::VAL_TOP);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: join,
                            args: vec![EdgeArg::Value(r)],
                        }],
                    );
                    self.at(generic);
                    let r = self.js(Opcode::JsGetProp(a), vec![x], MType::VAL_TOP);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: join,
                            args: vec![EdgeArg::Value(r)],
                        }],
                    );
                    self.at(join);
                    self.push(jr, Ty::Val(TagSet::ALL));
                    self.guard_result(site.claim, pc + op.len(), false);
                } else {
                    let x = self.boxed(recv);
                    let r = self.js(Opcode::JsGetProp(a), vec![x], MType::VAL_TOP);
                    // `Math.<fn>`, for a typed call (`math_call`).
                    if self.gname_vals.get(&recv.v).is_some_and(|&g| self.atom_is(g, "Math")) {
                        if let Some(m) = math_fn_named(&std::string::String::from_utf16_lossy(self.mm.atoms[a].chars())) {
                            self.math_fns.insert(r, m);
                        }
                    }
                    self.push(r, Ty::Val(TagSet::ALL));
                    let claim = self.s.ctx.facts.field_sites.get(&self.site(pc)).copied();
                    self.guard_result(claim.unwrap_or_default(), pc + op.len(), false);
                }
            }
            SetProp | StrictSetProp => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let v = self.pop();
                let recv = self.pop();
                if self.ctor_set(pc + op.len(), a, recv, v) {
                    self.repush(v);
                    return Ok(());
                }
                if self.accessor_set(pc, a, recv, v, op == StrictSetProp) {
                    self.repush(v);
                    return Ok(());
                }
                self.store_mask = self.field_claim(pc, a, recv);
                // A field of the predicted layout: a value of its predicted
                // type (statically) keeps TYPES as a typed store; another
                // goes through the IC, whose store keeps the bit by the
                // value's tag or leaves it to the engine, which clears it.
                // A value not statically of the field's type still stores
                // to the slot, as a store without the TYPES claim: its
                // lowering keeps the bit by the value's tag, or leaves the
                // store to the engine, which clears it.
                let vtags = v.ty.tags();
                let site = self
                    .typed_site(pc, a)
                    .or_else(|| self.hinted_site(recv.v, a))
                    .or_else(|| self.named_site(recv, a))
                    .map(|mut s| {
                    s.types &= vtags.is_nonempty_subset_of(s.store_tags);
                    s
                });
                let proven = site.and_then(|site| self.proven_recv(recv, &site));
                // The IC arm of an unproven typed store keeps facts, a kill
                // exiting; where it cannot, it is a fence the two arms meet
                // after: `Obj` slots (and the value, pushed back after it)
                // go in as `ObjHint`.
                let v = if site.is_some() && proven.is_none() && !self.keepable(1) {
                    self.demote_objs();
                    self.demote(v)
                } else {
                    v
                };
                match site {
                    Some(_) if proven.is_some() => {
                        let (mut o, site) = proven.unwrap();
                        if !site.types {
                            // Its TYPES claim is not the store's to keep.
                            if let MType::Obj(mut info) = self.f.ty(o) {
                                if let Some(c) = info.layout.as_mut() {
                                    c.types = false;
                                }
                                o = self.weaken(o, MType::Obj(info));
                            }
                        }
                        let mut x = self.boxed(v);
                        if site.types {
                            x = self.weaken(x, MType::val(site.store_tags));
                        }
                        self.js_dirty_exits(Opcode::StoreField(a), vec![o, x], None, pc + op.len(), Some(v));
                    }
                    Some(site) => {
                        // As for a typed read: another layout's receiver
                        // stores through the IC rather than exiting.
                        let r = self.boxed(recv);
                        let join = self.new_block();
                        let generic = self.new_block();
                        let o = self.guard_layout_or(r, &site, generic);
                        let mut x = self.boxed(v);
                        if site.types {
                            x = self.weaken(x, MType::val(site.store_tags));
                        }
                        self.js_dirty_exits(Opcode::StoreField(a), vec![o, x], None, pc + op.len(), Some(v));
                        self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                        self.at(generic);
                        let y = self.boxed(v);
                        self.js_void_keep(Opcode::JsSetProp(a, op == StrictSetProp), vec![r, y], v);
                        self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                        self.at(join);
                    }
                    None => {
                        let (x, y) = (self.boxed(recv), self.boxed(v));
                        self.js_void_keep(Opcode::JsSetProp(a, op == StrictSetProp), vec![x, y], v);
                    }
                }
                self.repush(v);
            }
            GetElem => {
                self.ta_poly_site = TA_POLY && self.s.ctx.facts.elem_poly_sites.contains(&self.site(pc));
                let key = self.pop();
                let recv = self.pop();
                let ta = self.ta_elem(pc, recv, key);
                let r = if let Some((o, i, k)) = ta {
                    // The element inline, as a boxed number; out of
                    // bounds, the generic op (a fence unless it keeps).
                    if !self.keepable(1) {
                        self.demote_objs();
                    }
                    let (ok, generic, join) = (self.new_block(), self.new_block(), self.new_block());
                    let raw = if k.is_float() { MType::F64_TOP } else { MType::I32_TOP };
                    let p = self.f.add_param(ok, raw);
                    let jr = self.f.add_param(join, MType::VAL_TOP);
                    self.term(
                        Opcode::LoadTa,
                        vec![o, i],
                        vec![
                            Edge {
                                block: ok,
                                args: vec![EdgeArg::Out(0)],
                            },
                            Self::goto(generic),
                        ],
                    );
                    self.at(ok);
                    let ty = if k.is_float() { Ty::F64 } else { Ty::I32 };
                    let b = self.boxed(Slot { v: p, ty });
                    let b = self.weaken(b, MType::VAL_TOP);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: join,
                            args: vec![EdgeArg::Value(b)],
                        }],
                    );
                    self.at(generic);
                    let (x, kb) = (self.boxed(recv), self.boxed(key));
                    let r = self.js(Opcode::JsGetElem, vec![x, kb], MType::VAL_TOP);
                    self.term(
                        Opcode::Jump,
                        vec![],
                        vec![Edge {
                            block: join,
                            args: vec![EdgeArg::Value(r)],
                        }],
                    );
                    self.at(join);
                    Some(jr)
                } else {
                    None
                };
                let r = if let Some(r) = r {
                    r
                } else {
                match self.native_elem(pc, recv, key) {
                    Some((o, i)) => {
                        // A dense element inline; out of bounds or a
                        // hole, the generic op (a fence unless it keeps).
                        if !self.keepable(1) {
                            self.demote_objs();
                        }
                        let (ok, generic, join) = (self.new_block(), self.new_block(), self.new_block());
                        let p = self.f.add_param(ok, MType::VAL_TOP);
                        let jr = self.f.add_param(join, MType::VAL_TOP);
                        self.term(
                            Opcode::LoadElem,
                            vec![o, i],
                            vec![
                                Edge {
                                    block: ok,
                                    args: vec![EdgeArg::Out(0)],
                                },
                                Self::goto(generic),
                            ],
                        );
                        self.at(ok);
                        self.term(
                            Opcode::Jump,
                            vec![],
                            vec![Edge {
                                block: join,
                                args: vec![EdgeArg::Value(p)],
                            }],
                        );
                        self.at(generic);
                        let (x, k) = (self.boxed(recv), self.boxed(key));
                        let r = self.js(Opcode::JsGetElem, vec![x, k], MType::VAL_TOP);
                        self.term(
                            Opcode::Jump,
                            vec![],
                            vec![Edge {
                                block: join,
                                args: vec![EdgeArg::Value(r)],
                            }],
                        );
                        self.at(join);
                        jr
                    }
                    None => {
                        let (x, k) = (self.boxed(recv), self.boxed(key));
                        self.js(Opcode::JsGetElem, vec![x, k], MType::VAL_TOP)
                    }
                }
                };
                self.ta_poly_site = false;
                self.push(r, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.elem_sites.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len(), true);
            }
            SetElem | StrictSetElem => {
                self.ta_poly_site = TA_POLY && self.s.ctx.facts.elem_poly_sites.contains(&self.site(pc));
                let v = self.pop();
                let key = self.pop();
                let recv = self.pop();
                let duty = self.ranges_duty(pc, v);
                // The value as the kind stores it, raw: an int32 for an
                // integer kind (Uint8Clamped clamps it), a number for a
                // float one. A value of unknown type is unboxed at run
                // time, as bbv's typed-array store arm does; a miss (or a
                // double into an integer kind) takes the generic op.
                let ta = self.ta_elem(pc, recv, key).and_then(|(o, i, k)| match (k.is_float(), v.ty.num()) {
                    (true, Some(_)) => Some((o, i, k, Some(self.as_f64(v)))),
                    (false, Some(Num::I32)) => Some((o, i, k, Some(self.as_i32(v)))),
                    (_, None) if !matches!(v.ty, Ty::Dead) => Some((o, i, k, None)),
                    _ => None,
                });
                if let Some((o, i, k, raw)) = ta {
                    let v = if self.keepable(1) {
                        v
                    } else {
                        self.demote_objs();
                        self.demote(v)
                    };
                    let (ok, generic, join) = (self.new_block(), self.new_block(), self.new_block());
                    let raw = match raw {
                        Some(r) => r,
                        None => {
                            let (kind, ty) = if k.is_float() {
                                (UnboxKind::F64Num, MType::F64_TOP)
                            } else {
                                (UnboxKind::I32, MType::I32_TOP)
                            };
                            let unboxed = self.new_block();
                            let r = self.f.add_param(unboxed, ty);
                            let y = self.boxed(v);
                            self.term(
                                Opcode::GuardUnbox(kind),
                                vec![y],
                                vec![
                                    Edge {
                                        block: unboxed,
                                        args: vec![EdgeArg::Out(0)],
                                    },
                                    Self::goto(generic),
                                ],
                            );
                            self.at(unboxed);
                            r
                        }
                    };
                    self.term(
                        Opcode::StoreTa,
                        vec![o, i, raw],
                        vec![Self::goto(ok), Self::goto(generic)],
                    );
                    self.at(ok);
                    self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                    self.at(generic);
                    let (x, kb, y) = (self.boxed(recv), self.boxed(key), self.boxed(v));
                    self.js_void_keep(Opcode::JsSetElem(op == StrictSetElem, duty), vec![x, kb, y], v);
                    self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                    self.at(join);
                    self.st.push(v);
                } else {
                match self.native_elem(pc, recv, key) {
                    Some((o, i)) => {
                        // A dense overwrite inline; else the generic op.
                        let v = if self.keepable(1) {
                            v
                        } else {
                            self.demote_objs();
                            self.demote(v)
                        };
                        let y = self.boxed(v);
                        let (ok, generic, join) = (self.new_block(), self.new_block(), self.new_block());
                        self.term(
                            Opcode::StoreElem(duty),
                            vec![o, i, y],
                            vec![Self::goto(ok), Self::goto(generic)],
                        );
                        self.at(ok);
                        self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                        self.at(generic);
                        let (x, k) = (self.boxed(recv), self.boxed(key));
                        self.js_void_keep(Opcode::JsSetElem(op == StrictSetElem, duty), vec![x, k, y], v);
                        self.term(Opcode::Jump, vec![], vec![Self::goto(join)]);
                        self.at(join);
                        self.st.push(v);
                    }
                    None => {
                        let (x, k, y) = (self.boxed(recv), self.boxed(key), self.boxed(v));
                        self.js_void_keep(Opcode::JsSetElem(op == StrictSetElem, duty), vec![x, k, y], v);
                        self.repush(v);
                    }
                }
                }
            }
            // Generic operations through their runtime helpers.
            Instanceof | In | HasOwn if RT_OPS => {
                let b = self.pop();
                let a = self.pop();
                let (x, y) = (self.boxed(a), self.boxed(b));
                let r = match op {
                    Instanceof => RtOp::Instanceof,
                    In => RtOp::In,
                    _ => RtOp::HasOwn,
                };
                let v = self.js(Opcode::JsRt(r), vec![x, y], MType::val(TagSet::BOOLEAN));
                self.push(v, Ty::Val(TagSet::BOOLEAN));
            }
            DelProp | StrictDelProp if RT_OPS => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let o = self.pop();
                let x = self.boxed(o);
                let r = RtOp::DelProp(a, op == StrictDelProp);
                let v = self.js(Opcode::JsRt(r), vec![x], MType::val(TagSet::BOOLEAN));
                self.push(v, Ty::Val(TagSet::BOOLEAN));
            }
            DelElem | StrictDelElem if RT_OPS => {
                let k = self.pop();
                let o = self.pop();
                let (x, y) = (self.boxed(o), self.boxed(k));
                let r = RtOp::DelElem(op == StrictDelElem);
                let v = self.js(Opcode::JsRt(r), vec![x, y], MType::val(TagSet::BOOLEAN));
                self.push(v, Ty::Val(TagSet::BOOLEAN));
            }
            NewInit | NewObject if RT_OPS => {
                let v = self.js(Opcode::JsRt(RtOp::NewObject), vec![], MType::val(TagSet::OBJECT));
                // An object-literal stamp site: the layout idx with SLOTS
                // (the inits land at the row's slots by construction).
                if let Some(&lid) = self.s.ctx.lit_stamps_in.get(&self.site(self.pc)) {
                    let w = (lid + 1) | crate::wasm::bbv::abi::CLASS_WORD_SLOTS;
                    self.inst(Opcode::StampFresh(w), vec![v], None);
                    self.val_cls.insert(v, lid);
                }
                self.push(v, Ty::Val(TagSet::OBJECT));
            }
            NewArray if RT_OPS => {
                let len = p.next_uint32().unwrap();
                let v = self.js(Opcode::JsRt(RtOp::NewArray(len)), vec![], MType::val(TagSet::OBJECT));
                // An array stamp site: the key with TYPES and RANGES, which
                // an empty array's elements satisfy vacuously; element
                // stores keep them.
                if let Some(&w) = self.s.ctx.array_stamp_in.get(&self.site(self.pc)) {
                    self.inst(Opcode::StampFresh(w), vec![v], None);
                }
                self.push(v, Ty::Val(TagSet::OBJECT));
            }
            InitProp | InitHiddenProp | InitLockedProp if RT_OPS => {
                // [obj, v] -> [obj]
                use crate::wasm::bbv::abi::{INIT_ATTR_ENUMERATE, INIT_ATTR_HIDDEN, INIT_ATTR_LOCKED};
                let a = self.atom(p.next_uint32().unwrap())?;
                let attrs = match op {
                    InitProp => INIT_ATTR_ENUMERATE,
                    InitHiddenProp => INIT_ATTR_HIDDEN,
                    _ => INIT_ATTR_LOCKED,
                };
                let v = self.pop();
                let o = self.top();
                let (x, y) = (self.boxed(o), self.boxed(v));
                self.js_void(Opcode::JsRt(RtOp::InitProp(a, attrs)), vec![x, y]);
            }
            InitElem | InitHiddenElem | InitLockedElem if RT_OPS => {
                // [obj, key, v] -> [obj]
                use crate::wasm::bbv::abi::{INIT_ATTR_ENUMERATE, INIT_ATTR_HIDDEN, INIT_ATTR_LOCKED};
                let attrs = match op {
                    InitElem => INIT_ATTR_ENUMERATE,
                    InitHiddenElem => INIT_ATTR_HIDDEN,
                    _ => INIT_ATTR_LOCKED,
                };
                let v = self.pop();
                let k = self.pop();
                let o = self.top();
                let r = self.ranges_duty(pc, v);
                let (x, y, z) = (self.boxed(o), self.boxed(k), self.boxed(v));
                self.js_void(Opcode::JsRt(RtOp::InitElem(attrs, r)), vec![x, y, z]);
            }
            InitElemArray if RT_OPS => {
                // [obj, v] -> [obj]
                let index = p.next_uint32().unwrap();
                let v = self.pop();
                let o = self.top();
                let k = self.const_val(ConstVal::Int32(index as i32));
                let r = self.ranges_duty(pc, v);
                let (x, z) = (self.boxed(o), self.boxed(v));
                let e = crate::wasm::bbv::abi::INIT_ATTR_ENUMERATE;
                self.js_void(Opcode::JsRt(RtOp::InitElem(e, r)), vec![x, k, z]);
            }
            InitElemInc if RT_OPS => {
                // [obj, idx, v] -> [obj, idx + 1]: an array literal's
                // spread, its index an int32 (the literal's positions).
                let v = self.pop();
                let i = self.pop();
                if i.ty.num() != Some(Num::I32) {
                    return Err("InitElemInc index not int32".into());
                }
                let o = self.top();
                let r = self.ranges_duty(pc, v);
                let (x, k, z) = (self.boxed(o), self.boxed(i), self.boxed(v));
                let e = crate::wasm::bbv::abi::INIT_ATTR_ENUMERATE;
                self.js_void(Opcode::JsRt(RtOp::InitElem(e, r)), vec![x, k, z]);
                let iv = self.as_i32(i);
                let one = self.const_i32(1);
                let n = self.inst(Opcode::I32Wrap(ArithOp::Add), vec![iv, one], Some(MType::I32_TOP));
                self.push(n, Ty::I32);
            }
            ToPropertyKey if RT_OPS => {
                // An int32, a string or a symbol is its own key.
                let x = self.top();
                let keyish = TagSet::INT32.union(TagSet::STRING).union(TagSet::prims(crate::opsem::PRIM_SYMBOL));
                if !x.ty.tags().is_nonempty_subset_of(keyish) {
                    let x = self.pop();
                    let v = self.boxed(x);
                    let r = self.js(Opcode::JsRt(RtOp::ToPropertyKey), vec![v], MType::VAL_TOP);
                    self.push(r, Ty::Val(TagSet::ALL));
                }
            }
            Typeof | TypeofExpr if RT_OPS => {
                let a = self.pop();
                let x = self.boxed(a);
                let v = self.inst(Opcode::JsTypeof, vec![x], Some(MType::val(TagSet::STRING)));
                self.push(v, Ty::Val(TagSet::STRING));
            }
            Throw if RT_OPS => {
                let a = self.pop();
                let x = self.boxed(a);
                let err = self.exit_block(true);
                self.retain_locals(&Opcode::JsThrow);
                let (t, _) = self.f.add_inst(self.cur, Opcode::JsThrow, vec![x], &[], vec![Self::goto(err)]);
                self.live = false;
                self.f.witnesses[t] = Some(mir::func::Witness {
                    may_kill: mir::types::KillPattern::ALL,
                });
            }
            // The actuals (the frame's variable region is past them: the
            // lowering's `vp`).
            Arguments => {
                if self.s.apply_fwd.is_some() {
                    // Only forwarded (`apply_forward`): never made, unless an
                    // exit needs it (`exit_operands`). A value of its own,
                    // so no other undefined is mistaken for it.
                    let v = self.const_val(ConstVal::Undefined);
                    self.args_placeholder = Some(v);
                    self.push(v, Ty::Val(TagSet::prims(PRIM_UNDEFINED)));
                } else {
                    let v = self.js_static(Opcode::ArgsObject, vec![], MType::val(TagSet::OBJECT));
                    self.push(v, Ty::Val(TagSet::OBJECT));
                }
            }
            Rest => {
                let nformal = self.s.nargs.saturating_sub(1);
                let v = self.js_static(Opcode::RestArray(nformal), vec![], MType::val(TagSet::OBJECT));
                self.push(v, Ty::Val(TagSet::OBJECT));
            }
            ArgumentsLength => {
                let v = self.inst(Opcode::ArgsLength, vec![], Some(MType::I32_TOP));
                self.push(v, Ty::I32);
            }
            GetActualArg => {
                let i = self.pop();
                if i.ty != Ty::I32 {
                    return Err("GetActualArg of a non-int32 index".into());
                }
                let v = self.inst(Opcode::ActualArg, vec![i.v], Some(MType::VAL_TOP));
                self.push(v, Ty::Val(TagSet::ALL));
            }
            Iter => {
                // For-in (baseline's helpers): the property iterator; the
                // loop's names from it; its close. A throw inside exits,
                // and baseline's unwind closes it.
                let x = self.pop();
                let v = self.boxed(x);
                let r = self.js(Opcode::JsRt(RtOp::Iter), vec![v], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            MoreIter => {
                let it = self.top();
                let v = self.boxed(it);
                let r = self.inst(Opcode::IterMore, vec![v], Some(MType::VAL_TOP));
                self.push(r, Ty::Val(TagSet::ALL));
            }
            IsNoIter => {
                let x = self.top();
                let v = self.boxed(x);
                let b = self.inst(Opcode::IterIsDone, vec![v], Some(MType::Bool));
                self.push(b, Ty::Bool);
            }
            EndIter => {
                self.pop();
                let it = self.pop();
                let v = self.boxed(it);
                self.inst(Opcode::IterEnd, vec![v], None);
            }
            Callee => {
                let v = self.inst(Opcode::FrameCallee, vec![], Some(MType::val(TagSet::OBJECT)));
                self.push(v, Ty::Val(TagSet::OBJECT));
            }
            CheckObjCoercible | CheckClassHeritage | CheckThis => {
                // The runtime's check of the value, which stays.
                let k = match op {
                    CheckObjCoercible => mir::ops::CHECK_OBJ_COERCIBLE,
                    CheckClassHeritage => mir::ops::CHECK_CLASS_HERITAGE,
                    _ => mir::ops::CHECK_THIS,
                };
                let x = self.top();
                let v = self.boxed(x);
                self.js_void(Opcode::JsRt(RtOp::Check(k)), vec![v]);
            }
            SetFunName => {
                let prefix = u32::from(p.next_uint8().unwrap());
                let name = self.pop();
                let fun = self.top();
                let (f, n) = (self.boxed(fun), self.boxed(name));
                self.js_void(Opcode::JsRt(RtOp::SetFunName(prefix)), vec![f, n]);
            }
            GlobalThis => {
                let r = self.js(Opcode::JsRt(RtOp::GlobalThis), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            BigInt => {
                let idx = p.next_uint32().unwrap();
                let r = self.js(Opcode::JsRt(RtOp::BigInt(idx)), vec![], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            MutateProto => {
                let proto = self.pop();
                let obj = self.top();
                let (o, pr) = (self.boxed(obj), self.boxed(proto));
                self.js_void(Opcode::JsRt(RtOp::MutateProto), vec![o, pr]);
            }
            CheckPrivateField => {
                let cond = u32::from(p.next_uint8().unwrap());
                let kind = u32::from(p.next_uint8().unwrap());
                let n = self.st.len();
                let (obj, key) = (self.st[n - 2], self.st[n - 1]);
                let (o, k) = (self.boxed(obj), self.boxed(key));
                let r = self.js(
                    Opcode::JsRt(RtOp::CheckPrivateField(cond, kind)),
                    vec![o, k],
                    MType::val(TagSet::BOOLEAN),
                );
                self.push(r, Ty::Val(TagSet::BOOLEAN));
            }
            Hole => {
                let v = self.const_val(ConstVal::Hole);
                self.push(v, Ty::Val(TagSet::MAGIC));
            }
            // Always throws: baseline does, from here.
            ThrowMsg | ThrowSetConst => {
                let b = self.exit_block(false);
                self.term(Opcode::Jump, vec![], vec![Self::goto(b)]);
            }
            NewTarget => {
                // The frame's new.target (undefined unless constructed).
                let v = self.inst(Opcode::FrameNewTarget, vec![], Some(MType::VAL_TOP));
                self.push(v, Ty::Val(TagSet::ALL));
            }
            IsConstructing => {
                let v = self.const_val(ConstVal::IsConstructing);
                self.push(v, Ty::Val(TagSet::MAGIC));
            }
            New | NewContent => {
                // [callee, this, args…, new.target] -> [object]
                self.publish_this();
                let argc = usize::from(p.next_uint16().unwrap());
                let n = self.st.len();
                let operands: Vec<Slot> = self.st.drain(n - argc - 3..).collect();
                let vals: Vec<mir::Value> = operands.into_iter().map(|x| self.boxed(x)).collect();
                let site = self.site(pc);
                let mono = match self.s.ctx.facts.scripted_targets(site) {
                    [s] => Some(*s),
                    _ => None,
                };
                let nslots = crate::wasm::bbv::construct_nslots(self.s.ctx, mono, site);
                let word = self.s.alloc_word(mono, site);
                let callee = match mono {
                    Some(k) if INLINE_CONSTRUCT => {
                        self.admit(&[k], true, &|s, k, ictx| s.callee(k, ictx)).map(|mut t| t.remove(0))
                    }
                    _ => None,
                };
                let r = match callee {
                    Some((k, c)) => self.inline_construct(k, &c, &vals, nslots, word),
                    _ => self.js(Opcode::Construct(nslots, word), vals, MType::val(TagSet::OBJECT)),
                };
                // The object the site's constructor builds: its layout, as
                // an advisory class (checked at use).
                let built = mono
                    .and_then(|f| self.s.ctx.stamp_ctors_in.get(&f))
                    .or_else(|| self.s.ctx.construct_sites_in.get(&site));
                if let Some(si) = built {
                    self.val_cls.insert(r, si.layout_id);
                }
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            PushLexicalEnv | PushClassBodyEnv | PushVarEnv => {
                // A scope's environment, made the frame's (write-through:
                // an exit's baseline frame, and its unwind, see it).
                let kind = match op {
                    PushLexicalEnv => mir::ops::ENV_LEXICAL,
                    PushClassBodyEnv => mir::ops::ENV_CLASS_BODY,
                    _ => mir::ops::ENV_VAR,
                };
                let e = self.js(Opcode::JsRt(RtOp::PushEnv(kind, pc.get())), vec![], MType::val(TagSet::OBJECT));
                self.inst(Opcode::EnvSet, vec![e], None);
            }
            EnterWith => {
                let x = self.pop();
                let v = self.boxed(x);
                let e = self.js(Opcode::JsRt(RtOp::EnterWith(pc.get())), vec![v], MType::val(TagSet::OBJECT));
                self.inst(Opcode::EnvSet, vec![e], None);
            }
            FreshenLexicalEnv | RecreateLexicalEnv => {
                let recreate = u32::from(op == RecreateLexicalEnv);
                let e = self.js(Opcode::JsRt(RtOp::FreshenEnv(recreate)), vec![], MType::val(TagSet::OBJECT));
                self.inst(Opcode::EnvSet, vec![e], None);
            }
            PopLexicalEnv | LeaveWith => {
                self.inst(Opcode::EnvPop, vec![], None);
            }
            GetName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let t = u32::from(self.s.next_is_typeof(pc, op));
                let r = self.js(Opcode::JsRt(RtOp::GetName(a, t)), vec![], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            BindName | BindUnqualifiedName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let k = u32::from(op == BindUnqualifiedName);
                let r = self.js(Opcode::JsRt(RtOp::BindName(a, k)), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            DelName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let r = self.js(Opcode::JsRt(RtOp::DelName(a)), vec![], MType::val(TagSet::BOOLEAN));
                self.push(r, Ty::Val(TagSet::BOOLEAN));
            }
            BindVar => {
                let r = self.js(Opcode::JsRt(RtOp::BindVar), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            SetName | StrictSetName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let v = self.pop();
                let env = self.pop();
                let (e, y) = (self.boxed(env), self.boxed(v));
                self.js_void(Opcode::JsRt(RtOp::SetName(a, op == StrictSetName)), vec![e, y]);
                self.repush(v);
            }
            Eval | StrictEval => {
                let argc = usize::from(p.next_uint16().unwrap());
                self.publish_this();
                let n = self.st.len();
                let operands: Vec<Slot> = self.st.drain(n - argc - 2..).collect();
                let vals: Vec<mir::Value> = operands.into_iter().map(|x| self.boxed(x)).collect();
                let r = self.js(Opcode::CallEval(pc.get()), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            Coalesce => {
                // `a ?? b`: on to `b` when the top is null or undefined,
                // else keep it and jump past.
                let off = p.next_int32().unwrap();
                let a = self.top();
                let nullish = TagSet::prims(PRIM_NULL | PRIM_UNDEFINED);
                let tags = a.ty.tags();
                let b = if tags.subset_of(nullish) {
                    self.inst(Opcode::ConstBool(true), vec![], Some(MType::Bool))
                } else if tags.intersect(nullish).is_empty() {
                    self.inst(Opcode::ConstBool(false), vec![], Some(MType::Bool))
                } else {
                    let x = self.boxed(a);
                    self.tag_test(x, nullish)
                };
                let (target, next) = (pc.branch(off), pc + op.len());
                self.branch(b, next, target);
            }
            Object | CallSiteObj => {
                let index = p.next_uint32().unwrap();
                let r = self.inst(Opcode::ObjectLit(index), vec![], Some(MType::val(TagSet::OBJECT)));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            EnvCallee => {
                let hops = match op.len() {
                    2 => u32::from(p.next_uint8().unwrap()),
                    _ => u32::from(p.next_uint16().unwrap()),
                };
                let r = self.inst(Opcode::EnvCallee(hops), vec![], Some(MType::val(TagSet::OBJECT)));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            InitElemGetter | InitHiddenElemGetter | InitElemSetter | InitHiddenElemSetter => {
                let kind = u32::from(matches!(op, InitElemSetter | InitHiddenElemSetter))
                    | (u32::from(matches!(op, InitHiddenElemGetter | InitHiddenElemSetter)) << 1);
                let f = self.pop();
                let k = self.pop();
                let o = self.top();
                let (x, y, z) = (self.boxed(o), self.boxed(k), self.boxed(f));
                self.js_void(Opcode::JsRt(RtOp::InitElemGetSet(kind)), vec![x, y, z]);
            }
            SuperCall => {
                // `super(args)`: the runtime's construct of the parent
                // (`[callee, IS_CONSTRUCTING, args…, new.target]`), which
                // makes `this`; no site sizing, as in baseline.
                self.publish_this();
                let argc = usize::from(p.next_uint16().unwrap());
                let n = self.st.len();
                let operands: Vec<Slot> = self.st.drain(n - argc - 3..).collect();
                let vals: Vec<mir::Value> = operands.into_iter().map(|x| self.boxed(x)).collect();
                let nslots = crate::wasm::bbv::abi::NO_NSLOTS;
                let r = self.js(Opcode::Construct(nslots, 0), vals, MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            SuperBase | SuperFun => {
                let x = self.pop();
                let v = self.boxed(x);
                let r = if op == SuperBase { RtOp::SuperBase } else { RtOp::SuperFun };
                let r = self.js(Opcode::JsRt(r), vec![v], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            GetPropSuper => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let base = self.pop();
                let recv = self.pop();
                let (x, y) = (self.boxed(recv), self.boxed(base));
                let r = self.js(Opcode::JsRt(RtOp::GetPropSuper(a)), vec![x, y], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            GetElemSuper => {
                let base = self.pop();
                let key = self.pop();
                let recv = self.pop();
                let vals = vec![self.boxed(recv), self.boxed(key), self.boxed(base)];
                let r = self.js(Opcode::JsRt(RtOp::GetElemSuper), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            SetPropSuper | StrictSetPropSuper => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let v = self.pop();
                let base = self.pop();
                let recv = self.pop();
                let vals = vec![self.boxed(recv), self.boxed(base), self.boxed(v)];
                let r = self.js(Opcode::JsRt(RtOp::SetPropSuper(a, op == StrictSetPropSuper)), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            SetElemSuper | StrictSetElemSuper => {
                let v = self.pop();
                let base = self.pop();
                let key = self.pop();
                let recv = self.pop();
                let vals = vec![self.boxed(recv), self.boxed(key), self.boxed(base), self.boxed(v)];
                let r = self.js(Opcode::JsRt(RtOp::SetElemSuper(op == StrictSetElemSuper)), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            InitHomeObject => {
                let home = self.pop();
                let f = self.top();
                let (x, y) = (self.boxed(f), self.boxed(home));
                self.js_void(Opcode::JsRt(RtOp::InitHomeObject), vec![x, y]);
            }
            FunWithProto => {
                let index = p.next_uint32().unwrap();
                let x = self.pop();
                let v = self.boxed(x);
                let r = self.js(Opcode::JsRt(RtOp::FunWithProto(index)), vec![v], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            CheckThisReinit => {
                let x = self.top();
                let v = self.boxed(x);
                self.js_void(Opcode::JsRt(RtOp::Check(mir::ops::CHECK_THIS_REINIT)), vec![v]);
            }
            CheckReturn => {
                // [this] -> [result], with the frame's rval.
                let t = self.pop();
                let rv = self.st[self.rval_ix()];
                let (x, y) = (self.boxed(t), self.boxed(rv));
                let r = self.js(Opcode::JsRt(RtOp::CheckReturn), vec![x, y], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            AddDisposable => {
                let hint = u32::from(p.next_uint8().unwrap());
                let nc = self.pop();
                let m = self.pop();
                let v = self.pop();
                let vals = vec![self.boxed(v), self.boxed(m), self.boxed(nc)];
                self.js_void(Opcode::JsRt(RtOp::AddDisposable(hint)), vals);
            }
            TakeDisposeCapability => {
                let r = self.js(Opcode::JsRt(RtOp::TakeDisposeCapability), vec![], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            CreateSuppressedError => {
                let sup = self.pop();
                let e = self.pop();
                let vals = vec![self.boxed(e), self.boxed(sup)];
                let r = self.js(Opcode::JsRt(RtOp::CreateSuppressedError), vals, MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            GetBoundName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let x = self.pop();
                let v = self.boxed(x);
                let r = self.js(Opcode::JsRt(RtOp::GetBoundName(a)), vec![v], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            ObjWithProto => {
                let x = self.pop();
                let v = self.boxed(x);
                let r = self.js(Opcode::JsRt(RtOp::ObjWithProto), vec![v], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            NewPrivateName => {
                let a = self.atom(p.next_uint32().unwrap())?;
                let t = TagSet::prims(crate::opsem::PRIM_SYMBOL);
                let r = self.js(Opcode::JsRt(RtOp::NewPrivateName(a)), vec![], MType::val(t));
                self.push(r, Ty::Val(t));
            }
            DynamicImport => {
                let o = self.pop();
                let s = self.pop();
                let vals = vec![self.boxed(s), self.boxed(o)];
                let r = self.js(Opcode::JsRt(RtOp::DynamicImport), vals, MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            SpreadEval | StrictSpreadEval => {
                self.publish_this();
                let arr = self.pop();
                let thisv = self.pop();
                let callee = self.pop();
                let vals = vec![self.boxed(callee), self.boxed(thisv), self.boxed(arr)];
                let r = self.js(Opcode::JsRt(RtOp::SpreadEval(pc.get())), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            Generator => {
                let r = self.js(Opcode::JsRt(RtOp::CreateGenerator), vec![], MType::val(TagSet::OBJECT));
                self.push(r, Ty::Val(TagSet::OBJECT));
            }
            InitialYield | Yield | Await => {
                // Suspend with the frame as an exit writes it; a resume
                // enters this yield's own root at the landing (§5.2's
                // onramps, keyed by the resume index).
                let index = p.next_uint24().unwrap();
                let initial = op == InitialYield;
                let before = self.st.clone();
                let ops = self.exit_operands(pc, &before);
                let (nargs, nlocals) = (self.s.nargs, self.s.nlocals);
                self.term(
                    Opcode::GenSuspend {
                        pc,
                        index,
                        nargs,
                        nlocals,
                        initial,
                    },
                    ops,
                    vec![],
                );
                let popped = if initial { 1 } else { 2 };
                self.resume_root(index, pc + op.len(), &before, popped)?;
            }
            AfterYield => {
                p.next_uint24();
            }
            FinalYieldRval => {
                let g = self.pop();
                let gv = self.boxed(g);
                self.js_void(Opcode::JsRt(RtOp::GenFinal), vec![gv]);
                let x = self.st[self.rval_ix()];
                let v = if x.ty == Ty::Dead {
                    self.const_val(ConstVal::Undefined)
                } else {
                    self.boxed(x)
                };
                self.term(Opcode::Return, vec![v], vec![]);
            }
            ResumeKind => {
                let kind = i32::from(p.next_uint8().unwrap());
                let v = self.const_i32(kind);
                self.push(v, Ty::I32);
            }
            IsGenClosing => {
                let x = self.top();
                let v = self.boxed(x);
                let b = self.inst(Opcode::IsGenClosing, vec![v], Some(MType::Bool));
                self.push(b, Ty::Bool);
            }
            CheckResumeKind => {
                // [val, gen, kind] -> [val]: next goes on; throw and return
                // raise through the helper, which always fails.
                let k = self.pop();
                let g = self.pop();
                let next = match k.ty {
                    Ty::I32 => self.const_i32_of(k.v),
                    _ => None,
                };
                if next != Some(0) {
                    let ki = if k.ty == Ty::I32 {
                        k.v
                    } else {
                        let kv = self.boxed(k);
                        self.guard(Opcode::GuardUnbox(UnboxKind::I32), vec![kv], MType::I32_TOP)
                    };
                    let zero = self.const_i32(0);
                    let is_next = self.inst(Opcode::Cmp(NumRepr::I32, Cc::Eq), vec![ki, zero], Some(MType::Bool));
                    let (cont, raise) = (self.new_block(), self.new_block());
                    self.term(Opcode::Br, vec![is_next], vec![Self::goto(cont), Self::goto(raise)]);
                    self.at(raise);
                    let v = self.top();
                    let vals = vec![self.boxed(v), self.boxed(g), self.boxed(k)];
                    // A return stages its value as the frame's rval: the
                    // throw's exit must leave that slot as the helper wrote
                    // it.
                    let ix = self.rval_ix();
                    self.pre[ix] = Slot::dead();
                    self.js_void(Opcode::JsRt(RtOp::GenCheckResume), vals);
                    self.term(Opcode::Unreachable, vec![], vec![]);
                    self.at(cont);
                }
            }
            AsyncAwait | AsyncResolve => {
                let g = self.pop();
                let v = self.pop();
                let vals = vec![self.boxed(v), self.boxed(g)];
                let r = self.js(Opcode::JsRt(RtOp::AsyncAwait(u32::from(op == AsyncResolve))), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            AsyncReject => {
                let g = self.pop();
                let stack = self.pop();
                let reason = self.pop();
                let vals = vec![self.boxed(reason), self.boxed(stack), self.boxed(g)];
                let r = self.js(Opcode::JsRt(RtOp::AsyncReject), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            CanSkipAwait => {
                let x = self.top();
                let v = self.boxed(x);
                let r = self.js(Opcode::JsRt(RtOp::CanSkipAwait), vec![v], MType::val(TagSet::BOOLEAN));
                self.push(r, Ty::Val(TagSet::BOOLEAN));
            }
            MaybeExtractAwaitValue => {
                // [v, can] -> [v', can]
                let can = self.pop();
                let x = self.pop();
                let vals = vec![self.boxed(x), self.boxed(can)];
                let r = self.js(Opcode::JsRt(RtOp::MaybeExtractAwait), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
                self.repush(can);
            }
            Resume => {
                let k = self.pop();
                let v = self.pop();
                let g = self.pop();
                let vals = vec![self.boxed(g), self.boxed(v), self.boxed(k)];
                let r = self.js(Opcode::JsRt(RtOp::Resume), vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            CallIter | CallContentIter => {
                // An iterator method (`obj[Symbol.iterator]()`, a
                // `return`): the ordinary call, whose uncallable callee
                // throws the iterator protocol's error.
                let argc = usize::from(p.next_uint16().unwrap());
                self.publish_this();
                let n = self.st.len();
                let operands: Vec<Slot> = self.st.drain(n - argc - 2..).collect();
                let vals: Vec<mir::Value> = operands.into_iter().map(|x| self.boxed(x)).collect();
                let r = self.js(Opcode::CallIter, vals, MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.call_types.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len(), false);
            }
            SpreadCall | SpreadNew | SpreadSuperCall => {
                // `f(...a)` / `new f(...a)` / `super(...a)`: baseline's
                // helper, over the spread's argument array.
                let construct = op != SpreadCall;
                self.publish_this();
                let nt = if construct {
                    let x = self.pop();
                    self.boxed(x)
                } else {
                    self.const_val(ConstVal::Null)
                };
                let arr = self.pop();
                let thisv = self.pop();
                let callee = self.pop();
                let vals = vec![self.boxed(callee), self.boxed(thisv), self.boxed(arr), nt];
                let (out, ty) = if construct {
                    (MType::val(TagSet::OBJECT), TagSet::OBJECT)
                } else {
                    (MType::VAL_TOP, TagSet::ALL)
                };
                let r = self.js(Opcode::JsRt(RtOp::SpreadCall(u32::from(construct))), vals, out);
                self.push(r, Ty::Val(ty));
            }
            OptimizeSpreadCall => {
                let x = self.pop();
                let v = self.boxed(x);
                let r = self.js(Opcode::JsRt(RtOp::OptimizeSpreadCall), vec![v], MType::VAL_TOP);
                self.push(r, Ty::Val(TagSet::ALL));
            }
            OptimizeGetIterator => {
                let x = self.pop();
                let v = self.boxed(x);
                let b = self.inst(Opcode::IterOptimizable, vec![v], Some(MType::Bool));
                self.push(b, Ty::Bool);
            }
            CheckIsObj => {
                let kind = u32::from(p.next_uint8().unwrap());
                let x = self.top();
                let v = self.boxed(x);
                self.js_void(Opcode::JsRt(RtOp::CheckIsObj(kind)), vec![v]);
            }
            CloseIter => {
                let kind = u32::from(p.next_uint8().unwrap());
                let x = self.pop();
                let v = self.boxed(x);
                self.js_void(Opcode::JsRt(RtOp::CloseIter(kind)), vec![v]);
            }
            Call | CallIgnoresRv | CallContent => {
                let argc = usize::from(p.next_uint16().unwrap());
                if self.math_call(argc) {
                    return Ok(());
                }
                self.publish_this();
                let n = self.st.len();
                let mut operands: Vec<Slot> = self.st.drain(n - argc - 2..).collect();
                // A receiver (or a `.call`'s `this`) a fence demoted from
                // under construction, for callees to inline: back to its
                // construction state (§2.3).
                {
                    let site = self.site(pc);
                    let facts = &self.s.ctx.facts;
                    let direct = !facts.scripted_targets(site).is_empty();
                    let fwd = (argc >= 1
                        && facts.apply_sites.get(&site) == Some(&crate::facts::CallForm::Call)
                        && (facts.apply_targets.contains_key(&site) || facts.apply_target_sets.contains_key(&site)))
                        || (argc == 2 && self.s.apply_fwd.as_ref().is_some_and(|f| f.contains(&pc)));
                    for (i, want) in [(1, direct), (2, fwd)] {
                        if want {
                            if let Some(s) = self.ctor_reguard(operands[i]) {
                                operands[i] = s;
                            }
                        }
                    }
                }
                // A known closure is the callee (context-sensitive: known
                // here, maybe not where the analysis looked); the closures
                // the call passes go to the callee's build.
                let known = match operands[0].ty {
                    Ty::Fn(k) => Some(k),
                    _ => None,
                };
                let fns: Vec<Option<ScriptId>> = operands[2..]
                    .iter()
                    .map(|x| match x.ty {
                        Ty::Fn(k) => Some(k),
                        _ => None,
                    })
                    .collect();
                // An object under construction as the receiver, or as a
                // `.call`'s `this`: callees built for it (§2.3).
                let this_ctor = |x: Option<&Slot>| match x.map(|x| x.ty) {
                    Some(Ty::Ctor(k, n, t)) => Some((k, n, t)),
                    _ => None,
                };
                let recv_ctor = this_ctor(operands.get(1)).map(|c| (c, operands[1]));
                let fwd_ctor = this_ctor(operands.get(2)).map(|c| (c, operands[2]));
                let vals: Vec<mir::Value> = operands.into_iter().map(|x| self.boxed(x)).collect();
                let facts_sids = self.s.ctx.facts.scripted_targets(self.site(pc));
                let known_sids: Vec<ScriptId> = known.into_iter().collect();
                let sids: &[ScriptId] = if known.is_some() { &known_sids } else { facts_sids };
                let sids: Vec<ScriptId> = sids.to_vec();
                let forward = if argc >= 1 {
                    self.call_forward(&vals, &fns[1..], fwd_ctor.map(|(c, x)| (c, x, vals[2])))
                } else {
                    None
                };
                let r = if let Some(r) = forward {
                    r
                } else if argc == 2 && self.s.apply_fwd.as_ref().is_some_and(|f| f.contains(&pc)) {
                    self.apply_forward(&vals, fwd_ctor)
                } else if let Some(targets) = {
                    let rc = recv_ctor.map(|(c, _)| c);
                    let fns = &fns;
                    self.admit(&sids, false, &|s, k, ictx| s.callee_ctx(k, fns, rc, ictx))
                } {
                    let raw = recv_ctor.map(|(_, x)| self.ctor_pass(x, vals[1]));
                    let r = self.inline_call_this(&targets, &vals, None, raw);
                    if raw.is_some() {
                        self.ctor_after(&targets, vals[1]);
                    }
                    r
                } else {
                    // Not inlined: a known single callee is called
                    // directly while it is the callee.
                    self.likely_targets = if DIRECT_CALLS
                        && sids.len() <= MAX_DIRECT_TARGETS
                        && sids.iter().all(|&k| self.s.direct_ok(k))
                    {
                        sids.to_vec()
                    } else {
                        vec![]
                    };
                    let r = self.js(Opcode::Call, vals, MType::VAL_TOP);
                    self.likely_targets.clear();
                    r
                };
                self.push(r, Ty::Val(TagSet::ALL));
                let claim = self.s.ctx.facts.call_types.get(&self.site(pc)).copied();
                self.guard_result(claim.unwrap_or_default(), pc + op.len(), false);
            }

            op => return Err(format!("{op:?}")),
        }
        Ok(())
    }

    fn js_binop(&mut self, k: JsBinop, a: Slot, b: Slot) {
        let (x, y) = (self.boxed(a), self.boxed(b));
        // A BigInt result needs both operands BigInt after ToNumeric; an
        // operand that is no BigInt and no object (whose valueOf might
        // give one) makes it a Number, or a TypeError for mixing.
        let big_free = |s: Slot| {
            s.ty
                .tags()
                .intersect(TagSet::prims(PRIM_BIGINT).union(TagSet::OBJECT))
                .is_empty()
        };
        let no_big = big_free(a) || big_free(b);
        let tags = match k {
            JsBinop::Ursh => TagSet::NUMBER,
            JsBinop::BitAnd | JsBinop::BitOr | JsBinop::BitXor | JsBinop::Lsh | JsBinop::Rsh if no_big => {
                TagSet::INT32
            }
            JsBinop::BitAnd | JsBinop::BitOr | JsBinop::BitXor | JsBinop::Lsh | JsBinop::Rsh => {
                TagSet::prims(PRIM_INT32 | PRIM_BIGINT)
            }
            _ if no_big => TagSet::NUMBER,
            _ => TagSet::prims(crate::opsem::NUM | PRIM_BIGINT),
        };
        let r = self.js(Opcode::JsBinop(k), vec![x, y], MType::val(tags));
        if tags == TagSet::INT32 {
            // Always an int32: unboxed, the guard never fails.
            let i = self.guard(Opcode::GuardUnbox(UnboxKind::I32), vec![r], MType::I32_TOP);
            self.push(i, Ty::I32);
        } else {
            self.push(r, Ty::Val(tags));
        }
    }

    fn js_unop(&mut self, u: JsUnop, a: Slot) {
        let x = self.boxed(a);
        let tags = match u {
            JsUnop::Pos => TagSet::NUMBER,
            _ => TagSet::prims(crate::opsem::NUM | PRIM_BIGINT),
        };
        let r = self.js(Opcode::JsUnop(u), vec![x], MType::val(tags));
        self.push(r, Ty::Val(tags));
    }
}
