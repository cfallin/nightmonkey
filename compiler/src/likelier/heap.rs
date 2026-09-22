/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The heap model: abstractions, field cells, classes, prototype chains,
//! and snapshot seeding as initial state (no oracle, no consultation points
//! -- program writes join into the same cells the snapshot pre-filled).
//!
//! Structure rules (all monotone, and all order-independent -- see the
//! note on prototype installs below):
//! - Two distinct snapshot objects are two distinct abstractions; their join
//!   is ClassAny/AnyObject. Nothing can fuse their field cells.
//! - A class's method table is the field space of its proto abstraction
//!   (`ProtoOf(class)`, synthetic); concrete prototype objects registered as
//!   sources feed it through standing per-name links. A proto link is a
//!   lookup edge, never value flow: `B.prototype = new A()` must not make
//!   A's instance fields flow into B's.
//! - `ClassView(C, name)` is the read view for ClassAny receivers: every
//!   `Field(a, name)` with `class(a) = C` and `ClassField(C, name)` feed it.
//!   A One(a) read reads only its own cell + ClassField + chain: letting it
//!   see sibling instances' values would merge a whole class into one cell,
//!   which is the precision this model exists to keep.
//! - A named property read does walk the prototype chain, and it joins
//!   every level rather than stopping at one (`chain_join`). The
//!   interpreter stops at the first object that has the property; the
//!   analysis cannot tell which object that will be, so picking a level
//!   would be a guess, and the alternative -- an if-else over "does this
//!   level have it" -- is not something a cell can express, since a cell
//!   holds what may flow there, not whether the property exists. Joining
//!   the levels answers the question the cells can answer: what values
//!   this read may see. That is how a method read off an instance finds
//!   its class's method table, which lives one level up.
//!   Element reads (the reserved `ELEMS` name) are the exception -- they
//!   consult the receiver's own cell only, since joining up the chain
//!   would pour every array's elements into one shared cell, and no real
//!   program inherits its elements.
//!
//! Determinism and prototype installs: the structure above is built as
//! constraints evaluate, so the *order* in which two `F.prototype = ...`
//! installs are seen decides which one wins the class's upward chain link
//! and which method scripts get homed to which class (`register_proto_source`,
//! `note_method_home`: first install wins, a differing second install
//! demotes to none). That is not a source of run-to-run nondeterminism --
//! the worklist order is itself deterministic, so the same input yields
//! the same answer every time -- but it does mean a program that installs
//! two different prototypes on one constructor is answered by whichever
//! install the fixpoint reaches first, rather than by a join of the two.
//! Field *values* have no such rule: they always join.

use super::builtins::{self, NativeKind};
use super::engine::{AllocKind, CellId, CellKey, ConId, Constraint, ElemBuiltinKind, SEED};
use super::types::{observe, Agreed};
use super::types::{AbsId, AbsLabels, ClassId, CtxId, FnId, NameId, ObjType, TypeSet, CTX0};
use super::{RecvKind, SharedCtorSite, Solver};
use crate::constants::{CHAIN_DEPTH, MAX_HOMES, RECV_LABEL_CAP};
use crate::ids::{EnvSlot, FormalIndex, JsString, Pc, ScriptId, Site, VarId};
use crate::opsem::{
    Prims, TaKind, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_STRING, PRIM_SYMBOL,
    PRIM_UNDEFINED,
};
use crate::source::{
    ObjectData, ObjectKind, Primitive, ScopeData, Source, SourceObject, SourceObjectId,
};
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AbsKey {
    /// A transcribed snapshot object (including the global).
    Snap(SourceObjectId),
    /// A script's function-object statics space (`F.staticName`).
    FnObj(ScriptId),
    /// The synthetic prototype abstraction of a class: its field space IS
    /// the method table.
    ProtoOf(ClassId),
    /// An allocation site, per context.
    Alloc {
        script: ScriptId,
        pc: Pc,
        ctx: CtxId,
    },
    /// A synthesized builtin namespace (Math, json, ...): the walker
    /// cannot transcribe unregistered native objects, so their method
    /// tables are seeded from the spec (index into namespaces).
    NativeNs(u8),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProtoLink {
    Abs(AbsId),
    None,
}

pub struct Abstraction {
    pub key: AbsKey,
    /// Immutable class label, assigned at intern time (what makes typeset
    /// joins order-independent).
    pub class: Option<ClassId>,
    pub proto: ProtoLink,
    /// The class whose method table this abstraction feeds (proto objects);
    /// method-home attribution keys on it.
    pub owner_class: Option<ClassId>,
    /// `ProtoOf` back-pointer.
    pub proto_of: Option<ClassId>,
    /// The element kind, when this abstraction is a typed array.
    pub ta_kind: Option<TaKind>,
    /// Whether this abstraction's object is a JS Array (a dense
    /// integer-indexed exotic object), as opposed to any object that
    /// merely happens to carry integer-keyed properties. Both kinds put
    /// their elements in the same place -- the field cell of the reserved
    /// `ELEMS` name -- so this bit does not decide where elements live. It
    /// decides the meet rule (`Engine::join_ts`: two array populations
    /// merge into a region that keeps its element view, an array and a
    /// non-array collapse to AnyObject) and the array-claim emission.
    pub is_array: bool,
    /// Whether the transcribed snapshot object's properties have been
    /// copied into this abstraction's field cells yet (`ensure_seeded`).
    /// Seeding is lazy -- a bundle has far more snapshot objects than the
    /// program ever touches -- and happens exactly once.
    seeded: bool,
}

/// Snapshot-confirmed class identity: the concrete `.prototype` cell when
/// one exists, else the constructor script (the lazy-`Function.prototype`
/// trap: a pure data record has no prototype object).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ClassKey {
    Proto(SourceObjectId),
    Script(ScriptId),
    /// Per-allocation-site pseudo-class for classless literals/arrays, so
    /// same-site cross-context abstractions join to ClassAny(site) instead
    /// of AnyObject.
    Site(Site),
}

pub struct ClassInfo {
    pub key: ClassKey,
    pub ctor: Option<ScriptId>,
    pub proto_abs: AbsId,
    /// Concrete prototype objects feeding the method table.
    pub sources: Vec<AbsId>,
    /// Site classes only: the allocation's typed-array element kind.
    pub ta_kind: Option<TaKind>,
    /// Site classes only: whether the allocation makes a JS Array. See
    /// [`Abstraction::is_array`].
    pub is_array: bool,
}

#[derive(Default)]
pub struct Heap {
    abs_ids: HashMap<AbsKey, AbsId>,
    pub abs: Vec<Abstraction>,
    class_ids: HashMap<ClassKey, ClassId>,
    pub classes: Vec<ClassInfo>,
    /// Field names ever interned per abstraction (drives late source
    /// registration).
    fields_of: HashMap<AbsId, Vec<NameId>>,
    /// Script -> the prototype object shared by all its live closures.
    pub script_proto: HashMap<ScriptId, SourceObjectId>,
    /// `.prototype` object id -> constructor script (the concrete->class
    /// bridge).
    pub proto_owner: HashMap<SourceObjectId, ScriptId>,
    /// Script -> its transcribed snapshot function objects, for seeding
    /// the `FnObj` statics space (`F.staticName` installed at wizen time
    /// lives only in the snapshot object).
    script_fn_objs: HashMap<ScriptId, Vec<SourceObjectId>>,
    /// Method script -> the constructor whose method table installed it,
    /// while every install agrees.
    pub method_home: HashMap<ScriptId, Agreed<ScriptId>>,
    /// Literal sites whose allocation became a prototype object (their
    /// "fields" are a method table, not instance layout evidence).
    pub site_is_proto: HashSet<Site>,
    /// Allocation sites whose objects receive computed-name property
    /// writes (a for-in copy like `Object.extend`): the generic store path
    /// cannot certify slot conformance, so SLOTS never holds on these
    /// objects and a slot row would arm a guard that misses forever.
    pub dyn_named_writes: HashSet<Site>,
}

impl Heap {
    pub fn class_id(&self, key: ClassKey) -> Option<ClassId> {
        self.class_ids.get(&key).copied()
    }

    pub fn abs_class(&self, a: AbsId) -> Option<ClassId> {
        self[a].class
    }
}

/// Abstractions and classes are stored in dense vectors keyed by their own
/// id type, so `heap[abs]` and `heap[class]` are the natural spellings and
/// no caller has to write out the `as usize` cast that a raw index needs.
impl std::ops::Index<AbsId> for Heap {
    type Output = Abstraction;
    fn index(&self, a: AbsId) -> &Abstraction {
        &self.abs[a.0 as usize]
    }
}

impl std::ops::IndexMut<AbsId> for Heap {
    fn index_mut(&mut self, a: AbsId) -> &mut Abstraction {
        &mut self.abs[a.0 as usize]
    }
}

impl std::ops::Index<ClassId> for Heap {
    type Output = ClassInfo;
    fn index(&self, c: ClassId) -> &ClassInfo {
        &self.classes[c.0 as usize]
    }
}

impl std::ops::IndexMut<ClassId> for Heap {
    fn index_mut(&mut self, c: ClassId) -> &mut ClassInfo {
        &mut self.classes[c.0 as usize]
    }
}

/// Whether a region root counts as a class label.
///
/// This is the one axis on which the two per-site receiver-class channels
/// differ. The agreement channel refuses it: a region is several classes,
/// so a site whose receiver is one has not settled on a class and must not
/// claim to have. The label channel accepts it, because the region rung's
/// whole job is to notice that every label a site saw lives in one region
/// -- and it cannot notice that if regions arrive unnamed.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum RegionLabels {
    Accept,
    Refuse,
}

/// A converted snapshot value.
#[derive(Clone, Copy)]
enum SVal {
    Fn(ScriptId),
    Obj(SourceObjectId),
    /// Prim mask plus the live value's interval claim (the heap-range
    /// channel's snapshot seed: an Int32/integral-Double carries its
    /// value, everything else the mask's default claim).
    Prim(Prims, super::types::Interval),
    /// A script-less (native) function with a name: carries the name's
    /// string object id; `ts_of_sval` resolves it to a reserved native
    /// fn id whose call result comes from the spec table.
    NativeFn(SourceObjectId),
}

fn sval(source: &Source, id: SourceObjectId) -> Option<SVal> {
    use super::types::Interval;
    if id.is_other() {
        return None;
    }
    Some(match source.object(id) {
        SourceObject::Object(ObjectData {
            kind: ObjectKind::Function,
            script: Some(s),
            ..
        }) => SVal::Fn(ScriptId::new(s.id())),
        SourceObject::Object(ObjectData {
            kind: ObjectKind::Function,
            script: None,
            name: Some(n),
            ..
        }) if !n.is_other() => SVal::NativeFn(*n),
        SourceObject::Object(ObjectData {
            non_native: false,
            kind: ObjectKind::Plain | ObjectKind::Array | ObjectKind::TypedArray(_),
            ..
        }) => SVal::Obj(id),
        SourceObject::String(_) => SVal::Prim(PRIM_STRING, Interval::Empty),
        SourceObject::Symbol => SVal::Prim(PRIM_SYMBOL, Interval::Empty),
        SourceObject::Primitive(p) => match p {
            Primitive::Undefined => SVal::Prim(PRIM_UNDEFINED, Interval::Empty),
            Primitive::Null => SVal::Prim(PRIM_NULL, Interval::Empty),
            Primitive::Boolean(_) => SVal::Prim(PRIM_BOOLEAN, Interval::Empty),
            Primitive::Int32(v) => SVal::Prim(PRIM_INT32, Interval::of_value(i64::from(*v))),
            Primitive::Double(v) => SVal::Prim(PRIM_DOUBLE, Interval::of_double(*v)),
        },
        _ => return None,
    })
}

impl Solver<'_> {
    /// Build the snapshot-derived identity maps and pre-fill the shared
    /// cells (gnames from the global object, aliased slots from captured
    /// CallObjects). This is the whole snapshot integration: initial state.
    pub(super) fn seed(&mut self) {
        let mut script_proto: HashMap<ScriptId, Agreed<SourceObjectId>> = HashMap::default();
        let prototype = self.names_of.prototype;
        for (id, obj) in self.source.objects() {
            let SourceObject::Object(ObjectData {
                non_native: false,
                kind,
                script,
                properties,
                ..
            }) = obj
            else {
                continue;
            };
            let Some(s) = script else { continue };
            if *kind == ObjectKind::Function {
                self.heap
                    .script_fn_objs
                    .entry(ScriptId::new(s.id()))
                    .or_default()
                    .push(id);
            }
            for (k, v) in properties {
                if k.is_other() {
                    continue;
                }
                let SourceObject::String(name) = self.source.object(*k) else {
                    continue;
                };
                if !name
                    .chars()
                    .iter()
                    .copied()
                    .eq(self.names.get(prototype).iter().copied())
                {
                    continue;
                }
                let Some(SVal::Obj(p)) = sval(self.source, *v) else {
                    continue;
                };
                let s = ScriptId::new(s.id());
                self.heap.proto_owner.entry(p).or_insert(s);
                observe(&mut script_proto, s, p);
            }
            let _ = id;
        }
        // A constructor seen with two different `.prototype` objects has
        // no class identity, so it keeps none.
        self.heap.script_proto = script_proto
            .into_iter()
            .filter_map(|(s, p)| p.value().map(|p| (s, p)))
            .collect();

        // Gnames: the live global object's properties are the initial state
        // of the GName cells.
        if let Some(g) = self.source.global_object {
            let props: Vec<(JsString, SourceObjectId)> = match self.source.object(g) {
                SourceObject::Object(ObjectData { properties, .. }) => properties
                    .iter()
                    .filter_map(|(k, v)| {
                        if k.is_other() {
                            return None;
                        }
                        let SourceObject::String(name) = self.source.object(*k) else {
                            return None;
                        };
                        Some((JsString::from_chars(name.chars().to_vec()), *v))
                    })
                    .collect(),
                _ => Vec::new(),
            };
            let mut seeded: HashSet<NameId> = HashSet::default();
            let mut seeded_objs: HashSet<NameId> = HashSet::default();
            for (name, v) in props {
                let Some(v) = sval(self.source, v) else {
                    continue;
                };
                let ts = self.ts_of_sval(v);
                let name = self.names.intern(name.chars());
                seeded.insert(name);
                if matches!(v, SVal::Obj(_)) {
                    seeded_objs.insert(name);
                }
                let cell = self.engine.cell(CellKey::GName(name));
                self.engine.raise(cell, &ts, (SEED, CTX0));
            }
            // A binding transcribed as a bare native fn (`Object`) has no
            // property cells of its own, so only a real transcribed OBJECT
            // suppresses its namespace; the fn-only seed and the namespace
            // join in the same gname cell (same reserved ctor id).
            self.seed_native_namespaces(&seeded_objs);
            self.seed_bare_natives(&seeded);
            self.seed_intrinsic_natives();
        }
        // Aliased slots: captured CallObject values. Load-bearing --
        // minified bundles reach most of their classes through short
        // closure aliases rather than through named globals.
        let mut slots: Vec<(SourceObjectId, EnvSlot, SourceObjectId)> = Vec::new();
        for (id, obj) in self.source.objects() {
            let SourceObject::Scope(ScopeData {
                env_slot_values, ..
            }) = obj
            else {
                continue;
            };
            for (slot, v) in env_slot_values {
                slots.push((id, EnvSlot::new(*slot), *v));
            }
        }
        for (scope, slot, v) in slots {
            let Some(v) = sval(self.source, v) else {
                continue;
            };
            let ts = self.ts_of_sval(v);
            let cell = self.engine.cell(CellKey::Aliased { scope, slot });
            self.engine.raise(cell, &ts, (SEED, CTX0));
        }
        // The global's abstraction must exist (bare-call receivers
        // population-bind to it in the interval channel). Interned last:
        // an earlier intern renumbers every downstream id for zero
        // semantic difference.
        if let Some(g) = self.source.global_object {
            let _ = self.intern_snap(g);
        }
    }

    fn ts_of_sval(&mut self, v: SVal) -> TypeSet {
        match v {
            SVal::Fn(s) => TypeSet::fn_one(FnId::script(s)),
            SVal::Obj(oid) => TypeSet::obj_one(self.intern_snap(oid)),
            SVal::Prim(p, interval) => {
                let mut ts = TypeSet::prim(p);
                ts.interval = interval;
                ts
            }
            SVal::NativeFn(nid) => {
                let SourceObject::String(s) = self.source.object(nid) else {
                    return TypeSet::default();
                };
                let chars = s.chars().to_vec();
                // The Array/TA constructor names keep their existing
                // reserved ids (allocation semantics; the scan-side gname
                // path mints the same ids, and the sets must agree).
                if builtins::is_array_ctor_name(&chars) {
                    return TypeSet::fn_one(FnId::ARRAY_CTOR);
                }
                if let Some(ta) = builtins::ta_kind_for_ctor_name(&chars) {
                    return TypeSet::fn_one(FnId::typed_array_ctor(ta));
                }
                let name = self.names.intern(&chars);
                TypeSet::fn_one(self.native_id(NativeKind::Bare, name))
            }
        }
    }

    /// Modeled self-hosted intrinsics: the scan reads `GetIntrinsic name`
    /// as the %-mangled gname (the intrinsic environment is not the global
    /// object, and '%' cannot appear in a user identifier), so seeding the
    /// mangled cell with the named native resolves the kernel calls the
    /// self-hosted string code bottoms out in. Leaving a kernel such as
    /// `Substring` unresolved would make the RegExp-replace buildup's
    /// results unresolved evidence and push every concat of one off the
    /// Opt track.
    fn seed_intrinsic_natives(&mut self) {
        // (intrinsic name, bare name the result mask resolves through).
        const INTRINSICS: &[(&str, &str)] = &[
            ("Substring", "Substring"),
            ("ToString", "ToString"),
            ("ToObject", "ToObject"),
            ("IsObject", "IsObject"),
            ("ToLength", "ToLength"),
            ("Number_isNaN", "Number_isNaN"),
            (
                "UnsafeGetStringFromReservedSlot",
                "UnsafeGetStringFromReservedSlot",
            ),
            ("RegExpMatcher", "RegExpMatcher"),
            ("RegExpSearcher", "RegExpSearcher"),
            ("RegExpSearcherLastLimit", "RegExpSearcherLastLimit"),
            ("RegExpHasCaptureGroups", "RegExpHasCaptureGroups"),
            ("RegExpGetSubstitution", "RegExpGetSubstitution"),
            ("IsOptimizableRegExpObject", "IsOptimizableRegExpObject"),
            ("SubstringKernel", "SubstringKernel"),
            ("StringSplitString", "StringSplitString"),
            ("GuardToSetObject", "GuardToSetObject"),
            ("ToInteger", "ToInteger"),
            (
                "UnsafeGetInt32FromReservedSlot",
                "UnsafeGetInt32FromReservedSlot",
            ),
            ("ThrowIncompatibleMethod", "ThrowIncompatibleMethod"),
            ("ThrowTypeError", "ThrowTypeError"),
            ("IsCallable", "IsCallable"),
            ("AdvanceStringIndex", "AdvanceStringIndex"),
            ("GuardToMapObject", "GuardToMapObject"),
            ("std_Math_max", "max"),
            ("std_Math_min", "min"),
        ];
        for &(n, result_as) in INTRINSICS {
            let bare: Vec<u16> = result_as.encode_utf16().collect();
            let mut chars: Vec<u16> = vec![u16::from(b'%')];
            chars.extend(n.encode_utf16());
            let mangled = self.names.intern(&chars);
            let id = self.natives.intern(NativeKind::Bare, mangled, &bare);
            let cell = self.engine.cell(CellKey::GName(mangled));
            self.engine.raise(cell, &TypeSet::fn_one(id), (SEED, CTX0));
        }
    }

    /// Bare global native converters the walker leaves other (a native
    /// JSFunction is untranscribable): seed their GName cells with the
    /// modeled native id, same likely-not-proof contract as the
    /// namespaces below -- every consumer guards callee identity at
    /// runtime, so a shadowed binding self-misses.
    fn seed_bare_natives(&mut self, seeded: &HashSet<NameId>) {
        for n in [
            "parseInt",
            "parseFloat",
            "isNaN",
            "isFinite",
            "print",
            "Error",
            "TypeError",
            "RangeError",
            "ReferenceError",
            "SyntaxError",
            "EvalError",
            "URIError",
        ] {
            let name = self.names.intern_str(n);
            if seeded.contains(&name) {
                continue;
            }
            let id = self.native_id(NativeKind::Bare, name);
            let cell = self.engine.cell(CellKey::GName(name));
            self.engine.raise(cell, &TypeSet::fn_one(id), (SEED, CTX0));
        }
    }

    /// Synthesize the builtin namespaces the walker could not transcribe:
    /// a namespace whose global binding was captured as a real object is
    /// skipped (its own property cells win); an absent-or-other binding
    /// gets a synthetic abstraction with spec-seeded method/const cells.
    fn seed_native_namespaces(&mut self, seeded: &HashSet<NameId>) {
        for (i, ns) in builtins::NAMESPACES.iter().enumerate() {
            let gname = self.names.intern_str(ns.global);
            if seeded.contains(&gname) {
                continue;
            }
            let abs = self.new_abs(AbsKey::NativeNs(u8::try_from(i).unwrap()));
            self.heap[abs].seeded = true;
            for m in ns.methods {
                let mname = self.names.intern_str(m);
                let id = self.native_id(NativeKind::Bare, mname);
                let cell = self.field_cell(abs, mname);
                self.engine.raise(cell, &TypeSet::fn_one(id), (SEED, CTX0));
            }
            for (c, mask) in ns.consts {
                let cname = self.names.intern_str(c);
                let cell = self.field_cell(abs, cname);
                self.engine.raise(cell, &TypeSet::prim(*mask), (SEED, CTX0));
            }
            let mut ts = TypeSet::obj_one(abs);
            if ns.ctor {
                let id = self.native_id(NativeKind::Bare, gname);
                ts.fns = super::types::BoundedFnSet::one(id);
            }
            let cell = self.engine.cell(CellKey::GName(gname));
            self.engine.raise(cell, &ts, (SEED, CTX0));
        }
    }

    /// Get-or-mint the reserved fn id for a (kind, name) native, resolving
    /// its spec result mask once.
    fn native_id(&mut self, kind: NativeKind, name: NameId) -> FnId {
        let chars = self.names.get(name).to_vec();
        self.natives.intern(kind, name, &chars)
    }

    /// The modeled call result for a named-native id: the spec table's
    /// mask, or the unknown evidence bit for natives we do not model.
    /// `args_integral`: every argument at the site is integrally ranged
    /// (the integral-preserving natives claim I53 under it).
    pub(super) fn native_ret(&self, f: FnId, args_integral: bool) -> TypeSet {
        let info = self.natives.get(f);
        let mask = info.and_then(|i| i.result);
        let mut ts = mask.map_or_else(TypeSet::unknown_evidence, TypeSet::prim);
        if mask.is_some()
            && info.is_some_and(|i| {
                let name = self.names.get(i.name);
                builtins::integral_native(name)
                    || (args_integral && builtins::integral_preserving_native(name))
            })
        {
            ts.range = super::types::Range::I53;
        }
        ts
    }

    fn new_abs(&mut self, key: AbsKey) -> AbsId {
        let id = AbsId(u32::try_from(self.heap.abs.len()).unwrap());
        self.heap.abs.push(Abstraction {
            key,
            class: None,
            proto: ProtoLink::None,
            owner_class: None,
            proto_of: None,
            ta_kind: None,
            is_array: false,
            seeded: false,
        });
        // The engine's parallel join-metadata vec (consulted by every
        // join) must grow in lockstep.
        self.engine.abs_labels.push(AbsLabels::default());
        self.heap.abs_ids.insert(key, id);
        id
    }

    fn set_abs_class(&mut self, a: AbsId, c: ClassId) {
        self.heap[a].class = Some(c);
        self.engine.abs_labels[a.0 as usize].class = Some(c);
    }

    pub(super) fn intern_snap(&mut self, oid: SourceObjectId) -> AbsId {
        if let Some(&a) = self.heap.abs_ids.get(&AbsKey::Snap(oid)) {
            return a;
        }
        // Insert before resolving class/proto: the bridge and proto walks
        // may re-enter for objects up the chain.
        let a = self.new_abs(AbsKey::Snap(oid));
        self.engine.abs_labels[a.0 as usize].snap = true;
        let sobj = self.source.object(oid);
        let (kind, proto) = match sobj {
            SourceObject::Object(ObjectData {
                non_native: false,
                kind,
                proto,
                ..
            }) => (*kind, *proto),
            _ => (ObjectKind::Other, None),
        };
        self.heap[a].is_array = kind == ObjectKind::Array;
        self.engine.abs_labels[a.0 as usize].array = kind == ObjectKind::Array;
        if let ObjectKind::TypedArray(code) = kind {
            if let Some(&tk) = crate::opsem::TaKind::ALL.get(usize::from(code).wrapping_sub(1)) {
                self.heap[a].ta_kind = Some(tk);
            }
        }
        if let Some(pid) = proto {
            // The concrete->class bridge: an object whose `[[Prototype]]` is
            // some constructor's `.prototype` is an instance of that class.
            if let Some(&ctor) = self.heap.proto_owner.get(&pid) {
                let c = self.class_for_fn(ctor);
                self.set_abs_class(a, c);
            }
            let pa = self.intern_snap(pid);
            self.heap[a].proto = ProtoLink::Abs(pa);
        }
        a
    }

    pub(super) fn intern_alloc(
        &mut self,
        script: ScriptId,
        pc: Pc,
        ctx: CtxId,
        class: Option<ClassId>,
        is_array: bool,
        ta_kind: Option<TaKind>,
    ) -> AbsId {
        let key = AbsKey::Alloc { script, pc, ctx };
        if let Some(&a) = self.heap.abs_ids.get(&key) {
            return a;
        }
        let a = self.new_abs(key);
        self.heap[a].is_array = is_array;
        self.engine.abs_labels[a.0 as usize].array = is_array;
        self.heap[a].ta_kind = ta_kind;
        match class {
            Some(c) => {
                self.set_abs_class(a, c);
                self.heap[a].proto = ProtoLink::Abs(self.heap[c].proto_abs);
            }
            None => {
                let c = self.site_class(script, pc);
                self.set_abs_class(a, c);
                if ta_kind.is_some() {
                    self.heap[c].ta_kind = ta_kind;
                }
                if is_array {
                    self.heap[c].is_array = true;
                    self.engine.array_classes.insert(c);
                }
            }
        }
        a
    }

    /// The per-site pseudo-class of a classless allocation site.
    fn site_class(&mut self, script: ScriptId, pc: Pc) -> ClassId {
        let key = ClassKey::Site(Site::new(script, pc));
        match self.heap.class_ids.get(&key) {
            Some(&c) => c,
            None => self.new_class(key, None),
        }
    }

    fn intern_fn_obj(&mut self, script: ScriptId) -> AbsId {
        if let Some(&a) = self.heap.abs_ids.get(&AbsKey::FnObj(script)) {
            return a;
        }
        self.new_abs(AbsKey::FnObj(script))
    }

    /// Mint (or fetch) the class of constructor script `f`. Identity:
    /// the snapshot-agreed `.prototype` object, else the script.
    /// Mint a class and its synthetic prototype abstraction.
    ///
    /// The prototype abstraction back-references the class, so the class
    /// row is reserved first and its `proto_abs` patched afterwards; that
    /// ordering is why the row is briefly published with the `AbsId::MAX`
    /// sentinel, and why this is one function rather than something each
    /// caller assembles.
    fn new_class(&mut self, key: ClassKey, ctor: Option<ScriptId>) -> ClassId {
        let c = ClassId(u32::try_from(self.heap.classes.len()).unwrap());
        self.heap.classes.push(ClassInfo {
            key,
            ctor,
            proto_abs: AbsId(u32::MAX),
            sources: Vec::new(),
            ta_kind: None,
            is_array: false,
        });
        self.heap.class_ids.insert(key, c);
        let pa = self.new_abs(AbsKey::ProtoOf(c));
        self.heap[pa].proto_of = Some(c);
        self.heap[pa].owner_class = Some(c);
        self.heap[c].proto_abs = pa;
        c
    }

    pub(super) fn class_for_fn(&mut self, f: ScriptId) -> ClassId {
        let key = match self.heap.script_proto.get(&f) {
            Some(&p) => ClassKey::Proto(p),
            None => ClassKey::Script(f),
        };
        self.class_for_key(key, Some(f), f)
    }

    /// Get-or-mint the class named by `key`, homing `f`'s `this` to it and
    /// registering the concrete prototype object as a method-table source
    /// when the key names one.
    fn class_for_key(&mut self, key: ClassKey, ctor: Option<ScriptId>, f: ScriptId) -> ClassId {
        if let Some(&c) = self.heap.class_ids.get(&key) {
            return c;
        }
        let c = self.new_class(key, ctor);
        if let ClassKey::Proto(p) = key {
            let src = self.intern_snap(p);
            self.register_proto_source(c, src);
        }
        self.this_home_add(f, c);
        c
    }

    /// Mint (or fetch) the class of a shared-generated ctor's concrete
    /// class object: identity is the object's own `.prototype` (many
    /// classes share the script, so `class_for_fn`'s script fallback
    /// collapses them). Same construction as `class_for_fn`'s Proto arm;
    /// registering the concrete prototype source homes its method
    /// scripts (`note_method_home`), which pins the methods' `this` to
    /// the class.
    pub(super) fn class_for_ctor_proto(&mut self, f: ScriptId, p: SourceObjectId) -> ClassId {
        // No ctor attribution: the script is shared, and a ctor-keyed
        // group id would collapse every such class into one group. A
        // class-keyed group (the lit-class rule) keeps each its own
        // layout-key range for the per-site emission.
        self.class_for_key(ClassKey::Proto(p), None, f)
    }

    /// Pre-solve resolution of shared-generated-ctor construct sites
    /// (the prototype.js `Class.create()` idiom). Purely syntactic +
    /// concrete: a ctor script whose `this` events are delegations only
    /// (no direct writes) is shared-generated; each construct site's
    /// callee def chain (gname/aliased roots, property hops) resolves
    /// against the snapshot to the concrete function object, whose
    /// `.prototype` keys the per-class identity and carries the member
    /// the `this.<init>.apply` dispatch reaches. Fills
    /// `site_ctor_class` (consumed at construct evaluation) and
    /// `shared_ctor_sites` (consumed by the emit-phase layout minting).
    pub(super) fn resolve_shared_ctor_sites(&mut self) {
        use super::engine::CKey;
        use super::scan::TEvent;
        let mut deleg_pcs: HashMap<ScriptId, Vec<Pc>> = HashMap::default();
        for (&sid, evs) in &self.tables.this_events {
            if evs.iter().any(|e| matches!(e, TEvent::Write(_))) {
                continue;
            }
            let pcs: Vec<Pc> = evs
                .iter()
                .filter_map(|e| match e {
                    TEvent::Deleg(pc) => Some(*pc),
                    _ => None,
                })
                .collect();
            if !pcs.is_empty() {
                deleg_pcs.insert(sid, pcs);
            }
        }
        if deleg_pcs.is_empty() {
            return;
        }
        let mut read_defs: HashMap<(ScriptId, VarId), (CKey, NameId)> = HashMap::default();
        let mut csites: Vec<(Site, CKey)> = Vec::new();
        let mut apply_tgt: HashMap<Site, CKey> = HashMap::default();
        for ci in 0..self.engine.cons.len() {
            let script = self.engine.con_script[ci];
            match &self.engine.cons[ci] {
                Constraint::Read {
                    recv,
                    name,
                    dst: CKey::Var(v),
                    ..
                } => {
                    read_defs.insert((script, *v), (*recv, *name));
                }
                Constraint::Call {
                    callee,
                    pc,
                    construct: true,
                    ..
                } => {
                    csites.push((Site::new(script, *pc), *callee));
                }
                Constraint::Apply { target, pc, .. } => {
                    apply_tgt.insert(Site::new(script, *pc), *target);
                }
                _ => {}
            }
        }
        let mut shared_init: HashMap<ScriptId, NameId> = HashMap::default();
        for (&f, pcs) in &deleg_pcs {
            for &dpc in pcs {
                let Some(&CKey::Var(tv)) = apply_tgt.get(&Site::new(f, dpc)) else {
                    continue;
                };
                let Some(&(CKey::This, n)) = read_defs.get(&(f, tv)) else {
                    continue;
                };
                shared_init.insert(f, n);
                break;
            }
        }
        if shared_init.is_empty() {
            return;
        }
        fn obj_prop(
            source: &Source,
            names: &super::types::Names,
            oid: SourceObjectId,
            name: NameId,
        ) -> Option<SourceObjectId> {
            if oid.is_other() {
                return None;
            }
            let SourceObject::Object(ObjectData { properties, .. }) = source.object(oid) else {
                return None;
            };
            let want = names.get(name);
            for (k, v) in properties {
                if k.is_other() {
                    continue;
                }
                let SourceObject::String(s) = source.object(*k) else {
                    continue;
                };
                if s.chars() == want.chars() {
                    return Some(*v);
                }
            }
            None
        }
        fn resolve_concrete(
            source: &Source,
            names: &super::types::Names,
            read_defs: &HashMap<(ScriptId, VarId), (CKey, NameId)>,
            script: ScriptId,
            key: CKey,
            depth: u32,
        ) -> Option<SourceObjectId> {
            if depth > 8 {
                return None;
            }
            match key {
                CKey::GName(n) => {
                    let g = source.global_object?;
                    obj_prop(source, names, g, n)
                }
                CKey::Var(v) => {
                    let &(recv, name) = read_defs.get(&(script, v))?;
                    let r = resolve_concrete(source, names, read_defs, script, recv, depth + 1)?;
                    obj_prop(source, names, r, name)
                }
                CKey::Aliased { scope, slot } => {
                    let SourceObject::Scope(ScopeData {
                        env_slot_values, ..
                    }) = source.object(scope)
                    else {
                        return None;
                    };
                    env_slot_values
                        .iter()
                        .find(|(s, _)| EnvSlot::new(*s) == slot)
                        .map(|(_, v)| *v)
                }
                _ => None,
            }
        }
        let n_prototype = self.names_of.prototype;
        // Two passes: resolve every site first, then commit only ctors
        // that are truly shared (>= 2 distinct prototypes across their
        // sites). A single-class apply wrapper is fully served by the
        // script-keyed machinery, and swapping its model identity for a
        // proto-keyed class costs it real speed for nothing.
        let mut resolved: Vec<(Site, SharedCtorSite)> = Vec::new();
        let mut protos_of: HashMap<ScriptId, HashSet<SourceObjectId>> = HashMap::default();
        for (site, callee) in csites {
            let Some(fo) =
                resolve_concrete(self.source, &self.names, &read_defs, site.script, callee, 0)
            else {
                continue;
            };
            let Some(f) = self.source.fn_script(fo) else {
                continue;
            };
            let Some(&init_name) = shared_init.get(&f) else {
                continue;
            };
            let Some(proto) = obj_prop(self.source, &self.names, fo, n_prototype) else {
                continue;
            };
            if proto.is_other() {
                continue;
            }
            let Some(init_fo) = obj_prop(self.source, &self.names, proto, init_name) else {
                continue;
            };
            let Some(init_sid) = self.source.fn_script(init_fo) else {
                continue;
            };
            protos_of.entry(f).or_default().insert(proto);
            resolved.push((
                site,
                SharedCtorSite {
                    ctor: f,
                    proto,
                    init: init_sid,
                },
            ));
        }
        for (site, shared) in resolved {
            if protos_of.get(&shared.ctor).is_none_or(|ps| ps.len() < 2) {
                continue;
            }
            let c = self.class_for_ctor_proto(shared.ctor, shared.proto);
            self.site_ctor_class.insert(site, c);
            self.shared_ctor_sites.insert(site, shared);
        }
    }

    /// Register a concrete prototype object as a source of `c`'s method
    /// table: per-name standing links both for names already interned and
    /// (via `field_cell`'s owner check) names interned later. Never value
    /// flow: the object's cells feed the table, nothing is merged.
    pub(super) fn register_proto_source(&mut self, c: ClassId, src: AbsId) {
        self.register_proto_source_impl(c, src, true);
    }

    /// The linking half of `register_proto_source` alone: the object's
    /// cells feed `c`'s method table, but `c` neither owns the object nor
    /// homes its methods. For the fn-keyed class of a SHARED ctor script
    /// (prototype.js `Class.create()`): `SharedCtor.prototype.m(...)`
    /// resolution needs the union table over every sharing class's
    /// prototype, while homing to that one class would demote every
    /// per-prototype pin.
    pub(super) fn link_proto_table(&mut self, c: ClassId, src: AbsId) {
        self.register_proto_source_impl(c, src, false);
    }

    fn register_proto_source_impl(&mut self, c: ClassId, src: AbsId, own: bool) {
        if self.heap[c].sources.contains(&src) {
            return;
        }
        self.heap[c].sources.push(src);
        if let AbsKey::Alloc { script, pc, .. } = self.heap[src].key {
            self.heap.site_is_proto.insert(Site::new(script, pc));
        }
        if own && self.heap[src].owner_class.is_none() {
            self.heap[src].owner_class = Some(c);
        }
        self.ensure_seeded(src);
        let pa = self.heap[c].proto_abs;
        // Class-level upward link: the table's chain continues where the
        // concrete prototype's chain does (first install wins).
        if self.heap[pa].proto == ProtoLink::None {
            if let ProtoLink::Abs(up) = self.heap[src].proto {
                self.heap[pa].proto = ProtoLink::Abs(up);
                let s = self.engine.cell(CellKey::ProtoSentinel(pa));
                self.engine
                    .raise(s, &TypeSet::prim(PRIM_NULL), (SEED, CTX0));
            }
        }
        let names: Vec<NameId> = self
            .heap
            .fields_of
            .get(&pa)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .chain(self.heap.fields_of.get(&src).cloned().unwrap_or_default())
            .collect();
        for name in names {
            let sc = self.field_cell(src, name);
            let dc = self.field_cell(pa, name);
            self.engine.link(sc, dc);
        }
        // Methods written into the object before it became a prototype
        // (`F.prototype = {m: fn}` inits the literal first) still get homed.
        if own {
            for name in self.heap.fields_of.get(&src).cloned().unwrap_or_default() {
                let cell = self.field_cell(src, name);
                let v = self.engine.ts(cell).clone();
                self.note_method_home(c, &v);
            }
        }
    }

    /// Seed `abs` from the snapshot if it has not been, then intern its
    /// field cell.
    ///
    /// The order matters and is why this is a helper rather than
    /// `field_cell` doing the seeding itself: seeding interns cells of its
    /// own, so folding it in would mint this field's cell before them and
    /// renumber the cell space.
    fn seeded_field_cell(&mut self, abs: AbsId, name: NameId) -> CellId {
        self.ensure_seeded(abs);
        self.field_cell(abs, name)
    }

    /// The bundle-wide union of every array abstraction's elements.
    fn elems_union(&mut self) -> CellId {
        self.engine.cell(CellKey::ArrayElemsUnion)
    }

    /// Read a cell on behalf of `user` and join it into `out`.
    fn read_join(&mut self, cell: CellId, user: (ConId, CtxId), out: &mut TypeSet) {
        let v = self.engine.read(cell, user);
        let _ = self.engine.join_ts(out, &v);
    }

    /// The class of the view a receiver of class `c` reads `name` through.
    /// Elements are read through the region root, so a merged array
    /// population shares one element node; every other name reads its own
    /// class's view.
    fn view_class(&self, c: ClassId, is_elems: bool) -> ClassId {
        if is_elems {
            self.engine.region_root(c)
        } else {
            c
        }
    }

    /// Intern `Field(abs, name)`, installing its standing edges on first
    /// creation: proto-source feeds, method-table feeds, and the ClassView
    /// feed for classed instances.
    pub(super) fn field_cell(&mut self, abs: AbsId, name: NameId) -> CellId {
        let key = CellKey::Field { abs, name };
        if let Some(c) = self.engine.lookup(key) {
            return c;
        }
        let cell = self.engine.cell(key);
        self.heap.fields_of.entry(abs).or_default().push(name);
        let info = &self.heap[abs];
        let proto_of = info.proto_of;
        let owner = info.owner_class;
        let class = info.class;
        let info_is_array = info.is_array;
        if let Some(c) = proto_of {
            for src in self.heap[c].sources.clone() {
                let sc = self.field_cell(src, name);
                self.engine.link(sc, cell);
            }
        }
        if let Some(c) = owner {
            if proto_of != Some(c) {
                let pa = self.heap[c].proto_abs;
                let dc = self.field_cell(pa, name);
                self.engine.link(cell, dc);
            }
        }
        if let Some(c) = class {
            let view = self.engine.cell(CellKey::ClassView { class: c, name });
            self.engine.link(cell, view);
        }
        if name == self.names_of.elems && info_is_array {
            let union = self.engine.cell(CellKey::ArrayElemsUnion);
            self.engine.link(cell, union);
        }
        cell
    }

    fn class_field_cell(&mut self, class: ClassId, name: NameId) -> CellId {
        let key = CellKey::ClassField { class, name };
        if let Some(c) = self.engine.lookup(key) {
            return c;
        }
        let cell = self.engine.cell(key);
        let view = self.engine.cell(CellKey::ClassView { class, name });
        self.engine.link(cell, view);
        cell
    }

    /// Pre-fill a snapshot abstraction's field cells from the transcribed
    /// heap, once, on first field access.
    pub(super) fn ensure_seeded(&mut self, abs: AbsId) {
        if self.heap[abs].seeded {
            return;
        }
        self.heap[abs].seeded = true;
        let oid = match self.heap[abs].key {
            AbsKey::Snap(oid) => oid,
            AbsKey::FnObj(s) => {
                self.seed_fn_obj(abs, s);
                return;
            }
            _ => return,
        };
        let (props, elems): (Vec<(JsString, SourceObjectId)>, Vec<SourceObjectId>) =
            match self.source.object(oid) {
                SourceObject::Object(ObjectData {
                    non_native: false,
                    properties,
                    elements,
                    ..
                }) => (
                    properties
                        .iter()
                        .filter_map(|(k, v)| {
                            if k.is_other() {
                                return None;
                            }
                            let SourceObject::String(name) = self.source.object(*k) else {
                                return None;
                            };
                            Some((JsString::from_chars(name.chars().to_vec()), *v))
                        })
                        .collect(),
                    elements.iter().map(|(_, v)| *v).collect(),
                ),
                _ => return,
            };
        for (name, v) in props {
            let Some(v) = sval(self.source, v) else {
                continue;
            };
            let ts = self.ts_of_sval(v);
            let name = self.names.intern(name.chars());
            let cell = self.field_cell(abs, name);
            self.engine.raise(cell, &ts, (SEED, CTX0));
        }
        if !elems.is_empty() {
            let mut ts = TypeSet::default();
            let mut fns: Vec<FnId> = Vec::new();
            for v in elems {
                let Some(v) = sval(self.source, v) else {
                    continue;
                };
                if let SVal::Fn(s) = v {
                    fns.push(FnId::script(s));
                }
                let t = self.ts_of_sval(v);
                ts.join_from(&t, &self.engine.abs_labels, &mut self.engine.sink);
            }
            // Fn-table member list: the elems cell saturates
            // to fn-multi past the BoundedFnSet cap, but the live wizer image
            // holds the load-time population -- seed it for arg-binding
            // (runtime registrations extend it via the write-side capture).
            if !fns.is_empty() {
                self.add_table_members(abs, &fns);
            }
            if !ts.is_empty() {
                let name = self.names_of.elems;
                let cell = self.field_cell(abs, name);
                self.engine.raise(cell, &ts, (SEED, CTX0));
            }
        }
    }

    /// Seed a script's `FnObj` statics space from every transcribed
    /// snapshot closure of the script (statics installed at wizen time
    /// exist only there; without this a `F.staticName` read is Empty
    /// forever). `.prototype` is identity, handled by the class maps.
    fn seed_fn_obj(&mut self, abs: AbsId, script: ScriptId) {
        let prototype = self.names_of.prototype;
        let oids = self
            .heap
            .script_fn_objs
            .get(&script)
            .cloned()
            .unwrap_or_default();
        for oid in oids {
            let props: Vec<(JsString, SourceObjectId)> = match self.source.object(oid) {
                SourceObject::Object(ObjectData {
                    non_native: false,
                    properties,
                    ..
                }) => properties
                    .iter()
                    .filter_map(|(k, v)| {
                        if k.is_other() {
                            return None;
                        }
                        let SourceObject::String(name) = self.source.object(*k) else {
                            return None;
                        };
                        Some((JsString::from_chars(name.chars().to_vec()), *v))
                    })
                    .collect(),
                _ => continue,
            };
            for (name, v) in props {
                let Some(v) = sval(self.source, v) else {
                    continue;
                };
                // Function- and prim-valued statics only: instance-valued
                // statics (BigInteger.ZERO) would join snapshot instances
                // into alloc-site-pure populations, merging classes that
                // never otherwise meet.
                if matches!(v, SVal::Obj(_)) {
                    continue;
                }
                let name = self.names.intern(name.chars());
                if name == prototype {
                    continue;
                }
                let ts = self.ts_of_sval(v);
                let cell = self.field_cell(abs, name);
                self.engine.raise(cell, &ts, (SEED, CTX0));
            }
        }
    }

    /// Fn-table member capture at an elems write: a
    /// single-fn write records directly; a saturated write sourced from
    /// an arg row merges that row's per-site fn record and registers the
    /// reverse feed so later registrations append without a re-fire.
    fn note_table_members(
        &mut self,
        a: AbsId,
        src: super::engine::CKey,
        script: ScriptId,
        v: &TypeSet,
    ) {
        if v.fns.is_multi() {
            let super::engine::CKey::Arg(i) = src else {
                return;
            };
            let feeds = self.arg_row_tables.entry((script, i)).or_default();
            if !feeds.contains(&a) {
                feeds.push(a);
            }
            let ids: Vec<FnId> = self
                .arg_fn_members
                .get(&(script, i))
                .map_or_else(Vec::new, |s| s.iter().copied().collect());
            if !ids.is_empty() {
                self.add_table_members(a, &ids);
            }
            return;
        }
        let ids: Vec<FnId> = v
            .fns
            .ids()
            .iter()
            .copied()
            .filter(|&f| !f.is_builtin())
            .collect();
        if !ids.is_empty() {
            self.add_table_members(a, &ids);
        }
    }

    /// Monotone chain join from `holder`'s proto upward: joins each level's
    /// own field cell, subscribing the reader along the way; a dead end
    /// subscribes the holder's proto sentinel so a later install re-fires.
    fn chain_join(&mut self, holder: AbsId, name: NameId, user: (ConId, CtxId), out: &mut TypeSet) {
        let mut cur = holder;
        for _ in 0..CHAIN_DEPTH {
            match self.heap[cur].proto {
                ProtoLink::None => {
                    let s = self.engine.cell(CellKey::ProtoSentinel(cur));
                    let _ = self.engine.read(s, user);
                    return;
                }
                ProtoLink::Abs(p) => {
                    let f = self.seeded_field_cell(p, name);
                    self.read_join(f, user, out);
                    cur = p;
                }
            }
        }
        // Ran out of depth with the chain still going: the levels above
        // were never joined.
        self.stats.caps.proto_chain += 1;
    }

    /// Add `c` to `sid`'s home classes (cell-side this-attribution):
    /// installs ThisField -> ClassField links for every name already
    /// this-written, and propagates through recorded this-forwarding
    /// delegation edges. Capped: a script homed everywhere is a shared
    /// helper, and linking it into every class merges their field cells
    /// into one useless claim.
    pub(super) fn this_home_add(&mut self, sid: ScriptId, c: ClassId) {
        {
            let homes = self.this_homes.entry(sid).or_default();
            if homes.contains(&c) {
                return;
            }
            if homes.len() >= MAX_HOMES {
                self.stats.caps.this_homes += 1;
                return;
            }
            homes.push(c);
        }
        for name in self.this_field_names.get(&sid).cloned().unwrap_or_default() {
            let src = self.engine.cell(CellKey::ThisField { script: sid, name });
            let dst = self.class_field_cell(c, name);
            self.engine.link(src, dst);
        }
        for d in self.this_delegs.get(&sid).cloned().unwrap_or_default() {
            self.this_home_add(d, c);
        }
    }

    /// Record a this-forwarding call edge (caller `f` hands its `this` to
    /// callee `g`): `g`'s this-writes attribute to `f`'s home classes.
    pub(super) fn this_deleg_add(&mut self, f: ScriptId, g: ScriptId) {
        let ds = self.this_delegs.entry(f).or_default();
        if ds.contains(&g) {
            return;
        }
        ds.push(g);
        for c in self.this_homes.get(&f).cloned().unwrap_or_default() {
            self.this_home_add(g, c);
        }
    }

    /// Raise a this-write into the script's ThisField cell (minting its
    /// home links on first use of the name).
    fn this_field_raise(&mut self, sid: ScriptId, name: NameId, v: &TypeSet, user: (ConId, CtxId)) {
        let key = CellKey::ThisField { script: sid, name };
        let cell = if let Some(c) = self.engine.lookup(key) {
            c
        } else {
            let c = self.engine.cell(key);
            self.this_field_names.entry(sid).or_default().push(name);
            for home in self.this_homes.get(&sid).cloned().unwrap_or_default() {
                let dst = self.class_field_cell(home, name);
                self.engine.link(c, dst);
            }
            c
        };
        self.engine.raise(cell, v, user);
    }

    /// Method-home attribution: a function value written into a class's
    /// method table homes the method script to the ctor (first install
    /// wins; a differing second install demotes).
    fn note_method_home(&mut self, owner: ClassId, v: &TypeSet) {
        if v.fns.is_multi() {
            return;
        }
        // The this-assertion: a method homed to a likely-class asserts that
        // `this` entering the method IS that class, independent of call
        // resolution -- polymorphic dispatch sites (a task queue holding
        // four task kinds) leave the receiver AnyObject, but each method
        // body still reads/writes its own class's cells precisely. A method
        // installed on two classes gets both seeds and joins to AnyObject:
        // the honest answer for genuinely shared methods.
        for m in v.fns.scripted() {
            // Pin bookkeeping: a single-homed method's `this` is asserted;
            // `bind_this_ok` refuses worse-than-asserted (AnyObject/AnyOf)
            // receivers. A second differing install unpins (shared method:
            // both seeds join to AnyObject below, callers bind normally).
            let first_pin = {
                let pin = self.this_pin.entry(m).or_default();
                let fresh = *pin == Agreed::Unset;
                pin.observe(owner);
                fresh
            };
            if first_pin {
                self.this_home_add(m, owner);
            }
            let this_cell = self.engine.cell(CellKey::This {
                script: m,
                ctx: CTX0,
            });
            let ts = TypeSet {
                obj: ObjType::ClassAny(owner),
                ..TypeSet::default()
            };
            self.engine.raise(this_cell, &ts, (SEED, CTX0));
        }
        let Some(ctor) = self.heap[owner].ctor else {
            return;
        };
        for m in v.fns.scripted() {
            observe(&mut self.heap.method_home, m, ctor);
        }
    }

    pub(super) fn eval_heap(&mut self, con: ConId, ctx: CtxId) -> bool {
        let sid = self.engine.con_script[con.0 as usize];
        let user = (con, ctx);
        match self.engine.cons[con.0 as usize].clone() {
            Constraint::Read {
                recv,
                name,
                dst,
                pc,
                callee_pos,
            } => {
                let r = self.engine.resolve(sid, ctx, recv);
                let rts = self.engine.read(r, user);
                self.trace_site_eval(sid, pc, ctx, recv, r, &rts);
                let d = self.engine.resolve(sid, ctx, dst);
                let mut out = TypeSet::default();
                let region_contributed = self.read_into(&rts, name, callee_pos, user, &mut out);
                if callee_pos && region_contributed {
                    if let super::engine::CKey::Var(v) = dst {
                        self.region_calls.insert((sid, v));
                    }
                }
                // Recorded for every elems read, not just callee position:
                // an apply-form dispatch (`action[0].call(...)`) consumes
                // the read's result as its TARGET, and the fn-table
                // fallback needs the same provenance there.
                if name == self.names_of.elems {
                    if let super::engine::CKey::Var(v) = dst {
                        self.elems_callee_vars.insert((sid, v), recv);
                    }
                }
                self.note_site_recv(sid, pc, &rts);
                self.note_site_evidence(sid, pc, name, &rts, Some(&out));
                self.engine.raise(d, &out, user);
                true
            }
            Constraint::Write {
                recv,
                name,
                src,
                pc,
            } => {
                let r = self.engine.resolve(sid, ctx, recv);
                let rts = self.engine.read(r, user);
                let s = self.engine.resolve(sid, ctx, src);
                let v = self.engine.read(s, user);
                if name == self.names_of.elems {
                    if let ObjType::One(a) = rts.obj {
                        self.note_table_members(a, src, sid, &v);
                        if let AbsKey::Alloc { script, pc, .. } = self.heap[a].key {
                            self.heap.dyn_named_writes.insert(Site::new(script, pc));
                        }
                    }
                }
                self.note_site_evidence(sid, pc, name, &rts, None);
                let this_recv = recv == super::engine::CKey::This && name != self.names_of.elems;
                if this_recv {
                    self.this_field_raise(sid, name, &v, user);
                }
                self.write_into(&rts, name, &v, this_recv, user);
                true
            }
            Constraint::Alloc { dst, pc, kind } => {
                let abs = match kind {
                    AllocKind::Snapshot(oid) => self.intern_snap(oid),
                    AllocKind::Plain => self.intern_alloc(sid, pc, ctx, None, false, None),
                    AllocKind::Array => self.intern_alloc(sid, pc, ctx, None, true, None),
                    AllocKind::TypedArray(k) => {
                        self.intern_alloc(sid, pc, ctx, None, false, Some(k))
                    }
                };
                let d = self.engine.resolve(sid, ctx, dst);
                self.engine.raise(d, &TypeSet::obj_one(abs), user);
                true
            }
            Constraint::ElemBuiltin {
                recv,
                arg,
                ret,
                pc: _,
                kind,
            } => {
                let r = self.engine.resolve(sid, ctx, recv);
                let rts = self.engine.read(r, user);
                let d = self.engine.resolve(sid, ctx, ret);
                let elems = self.names_of.elems;
                if kind == ElemBuiltinKind::Write {
                    if let Some(arg) = arg {
                        let s = self.engine.resolve(sid, ctx, arg);
                        let v = self.engine.read(s, user);
                        self.write_into(&rts, elems, &v, false, user);
                    }
                    self.engine.raise(d, &TypeSet::prim(PRIM_INT32), user);
                } else {
                    let mut out = TypeSet::prim(PRIM_UNDEFINED);
                    let _ = self.read_into(&rts, elems, false, user, &mut out);
                    self.engine.raise(d, &out, user);
                }
                true
            }
            _ => false,
        }
    }

    /// Read `name` off every part of receiver typeset `rts`, joining what
    /// each part yields into `out`. Returns whether a region's method
    /// table contributed a callee -- the caller records such sites so the
    /// emission can tell a flow-scoped dispatch set from a resolved one.
    fn read_into(
        &mut self,
        rts: &TypeSet,
        name: NameId,
        callee_pos: bool,
        user: (ConId, CtxId),
        out: &mut TypeSet,
    ) -> bool {
        self.trace_field("read", name, rts, None, user);
        let mut region_contributed = false;
        let is_elems = name == self.names_of.elems;
        let chain_ok = !is_elems;
        // Prim-receiver method resolution: a call off a known-string or
        // known-numeric receiver resolves modeled String/Number.prototype
        // natives (the receiver kind disambiguates names like slice).
        if callee_pos && rts.prims.intersects(PRIM_STRING | PRIM_INT32 | PRIM_DOUBLE) {
            let chars = self.names.get(name).to_vec();
            if rts.prims.intersects(PRIM_STRING)
                && builtins::prim_method(NativeKind::StringMethod, &chars)
            {
                let id = self.native_id(NativeKind::StringMethod, name);
                out.fns.insert(id, &mut self.engine.sink.dropped_fns);
            }
            if rts.prims.intersects(PRIM_INT32 | PRIM_DOUBLE)
                && builtins::prim_method(NativeKind::NumberMethod, &chars)
            {
                let id = self.native_id(NativeKind::NumberMethod, name);
                out.fns.insert(id, &mut self.engine.sink.dropped_fns);
            }
        }
        if rts.fns.is_multi() {
            // A lost-identity fn receiver: the property value is unknown,
            // but contributing fn-multi would poison the callee sets of
            // precise sibling contexts -- unknown contributes nothing.
            let mut any = TypeSet::unresolved();
            any.fns = Default::default();
            let _ = self.engine.join_ts(out, &any);
        } else {
            for f in rts.fns.scripted() {
                if name == self.names_of.prototype {
                    let c = self.class_for_fn(f);
                    let pa = self.heap[c].proto_abs;
                    let t = TypeSet::obj_one(pa);
                    out.join_from(&t, &self.engine.abs_labels, &mut self.engine.sink);
                } else {
                    let fo = self.intern_fn_obj(f);
                    let cell = self.seeded_field_cell(fo, name);
                    let v = self.engine.read(cell, user);
                    out.join_from(&v, &self.engine.abs_labels, &mut self.engine.sink);
                }
            }
        }
        match rts.obj {
            ObjType::Empty => {
                // An `unknown`-flagged receiver with no object component is
                // "something got here, contents unknown", not "no receiver":
                // the read yields the same unknown witness a read through an
                // AnyObject receiver does. Without this arm the read would
                // contribute nothing and a whole dataflow chain behind one
                // unknown-typed receiver would read as empty evidence.
                if rts.unknown {
                    let mut any = TypeSet::unresolved();
                    any.fns = Default::default();
                    any.obj = ObjType::Empty;
                    let _ = self.engine.join_ts(out, &any);
                }
            }
            ObjType::One(a) => {
                let own = self.seeded_field_cell(a, name);
                self.read_join(own, user, out);
                if let Some(c) = self.heap[a].class {
                    // Deliberately not the region root: a precise One
                    // receiver must read its own class's cells, not the
                    // merged set's.
                    let cf = self.class_field_cell(c, name);
                    self.read_join(cf, user, out);
                    self.accessor_read(c, name, user, out);
                }
                if chain_ok {
                    self.chain_join(a, name, user, out);
                }
            }
            ObjType::ClassAny(c) => {
                let c = self.view_class(c, is_elems);
                let view = self.engine.cell(CellKey::ClassView { class: c, name });
                let v = self.engine.read(view, user);
                let _ = self.engine.join_ts(out, &v);
                self.accessor_read(c, name, user, out);
                if chain_ok {
                    let pa = self.heap[c].proto_abs;
                    self.ensure_seeded(pa);
                    let f = self.field_cell(pa, name);
                    let v = self.engine.read(f, user);
                    out.join_from(&v, &self.engine.abs_labels, &mut self.engine.sink);
                    self.chain_join(pa, name, user, out);
                }
            }
            ObjType::AnyOf(r) => {
                if is_elems {
                    let union = self.elems_union();
                    self.read_join(union, user, out);
                } else {
                    // Some instance of the region's classes: the value is
                    // unresolved evidence, never fabricated
                    // definite prim bits; at callee position the fn set is
                    // the region's method-table union for the name -- the
                    // flow-scoped upper bound (the classes that actually
                    // met), never the program-wide name union.
                    let mut any = TypeSet::unresolved();
                    any.fns = Default::default();
                    if callee_pos {
                        let fns = self.region_methods(r, name, user);
                        if !fns.is_empty() {
                            region_contributed = true;
                        }
                        any.fns = fns;
                    }
                    // The region's aggregated view, subscribing the reader.
                    // The `unknown` witness is still joined alongside it
                    // (the view is a union of the writes the analysis SAW,
                    // and writes at an `AnyObject` receiver are dropped by
                    // design, so it can under-approximate) -- but the
                    // witness carries NO object component: joined as
                    // `AnyObject` it absorbed the view's population
                    // (`join_obj(AnyOf, AnyObject) = AnyObject`), so every
                    // value read off a region-typed receiver degraded to
                    // `unk|obj:any` and spread AnyObject through the pool
                    // and free-list fields it was stored into. The region
                    // IS the merged fact; `unknown` says the rest honestly.
                    any.obj = ObjType::Empty;
                    if let Some(view) = self.region_view(r, name) {
                        let v = self.engine.read(view, user);
                        let _ = self.engine.join_ts(out, &v);
                    }
                    let _ = self.engine.join_ts(out, &any);
                }
            }
            ObjType::AnyObject => {
                if is_elems {
                    let union = self.elems_union();
                    self.read_join(union, user, out);
                } else {
                    let mut any = TypeSet::unresolved();
                    any.fns = Default::default();
                    let _ = self.engine.join_ts(out, &any);
                }
            }
        }
        region_contributed
    }

    /// The region's field view for `name`: the ROOT class's view cell, with
    /// every member's view linked into it and back out again.
    ///
    /// One tier up from `class_field_cell`, and the same shape: an
    /// abstraction's field cell is linked up into `ClassView`, so a write
    /// through a precise receiver is seen by a `ClassAny` read; this links a
    /// class's view up into the region's, so a write through a classed
    /// receiver is seen by an `AnyOf` read, and back down, so a write at
    /// region granularity is seen by class- and alloc-site-level reads. That
    /// second direction is the point: without it, a write whose receiver
    /// is only known to a region would be dropped outright, emptying the
    /// field for every reader.
    ///
    /// Deliberately NOT a new cell kind. The region root moves as later
    /// meets union regions, so a view keyed by the root at creation time
    /// would go stale; using the root's own `ClassView` and re-linking
    /// lazily on each access makes that self-healing -- after a merge the
    /// next access relinks against the new root and member set, and `link`
    /// is idempotent, so the repeat costs a hash lookup.
    ///
    /// Capped like `region_methods`: a mega-region is honestly megamorphic,
    /// its union is worth nothing, and the linking is O(members). Past the
    /// cap there is no view and the caller keeps the old behaviour.
    fn region_view(&mut self, r: ClassId, name: NameId) -> Option<CellId> {
        let root = self.engine.region_root(r);
        let members = self
            .engine
            .region_members
            .get(&root)
            .cloned()
            .unwrap_or_else(|| vec![root]);
        if members.len() > crate::constants::REGION_VIEW_CAP {
            return None;
        }
        let view = self.engine.cell(CellKey::ClassView { class: root, name });
        for m in members {
            if m == root {
                continue;
            }
            let mv = self.engine.cell(CellKey::ClassView { class: m, name });
            self.engine.link(mv, view);
            self.engine.link(view, mv);
        }
        Some(view)
    }

    /// The region's method-table union for `name`: join the fn sets of each
    /// member class's proto-abstraction cell (subscribing the reader, so
    /// late installs re-fire). Iteration capped -- a huge region is
    /// megamorphic and honestly yields nothing.
    fn region_methods(
        &mut self,
        r: ClassId,
        name: NameId,
        user: (ConId, CtxId),
    ) -> super::types::BoundedFnSet {
        // Only a small region is a plausible closed dispatch set -- a
        // handful of sibling classes all defining the same method. A
        // mega-region's method sets are weak guesses whose guard chains
        // miss, so it stays honestly megamorphic.
        // The REGION cap, not the callee cap: iterating members is O(n)
        // once per (region, name) and the resulting fn set is deduped --
        // a region with many sibling classes sharing one method is
        // exactly the case the much smaller callee cap would fail to
        // resolve, starving every one of that method's arguments.
        let cap = crate::constants::REGION_VIEW_CAP;
        let root = self.engine.region_root(r);
        let members = self
            .engine
            .region_members
            .get(&root)
            .cloned()
            .unwrap_or_else(|| vec![root]);
        let mut fns = super::types::BoundedFnSet::default();
        if members.len() > cap {
            return fns;
        }
        for c in members {
            // The member's own prototype AND its chain: a subclass's
            // methods usually live on a base prototype, so reading only
            // the member's own proto would often yield an empty set --
            // an unresolved call, with no argument flowing into the
            // shared method.
            let mut cur = self.heap[c].proto_abs;
            for _ in 0..CHAIN_DEPTH {
                let cell = self.seeded_field_cell(cur, name);
                let v = self.engine.read(cell, user);
                fns.join_from(&v.fns, &mut self.engine.sink.dropped_fns);
                match self.heap[cur].proto {
                    ProtoLink::Abs(p) => cur = p,
                    ProtoLink::None => break,
                }
            }
        }
        fns
    }

    /// Accessor consultation on a classed read: the getter's return joins
    /// the result (subscribing, so late getter evidence re-fires).
    fn accessor_read(&mut self, c: ClassId, name: NameId, user: (ConId, CtxId), out: &mut TypeSet) {
        if let Some(&(Some(g), _)) = self.accessors.get(&(c, name)) {
            let r = self.engine.cell(CellKey::Ret {
                script: g,
                ctx: CTX0,
            });
            let v = self.engine.read(r, user);
            let _ = self.engine.join_ts(out, &v);
        }
    }

    /// Accessor consultation on a classed write: the stored value binds
    /// the setter's first formal at the generic context.
    fn accessor_write(&mut self, c: ClassId, name: NameId, v: &TypeSet, user: (ConId, CtxId)) {
        if let Some(&(_, Some(s))) = self.accessors.get(&(c, name)) {
            let dst = self.engine.cell(CellKey::Arg {
                script: s,
                arg: FormalIndex::new(0),
                ctx: CTX0,
            });
            self.engine.raise(dst, v, user);
        }
    }

    /// Per-ctx eval tracer for one read site (`NIGHT_TRACE_SITE=<sid>:<pc>`):
    /// every evaluation, with the evaluating ctx, the recv key, and what
    /// resolve() handed that ctx -- the instrument for a site whose cells
    /// know a class the read evaluations never see.
    fn trace_site_eval(
        &self,
        sid: ScriptId,
        pc: Pc,
        ctx: CtxId,
        recv: super::engine::CKey,
        cell: super::engine::CellId,
        rts: &TypeSet,
    ) {
        let Some(site) = super::trace_site_want() else {
            return;
        };
        if site != Site::new(sid, pc) {
            return;
        }
        crate::diag_line!(
            "night: tracesite eval {site} ctx {} recv {:?} cell {} obj {:?} prims {:?} unknown {}",
            ctx.0,
            recv,
            cell.0,
            rts.obj,
            rts.prims,
            rts.unknown
        );
    }

    /// Debug tracer for one field name (`NIGHT_TRACE_FIELD=<name>`): every
    /// read and write evaluation, with the receiver's abstract object type
    /// and, for a `One` receiver, whether that abstraction carries a class.
    /// The question it answers is where a field's value stops flowing --
    /// a write through an unclassed `One` never reaches the class view that
    /// a `ClassAny` read consults.
    fn trace_field(
        &self,
        tag: &str,
        name: NameId,
        rts: &TypeSet,
        v: Option<&TypeSet>,
        user: (ConId, CtxId),
    ) {
        let Some(want) = super::tracers().field.as_ref() else {
            return;
        };
        if String::from_utf16_lossy(self.names.get(name)) != *want {
            return;
        }
        let o = match rts.obj {
            ObjType::Empty => "Empty".to_string(),
            ObjType::One(a) => format!(
                "One(abs{} class {:?} snap {})",
                a.0,
                self.heap[a].class.map(|c| c.0),
                u8::from(matches!(self.heap[a].key, AbsKey::Snap(_)))
            ),
            ObjType::ClassAny(c) => format!("ClassAny({})", c.0),
            ObjType::AnyOf(r) => format!("AnyOf({})", r.0),
            ObjType::AnyObject => "AnyObject".to_string(),
        };
        let sid = self.engine.con_script[user.0 .0 as usize];
        let pc = match &self.engine.cons[user.0 .0 as usize] {
            super::engine::Constraint::Read { pc, .. }
            | super::engine::Constraint::Write { pc, .. } => Some(*pc),
            _ => None,
        };
        crate::diag_line!(
            "night: tracefield {tag} at {}:{} ctx {} recv {o} val {}",
            sid.get(),
            pc.map_or(0, |p| p.get()),
            user.1 .0,
            v.map_or_else(|| "-".to_string(), |t| format!("{:?}", t.obj))
        );
    }

    fn write_into(
        &mut self,
        rts: &TypeSet,
        name: NameId,
        v: &TypeSet,
        this_recv: bool,
        user: (ConId, CtxId),
    ) {
        self.trace_field("write", name, rts, Some(v), user);
        let is_elems = name == self.names_of.elems;
        if rts.fns.is_multi() {
            self.do_escape(v, user);
        } else {
            for f in rts.fns.scripted() {
                if name == self.names_of.prototype {
                    // Prototype install: Never value flow -- the concrete
                    // object becomes a method-table source and chain link.
                    // If the object already names a class (the shared-ctor
                    // presolve keys per-prototype classes for scripts many
                    // classes share), that class owns the table: keying by
                    // the fn script would home every such class's methods
                    // to ONE script-keyed class and demote every pin.
                    if let ObjType::One(x) = v.obj {
                        let proto_cls = match self.heap[x].key {
                            AbsKey::Snap(oid) => {
                                self.heap.class_ids.get(&ClassKey::Proto(oid)).copied()
                            }
                            _ => None,
                        };
                        match proto_cls {
                            Some(c) => self.register_proto_source(c, x),
                            // A shared ctor script's fn-keyed class serves
                            // one purpose: `SharedCtor.prototype` reads
                            // resolve names against it, so it wants the
                            // union of every sharing class's table -- but
                            // it must not OWN any of them (homing all their
                            // methods to the one script class demotes every
                            // per-prototype pin).
                            None if self.shared_ctor_sites.values().any(|s| s.ctor == f) => {
                                let c = self.class_for_fn(f);
                                self.link_proto_table(c, x);
                            }
                            None => {
                                let c = self.class_for_fn(f);
                                self.register_proto_source(c, x);
                            }
                        }
                    }
                } else {
                    let fo = self.intern_fn_obj(f);
                    let cell = self.field_cell(fo, name);
                    self.engine.raise(cell, v, user);
                }
            }
        }
        match rts.obj {
            ObjType::Empty => {
                // Same rule as the read side: an unknown receiver may hold
                // any object the analysis has seen escape, so the written
                // value escapes too (and is counted with the drops).
                if rts.unknown {
                    self.stats.dropped_writes += 1;
                    if this_recv {
                        self.stats.dropped_this_writes += 1;
                    }
                    self.do_escape(v, user);
                }
            }
            ObjType::One(a) => {
                let own = self.seeded_field_cell(a, name);
                self.engine.raise(own, v, user);
                if let Some(owner) = self.heap[a].owner_class {
                    self.note_method_home(owner, v);
                }
                if let Some(c) = self.heap[a].class {
                    self.accessor_write(c, name, v, user);
                }
            }
            ObjType::ClassAny(c) => {
                let c = self.view_class(c, is_elems);
                let cf = self.class_field_cell(c, name);
                self.engine.raise(cf, v, user);
                self.accessor_write(c, name, v, user);
            }
            ObjType::AnyOf(r) if !is_elems => {
                // A write whose receiver is known to a region: raise it into
                // the region's view, which is linked down into every
                // member's class view, so class- and alloc-site-level reads
                // see it. Dropping this was what emptied a field for every
                // reader when one write site lost its receiver class.
                //
                // `AnyObject` deliberately keeps the drop (below): it is not
                // a bounded set of classes that met, it is everything, and
                // distributing a write to every object in the program would
                // pollute far more than it recovers.
                match self.region_view(r, name) {
                    Some(view) => self.engine.raise(view, v, user),
                    None => {
                        self.stats.dropped_writes += 1;
                        if this_recv {
                            self.stats.dropped_this_writes += 1;
                        }
                    }
                }
                self.do_escape(v, user);
            }
            ObjType::AnyOf(_) | ObjType::AnyObject => {
                if is_elems {
                    let union = self.elems_union();
                    self.engine.raise(union, v, user);
                } else {
                    self.stats.dropped_writes += 1;
                    if this_recv {
                        self.stats.dropped_this_writes += 1;
                    }
                }
                self.do_escape(v, user);
            }
        }
    }

    /// The typed-array kind every object of `obj` has, when one does.
    /// A region whose every member is the same typed-array kind still
    /// names the kind (pdfjs: distinct Uint8Array alloc sites joined
    /// through the DecodeStream buffer field). The consumer arm guards the
    /// class at runtime, so this is a prediction like the exact forms, not
    /// a proof.
    pub(super) fn obj_ta_kind(&self, obj: ObjType) -> Option<crate::opsem::TaKind> {
        match obj {
            ObjType::One(a) => self.heap[a].ta_kind,
            ObjType::ClassAny(c) => self.heap[c].ta_kind,
            ObjType::AnyOf(r) => {
                let root = self.engine.region_root(r);
                self.engine
                    .region_members
                    .get(&root)
                    .filter(|ms| ms.len() <= crate::constants::REGION_VIEW_CAP)
                    .and_then(|ms| {
                        let mut it = ms.iter().map(|&m| self.heap[m].ta_kind);
                        let first = it.next().flatten()?;
                        it.all(|t| t == Some(first)).then_some(first)
                    })
            }
            _ => None,
        }
    }

    /// The class a typeset contributes to a site's agreement, or `None`
    /// when its object half is still EMPTY -- whatever the `unknown` flag
    /// says. The flag is not evidence about the class: a region read
    /// raises its unknown witness before the region view delivers the
    /// object half, so the first evaluations of a site see `Empty|unknown`
    /// and only later ones see the class. `Agreed::Conflict` is sticky, so
    /// counting that transient as a conflict would poison the site for
    /// every later evaluation. A receiver that stays empty contributes
    /// nothing and gets no class fact; `AnyObject` still conflicts.
    fn site_class_evidence(&self, ts: &TypeSet, regions: RegionLabels) -> Option<Option<ClassId>> {
        if ts.obj == ObjType::Empty {
            return None;
        }
        self.recv_class(ts.obj, ts.unknown, regions)
    }

    /// Per-site emission evidence: receiver class agreement, elem TA kind,
    /// and (reads) the joined result typeset.
    fn note_site_evidence(
        &mut self,
        sid: ScriptId,
        pc: Pc,
        name: NameId,
        rts: &TypeSet,
        out: Option<&TypeSet>,
    ) {
        let site = Site::new(sid, pc);
        if let Some(out) = out {
            if !out.is_empty() {
                let mut t = self.site_read_ts.remove(&site).unwrap_or_default();
                let _ = self.engine.join_ts(&mut t, out);
                self.site_read_ts.insert(site, t);
            }
            // Value-class agreement: what CLASS of object this read
            // yields, when every evaluation agrees (AnyObject or a
            // class-less abstraction poisons, exactly as the receiver
            // agreement does; region labels are accepted).
            if let Some(c) = self.site_class_evidence(out, RegionLabels::Accept) {
                let e = self.site_value_class.entry(site).or_default();
                match c {
                    Some(c) => e.observe(c),
                    None => *e = Agreed::Conflict,
                }
            }
        }
        if let Some(c) = self.site_class_evidence(rts, RegionLabels::Refuse) {
            let e = self.site_recv_class.entry(site).or_default();
            match c {
                Some(c) => e.observe(c),
                None => *e = Agreed::Conflict,
            }
            if Self::unresolved_recv(rts) {
                self.site_recv_unresolved.insert(site);
            }
        }
        if let Some(label) = self.site_class_evidence(rts, RegionLabels::Accept) {
            let e = self.site_recv_labels.entry(site).or_default();
            let before_conflict = *e == super::types::AgreedSet::Conflict;
            match label {
                None => e.conflict(),
                Some(c) => e.observe(c, RECV_LABEL_CAP),
            }
            if !before_conflict && *e == super::types::AgreedSet::Conflict && label.is_some() {
                self.stats.caps.recv_labels += 1;
            }
        }
        if name == self.names_of.elems {
            if let Some(ta) = self.obj_ta_kind(rts.obj) {
                observe(&mut self.site_recv_ta, site, ta);
            }
        }
    }

    /// The `TypeSet::unresolved` receiver shape: an object the analysis
    /// could not name, no named class beside it.
    fn unresolved_recv(ts: &TypeSet) -> bool {
        ts.obj == ObjType::AnyObject && ts.unknown
    }

    /// Re-derive the receiver-class agreement of every site an unresolved
    /// receiver reached, from the FINAL state of each live context, with
    /// that row weighed as no evidence: the site's claim is guarded at
    /// runtime, and the row is the generic context of a chain unresolved
    /// for reasons unrelated to the contexts that named the class. Final
    /// states only -- a class observed mid-fixpoint in a context that ends
    /// unresolved is a transient, and agreeing on it emits a typed read
    /// whose miss departs the track.
    pub(super) fn settle_unresolved_recv_sites(&mut self) {
        use super::engine::CellKey;
        let sites: Vec<Site> = self.site_recv_unresolved.iter().copied().collect();
        for site in sites {
            let sid = site.script;
            let recv = self.engine.script_cons.get(&sid).and_then(|cons| {
                cons.iter()
                    .find_map(|&c| match &self.engine.cons[c.0 as usize] {
                        Constraint::Read { recv, pc, .. } | Constraint::Write { recv, pc, .. }
                            if *pc == site.pc =>
                        {
                            Some(*recv)
                        }
                        _ => None,
                    })
            });
            let Some(recv) = recv else { continue };
            let ctxs = self.engine.live_ctxs.get(&sid).cloned().unwrap_or_default();
            let mut agreed = Agreed::Unset;
            for ctx in ctxs {
                let key = match recv {
                    super::engine::CKey::This => CellKey::This { script: sid, ctx },
                    _ => {
                        let id = self.engine.resolve(sid, ctx, recv);
                        let ts = self.engine.ts(id).clone();
                        Self::observe_final_recv(&mut agreed, &ts, self);
                        continue;
                    }
                };
                if let Some(id) = self.engine.lookup(key) {
                    let ts = self.engine.ts(id).clone();
                    Self::observe_final_recv(&mut agreed, &ts, self);
                }
            }
            self.site_recv_class.insert(site, agreed);
        }
    }

    fn observe_final_recv(agreed: &mut Agreed<ClassId>, ts: &TypeSet, sv: &Self) {
        if Self::unresolved_recv(ts) {
            return;
        }
        match sv.site_class_evidence(ts, RegionLabels::Refuse) {
            None => {}
            Some(Some(c)) => agreed.observe(c),
            Some(None) => *agreed = Agreed::Conflict,
        }
    }

    /// The class a receiver typeset names, as the per-site channels record
    /// it.
    ///
    /// Three answers, not two: `None` means the receiver contributed no
    /// evidence at all (it holds no object yet), `Some(None)` means it held
    /// an object the analysis cannot name, and `Some(Some(c))` names it.
    /// The middle answer is what conflicts a site, so collapsing it into
    /// the first would make an unnamed receiver look like no receiver.
    pub(super) fn recv_class(
        &self,
        o: ObjType,
        unknown: bool,
        regions: RegionLabels,
    ) -> Option<Option<ClassId>> {
        Some(match o {
            ObjType::Empty if unknown => None,
            ObjType::Empty => return None,
            ObjType::One(a) => self.heap[a].class,
            ObjType::ClassAny(c) => Some(c),
            ObjType::AnyOf(r) => match regions {
                RegionLabels::Accept => Some(r),
                RegionLabels::Refuse => None,
            },
            ObjType::AnyObject => None,
        })
    }

    /// Receiver-kind census per read site: record the least precise
    /// receiver this site has been evaluated with (see [`RecvKind`]).
    fn note_site_recv(&mut self, script: ScriptId, pc: Pc, rts: &TypeSet) {
        let kind = match rts.obj {
            ObjType::Empty => RecvKind::Empty,
            ObjType::One(_) => RecvKind::One,
            ObjType::ClassAny(_) => RecvKind::ClassAny,
            ObjType::AnyOf(_) => RecvKind::AnyOf,
            ObjType::AnyObject => RecvKind::AnyObject,
        };
        let e = self
            .site_recv
            .entry(Site::new(script, pc))
            .or_insert(RecvKind::Empty);
        if kind > *e {
            *e = kind;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::likelier::engine::CKey;
    use crate::likelier::Solver;

    fn empty_source() -> Source {
        Source {
            objects: Vec::new(),
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        }
    }

    fn run(sv: &mut Solver<'_>) {
        for sid in crate::likelier::sorted_keys(&sv.engine.script_cons) {
            sv.engine.instantiate(sid, CTX0);
        }
        while let Some((c, ctx)) = sv.engine.pop() {
            if sv.engine.eval_core(c, ctx) {
                continue;
            }
            if sv.eval_heap(c, ctx) {
                continue;
            }
            assert!(sv.eval_call(c, ctx), "unhandled constraint in heap test");
        }
    }

    fn var_ts(sv: &Solver<'_>, script: u32, var: u32) -> TypeSet {
        sv.engine
            .lookup(CellKey::Var {
                script: ScriptId::new(script),
                var: VarId::new(var),
                ctx: CTX0,
            })
            .map(|c| sv.engine.ts(c).clone())
            .unwrap_or_default()
    }

    /// The snapshot never-merge principle, structurally: sibling instances
    /// of one class do not share field cells (a One read must not see the
    /// sibling's value), while the ClassAny view sees all of them.
    #[test]
    fn sibling_isolation_and_class_view() {
        let source = empty_source();
        let gn = HashMap::default();
        let opts = crate::options::Options::default();
        let mut sv = Solver::new(&source, &gn, &opts, crate::ids::Names::default());
        let c = sv.class_for_fn(ScriptId::new(500));
        let a = sv.intern_alloc(ScriptId::new(1), Pc::new(10), CTX0, Some(c), false, None);
        let b = sv.intern_alloc(ScriptId::new(1), Pc::new(20), CTX0, Some(c), false, None);
        let n = sv.names.intern(&['f' as u16]);
        let mk = |sv: &mut Solver<'_>, con| {
            sv.engine.add_con(ScriptId::new(1), con);
        };
        mk(
            &mut sv,
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::obj_one(a),
            },
        );
        mk(
            &mut sv,
            Constraint::Const {
                dst: CKey::Var(VarId::new(1)),
                ts: TypeSet::prim(PRIM_INT32),
            },
        );
        mk(
            &mut sv,
            Constraint::Write {
                recv: CKey::Var(VarId::new(0)),
                name: n,
                src: CKey::Var(VarId::new(1)),
                pc: Pc::new(0),
            },
        );
        mk(
            &mut sv,
            Constraint::Const {
                dst: CKey::Var(VarId::new(2)),
                ts: TypeSet::obj_one(b),
            },
        );
        mk(
            &mut sv,
            Constraint::Read {
                recv: CKey::Var(VarId::new(2)),
                name: n,
                dst: CKey::Var(VarId::new(3)),
                pc: Pc::new(4),
                callee_pos: false,
            },
        );
        // A joined receiver (a join b = ClassAny(c)) reads the class view.
        mk(
            &mut sv,
            Constraint::Const {
                dst: CKey::Var(VarId::new(4)),
                ts: TypeSet::obj_one(a),
            },
        );
        mk(
            &mut sv,
            Constraint::Const {
                dst: CKey::Var(VarId::new(4)),
                ts: TypeSet::obj_one(b),
            },
        );
        mk(
            &mut sv,
            Constraint::Read {
                recv: CKey::Var(VarId::new(4)),
                name: n,
                dst: CKey::Var(VarId::new(5)),
                pc: Pc::new(8),
                callee_pos: false,
            },
        );
        run(&mut sv);
        // Sibling b sees nothing of a's own write...
        assert!(var_ts(&sv, 1, 3).prims.is_empty());
        // ...but the receiver itself joined to ClassAny...
        let recv = var_ts(&sv, 1, 4);
        assert_eq!(recv.obj, ObjType::ClassAny(c));
        // ...and the ClassAny read sees the instance write through the view.
        assert_eq!(var_ts(&sv, 1, 5).prims, PRIM_INT32);
    }

    /// Writes through a ClassAny receiver land in ClassField and are seen
    /// by One readers of any member (the ClassField/ClassView split).
    #[test]
    fn class_field_reaches_one_readers() {
        let source = empty_source();
        let gn = HashMap::default();
        let opts = crate::options::Options::default();
        let mut sv = Solver::new(&source, &gn, &opts, crate::ids::Names::default());
        let c = sv.class_for_fn(ScriptId::new(501));
        let a = sv.intern_alloc(ScriptId::new(1), Pc::new(10), CTX0, Some(c), false, None);
        let b = sv.intern_alloc(ScriptId::new(1), Pc::new(20), CTX0, Some(c), false, None);
        let n = sv.names.intern(&['g' as u16]);
        for con in [
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::obj_one(a),
            },
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::obj_one(b),
            },
            Constraint::Const {
                dst: CKey::Var(VarId::new(1)),
                ts: TypeSet::prim(PRIM_DOUBLE),
            },
            Constraint::Write {
                recv: CKey::Var(VarId::new(0)),
                name: n,
                src: CKey::Var(VarId::new(1)),
                pc: Pc::new(0),
            },
            Constraint::Const {
                dst: CKey::Var(VarId::new(2)),
                ts: TypeSet::obj_one(a),
            },
            Constraint::Read {
                recv: CKey::Var(VarId::new(2)),
                name: n,
                dst: CKey::Var(VarId::new(3)),
                pc: Pc::new(4),
                callee_pos: false,
            },
        ] {
            sv.engine.add_con(ScriptId::new(1), con);
        }
        run(&mut sv);
        assert_eq!(var_ts(&sv, 1, 3).prims, PRIM_DOUBLE);
    }

    /// The region rung end to end, in miniature: two
    /// instances of different classes meet (-> AnyOf(region)); a
    /// callee-position read of a method name resolves the region's
    /// method-table union; the call site emits the flow-scoped set.
    #[test]
    fn region_method_resolution() {
        let source = empty_source();
        let gn = HashMap::default();
        let opts = crate::options::Options::default();
        let mut sv = Solver::new(&source, &gn, &opts, crate::ids::Names::default());
        let c1 = sv.class_for_fn(ScriptId::new(700));
        let c2 = sv.class_for_fn(ScriptId::new(701));
        let a = sv.intern_alloc(ScriptId::new(1), Pc::new(10), CTX0, Some(c1), false, None);
        let b = sv.intern_alloc(ScriptId::new(1), Pc::new(20), CTX0, Some(c2), false, None);
        let m = sv.names.intern(&['m' as u16]);
        let proto_name = sv.names_of.prototype;
        for (fscript, method, base) in [(700u32, 800u32, 0u32), (701, 801, 10)] {
            sv.engine.add_con(
                ScriptId::new(2),
                Constraint::Const {
                    dst: CKey::Var(VarId::new(base)),
                    ts: TypeSet::fn_one(FnId::script(ScriptId::new(fscript))),
                },
            );
            sv.engine.add_con(
                ScriptId::new(2),
                Constraint::Read {
                    recv: CKey::Var(VarId::new(base)),
                    name: proto_name,
                    dst: CKey::Var(VarId::new(base + 1)),
                    pc: Pc::new(base),
                    callee_pos: false,
                },
            );
            sv.engine.add_con(
                ScriptId::new(2),
                Constraint::Const {
                    dst: CKey::Var(VarId::new(base + 2)),
                    ts: TypeSet::fn_one(FnId::script(ScriptId::new(method))),
                },
            );
            sv.engine.add_con(
                ScriptId::new(2),
                Constraint::Write {
                    recv: CKey::Var(VarId::new(base + 1)),
                    name: m,
                    src: CKey::Var(VarId::new(base + 2)),
                    pc: Pc::new(base + 1),
                },
            );
        }
        // The meet, and the dispatch through it.
        sv.engine.add_con(
            ScriptId::new(1),
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::obj_one(a),
            },
        );
        sv.engine.add_con(
            ScriptId::new(1),
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::obj_one(b),
            },
        );
        sv.engine.add_con(
            ScriptId::new(1),
            Constraint::Read {
                recv: CKey::Var(VarId::new(0)),
                name: m,
                dst: CKey::Var(VarId::new(1)),
                pc: Pc::new(5),
                callee_pos: true,
            },
        );
        sv.engine.add_con(
            ScriptId::new(1),
            Constraint::Call {
                callee: CKey::Var(VarId::new(1)),
                this_: Some(CKey::Var(VarId::new(0))),
                args: Vec::new().into(),
                ret: CKey::Var(VarId::new(2)),
                pc: Pc::new(9),
                construct: false,
            },
        );
        run(&mut sv);
        let recv = var_ts(&sv, 1, 0);
        assert!(matches!(recv.obj, ObjType::AnyOf(_)), "meet -> {recv:?}");
        let callee = var_ts(&sv, 1, 1);
        assert_eq!(
            callee.fns.ids(),
            &[
                FnId::script(ScriptId::new(800)),
                FnId::script(ScriptId::new(801))
            ]
        );
        let site = sv.site_calls.get(&Site::from_raw(1, 9)).expect("site fact");
        assert_eq!(
            site.ids(),
            &[
                FnId::script(ScriptId::new(800)),
                FnId::script(ScriptId::new(801))
            ]
        );
    }

    /// A method read that dead-ends before the prototype is installed
    /// re-fires when `F.prototype = {...; m: fn}` lands later (sentinel +
    /// standing links), and the method-home attribution records the ctor.
    #[test]
    fn late_prototype_install_refires() {
        let source = empty_source();
        let gn = HashMap::default();
        let opts = crate::options::Options::default();
        let mut sv = Solver::new(&source, &gn, &opts, crate::ids::Names::default());
        let c = sv.class_for_fn(ScriptId::new(600));
        let inst = sv.intern_alloc(ScriptId::new(1), Pc::new(10), CTX0, Some(c), false, None);
        let m = sv.names.intern(&['m' as u16]);
        let proto_name = sv.names_of.prototype;
        // Script 1: read inst.m (evaluates first, dead-ends).
        sv.engine.add_con(
            ScriptId::new(1),
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::obj_one(inst),
            },
        );
        sv.engine.add_con(
            ScriptId::new(1),
            Constraint::Read {
                recv: CKey::Var(VarId::new(0)),
                name: m,
                dst: CKey::Var(VarId::new(1)),
                pc: Pc::new(0),
                callee_pos: false,
            },
        );
        run(&mut sv);
        assert!(var_ts(&sv, 1, 1).fns.is_empty());
        // Script 2: F.prototype = lit; lit.m = <script 601>.
        let lit_pc = 99;
        sv.engine.add_con(
            ScriptId::new(2),
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::fn_one(FnId::script(ScriptId::new(600))),
            },
        );
        sv.engine.add_con(
            ScriptId::new(2),
            Constraint::Alloc {
                dst: CKey::Var(VarId::new(1)),
                pc: Pc::new(lit_pc),
                kind: AllocKind::Plain,
            },
        );
        sv.engine.add_con(
            ScriptId::new(2),
            Constraint::Const {
                dst: CKey::Var(VarId::new(2)),
                ts: TypeSet::fn_one(FnId::script(ScriptId::new(601))),
            },
        );
        sv.engine.add_con(
            ScriptId::new(2),
            Constraint::Write {
                recv: CKey::Var(VarId::new(1)),
                name: m,
                src: CKey::Var(VarId::new(2)),
                pc: Pc::new(100),
            },
        );
        sv.engine.add_con(
            ScriptId::new(2),
            Constraint::Write {
                recv: CKey::Var(VarId::new(0)),
                name: proto_name,
                src: CKey::Var(VarId::new(1)),
                pc: Pc::new(101),
            },
        );
        run(&mut sv);
        let got = var_ts(&sv, 1, 1);
        assert_eq!(got.fns.ids(), &[FnId::script(ScriptId::new(601))]);
        assert_eq!(
            sv.heap.method_home.get(&ScriptId::new(601)),
            Some(&Agreed::One(ScriptId::new(600)))
        );
    }

    /// An executed-but-unresolved call raises unresolved evidence into
    /// its result (never nothing); the bit flows through a field write,
    /// so the read view is no longer pure numeric.
    #[test]
    #[allow(clippy::field_reassign_with_default)]
    fn unresolved_call_result_poisons_field_view() {
        let source = empty_source();
        let gn = HashMap::default();
        let opts = crate::options::Options::default();
        let mut sv = Solver::new(&source, &gn, &opts, crate::ids::Names::default());
        let c = sv.class_for_fn(ScriptId::new(800));
        let a = sv.intern_alloc(ScriptId::new(1), Pc::new(10), CTX0, Some(c), false, None);
        let v1 = sv.names.intern(&['v' as u16]);
        let mut anyobj = TypeSet::default();
        anyobj.obj = ObjType::AnyObject;
        for con in [
            // t = <unresolved callee>()
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: anyobj,
            },
            Constraint::Call {
                callee: CKey::Var(VarId::new(0)),
                this_: None,
                args: Vec::new().into(),
                ret: CKey::Var(VarId::new(1)),
                pc: Pc::new(0),
                construct: false,
            },
            // this-less stand-in: a.v = t, plus a numeric sibling write.
            Constraint::Const {
                dst: CKey::Var(VarId::new(2)),
                ts: TypeSet::obj_one(a),
            },
            Constraint::Write {
                recv: CKey::Var(VarId::new(2)),
                name: v1,
                src: CKey::Var(VarId::new(1)),
                pc: Pc::new(4),
            },
            Constraint::Const {
                dst: CKey::Var(VarId::new(3)),
                ts: TypeSet::prim(PRIM_INT32),
            },
            Constraint::Write {
                recv: CKey::Var(VarId::new(2)),
                name: v1,
                src: CKey::Var(VarId::new(3)),
                pc: Pc::new(8),
            },
            Constraint::Read {
                recv: CKey::Var(VarId::new(2)),
                name: v1,
                dst: CKey::Var(VarId::new(4)),
                pc: Pc::new(12),
                callee_pos: false,
            },
        ] {
            sv.engine.add_con(ScriptId::new(1), con);
        }
        run(&mut sv);
        assert!(var_ts(&sv, 1, 1).unknown);
        let read = var_ts(&sv, 1, 4);
        assert_eq!(read.prims, PRIM_INT32);
        assert!(read.unknown);
        assert!(read.prims.subset_of(PRIM_INT32 | PRIM_DOUBLE));
    }

    /// The heap-interval channel end to end: quantized store-side joins,
    /// the arith mask rule via constraint literals, Any-poison from an
    /// unbounded store, and the dropped-write name poison.
    #[test]
    fn heap_interval_store_side() {
        use crate::likelier::types::{Interval, NumOp, ValueRange};
        let source = empty_source();
        let gn = HashMap::default();
        let opts = crate::options::Options::default();
        let mut sv = Solver::new(&source, &gn, &opts, crate::ids::Names::default());
        let arr = sv.intern_alloc(ScriptId::new(1), Pc::new(10), CTX0, None, true, None);
        let elems = sv.names_of.elems;
        for con in [
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::obj_one(arr),
            },
            // x = <unknown int32> & 0xfff
            Constraint::Const {
                dst: CKey::Var(VarId::new(1)),
                ts: TypeSet::prim(PRIM_INT32),
            },
            Constraint::Arith {
                op: NumOp::BitAnd,
                a: CKey::Var(VarId::new(1)),
                b: Some(CKey::Var(VarId::new(2))),
                dst: CKey::Var(VarId::new(3)),
                a_lit: None,
                b_lit: Some(ValueRange::new(0xfff, 0xfff)),
                pc: Pc::new(0),
            },
            Constraint::Write {
                recv: CKey::Var(VarId::new(0)),
                name: elems,
                src: CKey::Var(VarId::new(3)),
                pc: Pc::new(0),
            },
            Constraint::Read {
                recv: CKey::Var(VarId::new(0)),
                name: elems,
                dst: CKey::Var(VarId::new(4)),
                pc: Pc::new(4),
                callee_pos: false,
            },
        ] {
            sv.engine.add_con(ScriptId::new(1), con);
        }
        run(&mut sv);
        assert_eq!(
            var_ts(&sv, 1, 4).interval,
            Interval::In(ValueRange::new(0, 0xfff))
        );
        // An unbounded int32 store kills the claim (one unprovable store
        // kills the fact).
        let c = sv.engine.add_con(
            ScriptId::new(1),
            Constraint::Write {
                recv: CKey::Var(VarId::new(0)),
                name: elems,
                src: CKey::Var(VarId::new(1)),
                pc: Pc::new(8),
            },
        );
        sv.engine.enqueue(c, CTX0);
        run(&mut sv);
        assert_eq!(var_ts(&sv, 1, 4).interval, Interval::Num);
    }

    /// Cell-side this-attribution: a home installed before and a home
    /// installed after the this-write both receive the evidence in their
    /// ClassField/ClassView cells (links propagate current value on
    /// install); delegation edges propagate homes transitively.
    #[test]
    fn this_field_home_links() {
        let source = empty_source();
        let gn = HashMap::default();
        let opts = crate::options::Options::default();
        let mut sv = Solver::new(&source, &gn, &opts, crate::ids::Names::default());
        let n = sv.names.intern(&['q' as u16]);
        let c_early = sv.class_for_fn(ScriptId::new(10));
        sv.this_home_add(ScriptId::new(7), c_early);
        let con = sv.engine.add_con(
            ScriptId::new(7),
            crate::likelier::engine::Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::default(),
            },
        );
        sv.this_field_raise(
            ScriptId::new(7),
            n,
            &TypeSet::prim(PRIM_INT32),
            (con, crate::likelier::types::CTX0),
        );
        let view = |sv: &mut Solver<'_>, c| {
            let cell = sv
                .engine
                .cell(crate::likelier::engine::CellKey::ClassView { class: c, name: n });
            sv.engine.ts(cell).clone()
        };
        assert_eq!(view(&mut sv, c_early).prims, PRIM_INT32);
        // Late home: link install propagates the already-raised value.
        let c_late = sv.class_for_fn(ScriptId::new(11));
        sv.this_home_add(ScriptId::new(7), c_late);
        assert_eq!(view(&mut sv, c_late).prims, PRIM_INT32);
        // Delegation: sid 7 forwards this to sid 8; 8's writes reach 7's homes,
        // including homes added after the edge.
        sv.this_deleg_add(ScriptId::new(7), ScriptId::new(8));
        sv.this_field_raise(
            ScriptId::new(8),
            n,
            &TypeSet::prim(PRIM_DOUBLE),
            (con, crate::likelier::types::CTX0),
        );
        assert_eq!(view(&mut sv, c_early).prims, PRIM_INT32 | PRIM_DOUBLE);
    }
}
