/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The incremental fixpoint engine: cells, the constraint IR, subscriptions,
//! the worklist, and provenance. Constraints are generated once per script;
//! evaluation is per `(constraint, ctx)`. An edge re-fires whenever its
//! source cell grows.
//!
//! Determinism: all ids are dense and allocation-ordered; joins are
//! commutative on an immutable class labelling, so worklist order affects
//! only work, never the fixpoint.

use super::types::{
    AbsId, AbsLabels, ClassId, CtxId, Interval, JoinSink, NameId, TypeSet, CTX0, MAX_CELL_CHANGES,
};
use crate::facts::CallForm;
use crate::ids::{EnvSlot, FormalIndex, Pc, ScriptId, VarId};
use crate::opsem::{Prims, ValueRange};
use crate::source::SourceObjectId;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
use std::collections::VecDeque;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct CellId(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ConId(pub u32);

/// Provenance sentinel for raises that come from initial state (snapshot
/// seeding, gname seeds) or standing links rather than a constraint.
pub const SEED: ConId = ConId(u32::MAX);

/// Global cell identity. `Var`/`Arg`/`This`/`Ret` are per-context rows;
/// heap and global cells are context-free (context sensitivity lives in
/// which per-ctx rows have edges into them).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CellKey {
    /// One local or temporary of a script, in one context.
    Var {
        script: ScriptId,
        var: VarId,
        ctx: CtxId,
    },
    /// One formal position of a script, in one context.
    Arg {
        script: ScriptId,
        arg: FormalIndex,
        ctx: CtxId,
    },
    /// A script's receiver, in one context.
    This {
        script: ScriptId,
        ctx: CtxId,
    },
    /// Everything a script returns, in one context.
    Ret {
        script: ScriptId,
        ctx: CtxId,
    },
    /// A global binding, by name.
    GName(NameId),
    /// One slot of a closure environment, named by the scope object that
    /// owns it. Context-free: every closure over the scope shares the slot.
    Aliased {
        scope: SourceObjectId,
        slot: EnvSlot,
    },
    Field {
        abs: AbsId,
        name: NameId,
    },
    ClassField {
        class: ClassId,
        name: NameId,
    },
    ClassView {
        class: ClassId,
        name: NameId,
    },
    /// Sentinel: raised (with a dummy bit) when the abstraction's proto
    /// link is installed, so chain-walking reads that dead-ended re-fire.
    ProtoSentinel(AbsId),
    /// A script's accumulated `this.name = v` evidence, ctx-collapsed.
    /// Standing links fan it into the ClassField cells of the script's
    /// home classes (ctor class, single-home pin, this-forwarding
    /// delegation), so this-attributed writes survive receiver saturation
    /// -- the cell-graph form of the this_wmask side table's attribution.
    ThisField {
        script: ScriptId,
        name: NameId,
    },
    /// The bundle-wide union of every array abstraction's elems cell (fed
    /// by standing links). Elems reads on AnyObject receivers consult it:
    /// "an element read whose receiver we lost track of likely yields some
    /// array's element" -- the guarded coarsening of unify-on-meet element
    /// nodes.
    ArrayElemsUnion,
    /// Fn-table dispatch join row: the per-arg-index profile joined over
    /// every dispatch site whose callee reads `abs`'s elems cell. Standing
    /// links fan it into each snapshot member's Arg row at the generic
    /// context -- one row, never per-target contexts (the set
    /// is opaque at the sites, but the members' formals still learn the
    /// join of what the table is called with).
    TableArgJoin {
        abs: AbsId,
        arg: FormalIndex,
    },
}

/// Context-relative cell reference inside a constraint. Constraint identity
/// is context-free; `(sid, ctx)` resolves a `CKey` to a `CellKey` at eval.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CKey {
    Var(VarId),
    Arg(FormalIndex),
    This,
    Ret,
    GName(NameId),
    Aliased {
        scope: SourceObjectId,
        slot: EnvSlot,
    },
}

#[derive(Clone, Debug)]
pub enum Constraint {
    /// dst <- src.
    Move { src: CKey, dst: CKey },
    /// dst <- fixed typeset (constants, unhandled-op Any, prim op results).
    Const { dst: CKey, ts: TypeSet },
    /// dst <- receiver.name (heap semantics). `callee_pos`: the result
    /// feeds a call's callee operand (set by the scanner); only such reads
    /// consult the per-name method union on AnyObject receivers -- letting
    /// union fns into generic value flow leaks them into escape sinks and
    /// poisons the very method bodies the union serves.
    Read {
        recv: CKey,
        name: NameId,
        dst: CKey,
        pc: Pc,
        callee_pos: bool,
    },
    /// receiver.name <- src (heap semantics).
    Write {
        recv: CKey,
        name: NameId,
        src: CKey,
        pc: Pc,
    },
    /// Call binding. `args` resolve against the caller's ctx
    /// (Rc: constraints are cloned per eval; a Vec here allocated on the
    /// solve hot path).
    Call {
        callee: CKey,
        this_: Option<CKey>,
        args: std::rc::Rc<[CKey]>,
        ret: CKey,
        pc: Pc,
        construct: bool,
    },
    /// `T.apply(this, args)` / `T.call(this, a, b)`: a delegation call
    /// edge. `args[0]` is the forwarded receiver; direct arguments are
    /// `args[1..]` (call) or the unpacked frame `arguments` when
    /// `arg1_is_arguments` (apply).
    Apply {
        target: CKey,
        args: std::rc::Rc<[CKey]>,
        arg1_is_arguments: bool,
        ret: CKey,
        pc: Pc,
        form: CallForm,
    },
    /// `recv.push/unshift(arg)` or `recv.pop/shift()`: the array builtins
    /// that move a value in or out of the receiver's element node.
    ElemBuiltin {
        recv: CKey,
        arg: Option<CKey>,
        ret: CKey,
        pc: Pc,
        kind: ElemBuiltinKind,
    },
    /// Allocation site: dst <- One(Alloc(sid, pc, ctx)) (heap semantics).
    /// `Snap` yields the ctx-free snapshot abstraction instead.
    Alloc { dst: CKey, pc: Pc, kind: AllocKind },
    /// dst <- op(a[, b]): the operand-sensitive arithmetic transfer
    /// (`types::arith_transfer`), which reads the operands' own claims
    /// rather than returning one generic numeric mask. `a_lit`/`b_lit` are
    /// exact scan-time literal intervals for the interval transfer (cells
    /// hold only quantized bounds; the shift/mask rules need the literal).
    Arith {
        op: super::types::NumOp,
        a: CKey,
        b: Option<CKey>,
        dst: CKey,
        a_lit: Option<ValueRange>,
        b_lit: Option<ValueRange>,
        pc: Pc,
    },
}

/// Which kind of dataflow edge a constraint is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConstraintKind {
    Move,
    Const,
    Read,
    Write,
    Call,
    Apply,
    ElemBuiltin,
    Alloc,
    Arith,
}

impl ConstraintKind {
    pub const ALL: [ConstraintKind; 9] = [
        ConstraintKind::Move,
        ConstraintKind::Const,
        ConstraintKind::Read,
        ConstraintKind::Write,
        ConstraintKind::Call,
        ConstraintKind::Apply,
        ConstraintKind::ElemBuiltin,
        ConstraintKind::Alloc,
        ConstraintKind::Arith,
    ];

    pub fn name(self) -> &'static str {
        match self {
            ConstraintKind::Move => "move",
            ConstraintKind::Const => "const",
            ConstraintKind::Read => "read",
            ConstraintKind::Write => "write",
            ConstraintKind::Call => "call",
            ConstraintKind::Apply => "apply",
            ConstraintKind::ElemBuiltin => "elem",
            ConstraintKind::Alloc => "alloc",
            ConstraintKind::Arith => "arith",
        }
    }
}

impl Constraint {
    pub fn kind(&self) -> ConstraintKind {
        match self {
            Constraint::Move { .. } => ConstraintKind::Move,
            Constraint::Const { .. } => ConstraintKind::Const,
            Constraint::Read { .. } => ConstraintKind::Read,
            Constraint::Write { .. } => ConstraintKind::Write,
            Constraint::Call { .. } => ConstraintKind::Call,
            Constraint::Apply { .. } => ConstraintKind::Apply,
            Constraint::ElemBuiltin { .. } => ConstraintKind::ElemBuiltin,
            Constraint::Alloc { .. } => ConstraintKind::Alloc,
            Constraint::Arith { .. } => ConstraintKind::Arith,
        }
    }
}

/// Which array builtin an [`Constraint::ElemBuiltin`] edge models.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ElemBuiltinKind {
    /// `push`/`unshift`: the argument flows into the receiver's elements.
    Write,
    /// `pop`/`shift`: an element flows out into the result.
    Read,
}

#[derive(Clone, Copy, Debug)]
pub enum AllocKind {
    /// Object literal (`NewInit`/`NewObject`); the lit-order channel keys on
    /// the site.
    Plain,
    /// Array literal, or `Array(n)` in either call form.
    Array,
    /// `new <TypedArray>()`, with the element kind the scanner read off
    /// the constructor name.
    TypedArray(crate::opsem::TaKind),
    /// Precompiled run-once literal (`JSOp::Object`): the transcribed
    /// source object it names, one ctx-free abstraction.
    Snapshot(SourceObjectId),
}

pub struct Cell {
    pub key: CellKey,
    pub ts: TypeSet,
    changes: u16,
}

/// The solver state: the cell graph, the constraints over it, and the
/// worklist that brings the two to a fixpoint.
///
/// A *cell* holds the typeset of one program location (a local in a
/// context, a field of an abstraction, a global binding). A *constraint*
/// is one dataflow edge, generated once per script and evaluated once per
/// context the script is live at. Evaluating an edge reads its source
/// cells -- which subscribes it to them -- and raises its destination; a
/// raise that grows a cell re-fires that cell's subscribers. The fixpoint
/// is reached when the worklist drains.
#[derive(Default)]
pub struct Engine {
    /// Every cell, indexed by [`CellId`].
    pub cells: Vec<Cell>,
    cell_ids: HashMap<CellKey, CellId>,
    /// Every constraint, indexed by [`ConId`].
    pub cons: Vec<Constraint>,
    /// The script each constraint was generated for, indexed by [`ConId`]:
    /// the context-relative `CKey`s in a constraint resolve against it.
    pub con_script: Vec<ScriptId>,
    /// The reverse index: a script's constraint ids, in emission order.
    pub script_cons: HashMap<ScriptId, Vec<ConId>>,
    /// Contexts a script has been instantiated at (its live rows).
    pub live_ctxs: HashMap<ScriptId, Vec<CtxId>>,
    worklist: VecDeque<(ConId, CtxId)>,
    inq: HashSet<(ConId, CtxId)>,
    /// Dynamic subscriptions: cell -> (constraint, ctx) pairs to re-fire
    /// when the cell grows. Installed on first read, permanent.
    subs: HashMap<CellId, Vec<(ConId, CtxId)>>,
    sub_set: HashSet<(CellId, ConId, CtxId)>,
    /// Standing cell -> cell edges (`ClassView` feeds, proto plumbing):
    /// a raise propagates through them immediately.
    links: HashMap<CellId, Vec<CellId>>,
    link_set: HashSet<(CellId, CellId)>,
    /// The join-visible labels of each abstraction, indexed by [`AbsId`]
    /// and assigned at intern time by the heap layer; what makes joins
    /// order-independent.
    pub abs_labels: Vec<AbsLabels>,
    /// Census counters: evaluations, raises.
    pub n_evals: u64,
    pub n_raises: u64,
    /// Class-region union-find (parent map). A *region* is the set of
    /// classes whose instances have been observed meeting; it is what a
    /// meet of two differently-classed objects labels itself with instead
    /// of collapsing to AnyObject. One union-find serves both kinds of
    /// region (array and non-array) -- they differ in the meet rule, not
    /// in the representation. Deterministic min-root; unions happen at
    /// join time.
    region_parent: HashMap<ClassId, ClassId>,
    /// Region root -> member classes (root included). Absent = singleton.
    pub region_members: HashMap<ClassId, Vec<ClassId>>,
    /// Classes whose instances are arrays: the site classes minted for
    /// plain-array allocations. Membership decides which meet rule two
    /// classed objects take (see `join_ts`).
    pub array_classes: HashSet<ClassId>,
    /// The interned elems name (set once by the solver; view links need it).
    pub elems_name: Option<NameId>,
    /// AnyObject-transition attribution: constraint -> number of cells it
    /// flipped to AnyObject (the design's failure mode, so its provenance
    /// is a first-class census).
    pub anyobj_why: HashMap<ConId, u32>,
    /// The first transitions, in order (genesis vs cascade).
    pub anyobj_first: Vec<(CellKey, ConId)>,
    /// Join diagnostics (One+One absorption pairs, dropped fn ids);
    /// censused only -- nothing consumes them.
    pub sink: JoinSink,
}

impl Engine {
    /// The cell for `key` if one was ever created (no allocation).
    pub fn existing_cell(&self, key: CellKey) -> Option<CellId> {
        self.cell_ids.get(&key).copied()
    }

    pub fn cell(&mut self, key: CellKey) -> CellId {
        if let Some(&id) = self.cell_ids.get(&key) {
            return id;
        }
        let id = CellId(u32::try_from(self.cells.len()).unwrap());
        self.cells.push(Cell {
            key,
            ts: TypeSet::default(),
            changes: 0,
        });
        self.cell_ids.insert(key, id);
        id
    }

    pub fn lookup(&self, key: CellKey) -> Option<CellId> {
        self.cell_ids.get(&key).copied()
    }

    /// Every class-view (field) cell, for the viz.
    pub fn field_cells(&self) -> Vec<(ClassId, crate::ids::NameId, CellId)> {
        let mut out: Vec<_> = self
            .cell_ids
            .iter()
            .filter_map(|(k, &id)| match k {
                CellKey::ClassView { class, name } => Some((*class, *name, id)),
                _ => None,
            })
            .collect();
        out.sort_by_key(|(c, n, _)| (c.0, n.0));
        out
    }

    /// Every gname cell (context-free by construction), for the fact
    /// emitter's projection pass.
    pub fn gname_cells(&self) -> Vec<(crate::ids::NameId, CellId)> {
        let mut out: Vec<_> = self
            .cell_ids
            .iter()
            .filter_map(|(k, &id)| match k {
                CellKey::GName(n) => Some((*n, id)),
                _ => None,
            })
            .collect();
        out.sort_by_key(|&(n, _)| n);
        out
    }

    pub fn ts(&self, id: CellId) -> &TypeSet {
        &self.cells[id.0 as usize].ts
    }

    pub fn add_con(&mut self, script: ScriptId, con: Constraint) -> ConId {
        let id = ConId(u32::try_from(self.cons.len()).unwrap());
        self.cons.push(con);
        self.con_script.push(script);
        self.script_cons.entry(script).or_default().push(id);
        id
    }

    /// Enqueue every constraint of `script` at `ctx` (first time only).
    pub fn instantiate(&mut self, script: ScriptId, ctx: CtxId) -> bool {
        let ctxs = self.live_ctxs.entry(script).or_default();
        if ctxs.contains(&ctx) {
            return false;
        }
        ctxs.push(ctx);
        if let Some(cons) = self.script_cons.get(&script) {
            for &c in cons.clone().iter() {
                self.enqueue(c, ctx);
            }
        }
        true
    }

    /// Resolve a constraint-relative cell reference against the script and
    /// context it is being evaluated at.
    pub fn resolve(&mut self, script: ScriptId, ctx: CtxId, k: CKey) -> CellId {
        let key = match k {
            CKey::Var(var) => CellKey::Var { script, var, ctx },
            CKey::Arg(arg) => CellKey::Arg { script, arg, ctx },
            CKey::This => CellKey::This { script, ctx },
            CKey::Ret => CellKey::Ret { script, ctx },
            CKey::GName(name) => CellKey::GName(name),
            CKey::Aliased { scope, slot } => CellKey::Aliased { scope, slot },
        };
        self.cell(key)
    }

    /// Read a cell on behalf of `(con, ctx)`: subscribes the reader (so it
    /// re-fires when the source grows) and returns a snapshot.
    pub fn read(&mut self, id: CellId, user: (ConId, CtxId)) -> TypeSet {
        if self.sub_set.insert((id, user.0, user.1)) {
            self.subs.entry(id).or_default().push(user);
        }
        self.cells[id.0 as usize].ts.clone()
    }

    /// The region root of a class: the representative of every class this
    /// one has met with. A class that has never met another is its own
    /// root.
    pub fn region_root(&self, c: ClassId) -> ClassId {
        let mut cur = c;
        while let Some(&p) = self.region_parent.get(&cur) {
            if p == cur {
                break;
            }
            cur = p;
        }
        cur
    }

    /// Merge two classes' regions (min root wins, deterministically) and
    /// chain the loser's elems view into the winner's, so a read through
    /// the merged root sees both populations' elements. Merging a class
    /// with itself, or with a class already in its region, is just
    /// [`Engine::region_root`] -- the early return below is what lets
    /// callers hand it any pair.
    fn union_regions(&mut self, c: ClassId, d: ClassId) -> ClassId {
        let rc = self.region_root(c);
        let rd = self.region_root(d);
        if rc == rd {
            return rc;
        }
        let (win, lose) = if rc < rd { (rc, rd) } else { (rd, rc) };
        self.region_parent.insert(lose, win);
        let lm = self
            .region_members
            .remove(&lose)
            .unwrap_or_else(|| vec![lose]);
        self.region_members
            .entry(win)
            .or_insert_with(|| vec![win])
            .extend(lm);
        if let Some(en) = self.elems_name {
            let from = self.cell(CellKey::ClassView {
                class: lose,
                name: en,
            });
            let to = self.cell(CellKey::ClassView {
                class: win,
                name: en,
            });
            self.link(from, to);
        }
        win
    }

    /// The class of an object part whose instances are arrays, when it has
    /// one. `None` for a non-array part, a part with no class at all, and
    /// for `AnyOf` -- a non-array region by construction, since the meet
    /// rule below never puts an array class in one.
    fn array_region_of(&self, o: super::types::ObjType) -> Option<ClassId> {
        use super::types::ObjType::*;
        match o {
            One(a) => {
                let m = self.abs_labels.get(a.0 as usize)?;
                if m.array {
                    m.class
                        .filter(|c| self.array_classes.contains(&self.region_root(*c)))
                } else {
                    None
                }
            }
            ClassAny(c) => {
                if self.array_classes.contains(&self.region_root(c)) {
                    Some(c)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// The class (or, for `AnyOf`, the region root) an object part carries,
    /// plus whether its instances are arrays. The `AnyOf` arm answers
    /// `false` unconditionally because the meet rule below only ever forms
    /// an `AnyOf` region out of non-array classes.
    fn class_and_arrayness(&self, o: super::types::ObjType) -> (Option<ClassId>, bool) {
        use super::types::ObjType::*;
        match o {
            One(a) => match self.abs_labels.get(a.0 as usize) {
                Some(m) => (m.class, m.array),
                None => (None, false),
            },
            ClassAny(c) => (Some(c), self.array_classes.contains(&self.region_root(c))),
            AnyOf(r) => (Some(r), false),
            _ => (None, false),
        }
    }

    /// Engine-aware typeset join: `TypeSet::join_from` plus the two cases
    /// where two classed object parts, instead of collapsing to AnyObject,
    /// merge their classes into one region and meet as that region.
    ///
    /// Arrays are not a separate world in the model -- an array's elements
    /// live in an ordinary field cell under the reserved `ELEMS` name, and
    /// arrayness is one bit on the class. What is array-specific is only
    /// this meet rule, in three cases:
    ///
    /// - array meets array -> `ClassAny(root)`. The merged root keeps a
    ///   class, so reads still go through the element view cell of that
    ///   population.
    /// - non-array meets non-array -> `AnyOf(root)`, the weaker label: a
    ///   read through it yields unresolved evidence (plus, at callee
    ///   position, the region's method-table union).
    /// - array meets non-array -> `AnyObject`. Merging the two would put
    ///   every array population into the same region as every object
    ///   population it ever met.
    ///
    /// Collapsing all three cases into the `AnyOf` rule would land every
    /// array population of a program in one region, so
    /// `array_alloc_sites`/`array_elem_recv`/`typed_sites` could no
    /// longer tell them apart.
    pub fn join_ts(&mut self, dst: &mut TypeSet, src: &TypeSet) -> bool {
        use super::types::ObjType;
        let jo = match (self.array_region_of(dst.obj), self.array_region_of(src.obj)) {
            (Some(c), Some(d)) => Some(ObjType::ClassAny(self.union_regions(c, d))),
            _ => {
                let pure = super::types::join_obj(dst.obj, src.obj, &self.abs_labels);
                if pure == ObjType::AnyObject {
                    let (ca, aa) = self.class_and_arrayness(dst.obj);
                    let (cb, ab) = self.class_and_arrayness(src.obj);
                    match (ca, cb) {
                        (Some(c), Some(d)) if !aa && !ab => {
                            Some(ObjType::AnyOf(self.union_regions(c, d)))
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            }
        };
        let changed = dst.join_from(src, &self.abs_labels, &mut self.sink);
        match jo {
            Some(j) if dst.obj != j => {
                dst.obj = j;
                true
            }
            Some(_) => changed,
            None => changed,
        }
    }

    /// Join one cell across every context a script was live at.
    ///
    /// Deliberately not [`Engine::join_ts`]: this is the projection the
    /// emission and the trace use, and it must not merge class regions.
    /// `join_ts` unions the region union-find as a side effect, which is
    /// right while the fixpoint is running and wrong afterwards -- reading
    /// out an answer should not change it. So the object part here keeps
    /// the last non-empty label rather than meeting the labels, and the
    /// consumers only ask coarse questions of it ("was there an object at
    /// all", "which single class").
    ///
    /// Every other component joins exactly as `TypeSet::join_from` does,
    /// the object part being the single deliberate difference.
    pub fn join_over_ctxs(&self, ctxs: &[CtxId], mk: impl Fn(CtxId) -> CellKey) -> Option<TypeSet> {
        let mut joined: Option<TypeSet> = None;
        for &ctx in ctxs {
            let Some(cid) = self.lookup(mk(ctx)) else {
                continue;
            };
            let ts = self.ts(cid).clone();
            match &mut joined {
                None => joined = Some(ts),
                Some(j) => {
                    j.prims |= ts.prims;
                    j.unknown |= ts.unknown;
                    if ts.range > j.range {
                        j.range = ts.range;
                    }
                    if ts.obj != super::types::ObjType::Empty {
                        j.obj = ts.obj;
                    }
                    if !ts.fns.is_empty() {
                        let f = ts.fns.clone();
                        j.fns.join_from(&f, &mut Vec::new());
                    }
                    j.interval = Interval::join(j.interval, ts.interval);
                }
            }
        }
        joined
    }

    /// Monotone raise; on growth, re-fires the cell's subscribers.
    pub fn raise(&mut self, id: CellId, ts: &TypeSet, why: (ConId, CtxId)) {
        self.trace_cell(id, ts, why);
        {
            // No-growth fast path: cells change O(1) times but are raised
            // constantly, and the clone + engine join per raise is
            // allocation-heavy. Conservatively limited to raises that
            // cannot trigger a region merge or relabel: prim/fn/range/
            // interval subset with an Empty or identical non-array obj
            // part.
            let cur = &self.cells[id.0 as usize].ts;
            if ts.prims | cur.prims == cur.prims
                && ts.fns.is_subset_of(&cur.fns)
                && (ts.obj == super::types::ObjType::Empty
                    || (ts.obj == cur.obj && self.array_region_of(ts.obj).is_none()))
                && ts.range <= cur.range
                && cur.interval.subsumes(ts.interval)
            {
                return;
            }
        }
        let was_anyobj = self.cells[id.0 as usize].ts.obj == super::types::ObjType::AnyObject;
        let mut joined = self.cells[id.0 as usize].ts.clone();
        if !self.join_ts(&mut joined, ts) {
            return;
        }
        self.cells[id.0 as usize].ts = joined;
        let cell = &mut self.cells[id.0 as usize];
        let flipped_anyobj = !was_anyobj && cell.ts.obj == super::types::ObjType::AnyObject;
        let key = cell.key;
        if flipped_anyobj {
            *self.anyobj_why.entry(why.0).or_insert(0) += 1;
            if self.anyobj_first.len() < 12 {
                self.anyobj_first.push((key, why.0));
            }
        }
        cell.changes += 1;
        debug_assert!(
            cell.changes <= MAX_CELL_CHANGES,
            "cell {:?} exceeded the lattice-height change bound",
            cell.key
        );
        self.n_raises += 1;
        if let Some(users) = self.subs.get(&id) {
            for &(c, ctx) in users {
                if self.inq.insert((c, ctx)) {
                    self.worklist.push_back((c, ctx));
                }
            }
        }
        if let Some(dsts) = self.links.get(&id) {
            let v = self.cells[id.0 as usize].ts.clone();
            for d in dsts.clone() {
                self.raise(d, &v, why);
            }
        }
    }

    /// Install a standing `src -> dst` edge and propagate the current value
    /// (idempotent). Termination through link cycles comes from `raise`
    /// stopping at no-change.
    pub fn link(&mut self, src: CellId, dst: CellId) {
        if src == dst || !self.link_set.insert((src, dst)) {
            return;
        }
        self.links.entry(src).or_default().push(dst);
        let v = self.cells[src.0 as usize].ts.clone();
        if !v.is_empty() {
            self.raise(dst, &v, (SEED, CTX0));
        }
    }

    /// Debug tracer for one cell (`--trace-cell arg:<sid>:<n>` or
    /// `local:<sid>:<n>`): every raise into it, with the incoming object
    /// type and the constraint responsible. Answers "which writer made this
    /// slot AnyObject", which no census can, because the answer is a single
    /// join step inside the solver.
    fn trace_cell(&self, id: CellId, ts: &TypeSet, why: (ConId, CtxId)) {
        let Some(want) = super::tracers().cell.as_ref() else {
            return;
        };
        let key = self.cells[id.0 as usize].key;
        let got = match key {
            CellKey::Arg { script, arg, .. } => format!("arg:{}:{}", script.get(), arg.get()),
            CellKey::Var { script, var, .. } => format!("local:{}:{}", script.get(), var.get()),
            _ => return,
        };
        if got != *want {
            return;
        }
        let src = self.con_script.get(why.0 .0 as usize).copied();
        let con = self
            .cons
            .get(why.0 .0 as usize)
            .map_or_else(|| "?".to_string(), |c| format!("{c:?}"));
        crate::diag_line!(
            "night: tracecell {got} <- obj {:?} unknown {} from sid {:?} con {}",
            ts.obj,
            u8::from(ts.unknown),
            src.map(|s| s.get()),
            con
        );
    }

    pub fn enqueue(&mut self, con: ConId, ctx: CtxId) {
        if self.inq.insert((con, ctx)) {
            self.worklist.push_back((con, ctx));
        }
    }

    pub fn pop(&mut self) -> Option<(ConId, CtxId)> {
        let item = self.worklist.pop_front()?;
        self.inq.remove(&item);
        self.n_evals += 1;
        Some(item)
    }

    /// Core structural constraints (`Move`/`Const`). Heap and call
    /// constraints are dispatched by the solver layers above.
    pub fn eval_core(&mut self, con: ConId, ctx: CtxId) -> bool {
        let sid = self.con_script[con.0 as usize];
        match self.cons[con.0 as usize].clone() {
            Constraint::Move { src, dst } => {
                let s = self.resolve(sid, ctx, src);
                let d = self.resolve(sid, ctx, dst);
                let v = self.read(s, (con, ctx));
                self.raise(d, &v, (con, ctx));
                true
            }
            Constraint::Const { dst, ts } => {
                let d = self.resolve(sid, ctx, dst);
                self.raise(d, &ts, (con, ctx));
                true
            }
            Constraint::Arith {
                op,
                a,
                b,
                dst,
                a_lit,
                b_lit,
                pc: _,
            } => {
                let ca = self.resolve(sid, ctx, a);
                let ta = self.read(ca, (con, ctx));
                let tb = b.map(|k| {
                    let cb = self.resolve(sid, ctx, k);
                    self.read(cb, (con, ctx))
                });
                let (m, r) = super::types::arith_transfer(op, &ta, tb.as_ref());
                let interval = super::types::arith_interval(
                    op,
                    super::types::operand_interval(&ta),
                    a_lit,
                    tb.as_ref().map(super::types::operand_interval),
                    b_lit,
                );
                // The interval component flows even when the mask side is
                // empty (mask-invisible shadow operands carry interval only).
                if m != Prims::EMPTY || interval != Interval::Empty {
                    let d = self.resolve(sid, ctx, dst);
                    self.raise(d, &TypeSet::prim_interval(m, r, interval), (con, ctx));
                }
                true
            }
            _ => false,
        }
    }
}

/// Drive `eval` to fixpoint. `eval` must fully handle every constraint kind
/// present (the solver composes `eval_core` with heap/call evaluation).
pub fn run(engine: &mut Engine, mut eval: impl FnMut(&mut Engine, ConId, CtxId)) {
    while let Some((c, ctx)) = engine.pop() {
        eval(engine, c, ctx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const S1: ScriptId = ScriptId::new(1);
    const S2: ScriptId = ScriptId::new(2);
    use crate::likelier::types::{BoundedFnSet, FnId, ObjType};
    use crate::opsem::{PRIM_DOUBLE, PRIM_INT32};

    fn core_solver(e: &mut Engine) {
        run(e, |e, c, ctx| {
            let handled = e.eval_core(c, ctx);
            assert!(handled, "test graphs use only core constraints");
        });
    }

    /// A diamond with a cycle: v0 -> v1 -> v2 -> v1 (loop), v2 -> v3.
    fn build_cycle(e: &mut Engine) {
        e.add_con(
            S1,
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::prim(PRIM_INT32),
            },
        );
        e.add_con(
            S1,
            Constraint::Move {
                src: CKey::Var(VarId::new(0)),
                dst: CKey::Var(VarId::new(1)),
            },
        );
        e.add_con(
            S1,
            Constraint::Move {
                src: CKey::Var(VarId::new(1)),
                dst: CKey::Var(VarId::new(2)),
            },
        );
        e.add_con(
            S1,
            Constraint::Move {
                src: CKey::Var(VarId::new(2)),
                dst: CKey::Var(VarId::new(1)),
            },
        );
        e.add_con(
            S1,
            Constraint::Move {
                src: CKey::Var(VarId::new(2)),
                dst: CKey::Var(VarId::new(3)),
            },
        );
        e.add_con(
            S1,
            Constraint::Const {
                dst: CKey::Var(VarId::new(2)),
                ts: TypeSet::prim(PRIM_DOUBLE),
            },
        );
    }

    #[test]
    fn fixpoint_through_cycle() {
        let mut e = Engine::default();
        build_cycle(&mut e);
        e.instantiate(S1, CTX0);
        core_solver(&mut e);
        let v3 = e
            .lookup(CellKey::Var {
                script: S1,
                var: VarId::new(3),
                ctx: CTX0,
            })
            .unwrap();
        assert_eq!(e.ts(v3).prims, PRIM_INT32 | PRIM_DOUBLE);
        // The back edge propagated the loop-added double into v1 too.
        let v1 = e
            .lookup(CellKey::Var {
                script: S1,
                var: VarId::new(1),
                ctx: CTX0,
            })
            .unwrap();
        assert_eq!(e.ts(v1).prims, PRIM_INT32 | PRIM_DOUBLE);
    }

    #[test]
    fn refire_on_late_source_growth() {
        // A reader that evaluates before its source is written must re-fire:
        // the exact failure mode of one-way edges without a fixpoint.
        let mut e = Engine::default();
        // Script 1 reads gname g into v0 (evaluates first).
        let mut names = crate::likelier::types::Names::default();
        let g = names.intern(&[103]);
        e.add_con(
            S1,
            Constraint::Move {
                src: CKey::GName(g),
                dst: CKey::Var(VarId::new(0)),
            },
        );
        // Script 2 writes g (instantiated after script 1 has quiesced).
        e.instantiate(S1, CTX0);
        core_solver(&mut e);
        e.add_con(
            S2,
            Constraint::Const {
                dst: CKey::GName(g),
                ts: TypeSet::fn_one(FnId::script(ScriptId::new(42))),
            },
        );
        e.instantiate(S2, CTX0);
        core_solver(&mut e);
        let v0 = e
            .lookup(CellKey::Var {
                script: S1,
                var: VarId::new(0),
                ctx: CTX0,
            })
            .unwrap();
        assert_eq!(
            e.ts(v0).fns,
            BoundedFnSet::one(FnId::script(ScriptId::new(42)))
        );
    }

    #[test]
    fn per_ctx_rows_are_distinct() {
        let mut e = Engine::default();
        e.add_con(
            S1,
            Constraint::Move {
                src: CKey::Arg(FormalIndex::new(0)),
                dst: CKey::Ret,
            },
        );
        let ctx1 = CtxId(1);
        e.instantiate(S1, CTX0);
        e.instantiate(S1, ctx1);
        let a0 = e.cell(CellKey::Arg {
            script: S1,
            arg: FormalIndex::new(0),
            ctx: CTX0,
        });
        let a1 = e.cell(CellKey::Arg {
            script: S1,
            arg: FormalIndex::new(0),
            ctx: ctx1,
        });
        e.raise(a0, &TypeSet::prim(PRIM_INT32), (ConId(0), CTX0));
        e.raise(a1, &TypeSet::prim(PRIM_DOUBLE), (ConId(0), ctx1));
        core_solver(&mut e);
        let r0 = e
            .lookup(CellKey::Ret {
                script: S1,
                ctx: CTX0,
            })
            .unwrap();
        let r1 = e
            .lookup(CellKey::Ret {
                script: S1,
                ctx: ctx1,
            })
            .unwrap();
        assert_eq!(e.ts(r0).prims, PRIM_INT32);
        assert_eq!(e.ts(r1).prims, PRIM_DOUBLE);
    }

    #[test]
    #[allow(clippy::field_reassign_with_default)]
    fn one_plus_one_meets_as_class_any() {
        let mut e = Engine::default();
        // classes: abs 0,1 -> class 0
        e.abs_labels = vec![
            AbsLabels {
                class: Some(ClassId(0)),
                snap: false,
                array: false,
            },
            AbsLabels {
                class: Some(ClassId(0)),
                snap: false,
                array: false,
            },
            AbsLabels::default(),
        ];
        build_cycle(&mut e);
        e.add_con(
            S1,
            Constraint::Const {
                dst: CKey::Var(VarId::new(1)),
                ts: TypeSet::obj_one(AbsId(0)),
            },
        );
        e.add_con(
            S1,
            Constraint::Const {
                dst: CKey::Var(VarId::new(2)),
                ts: TypeSet::obj_one(AbsId(1)),
            },
        );
        e.instantiate(S1, CTX0);
        core_solver(&mut e);
        let v1 = e
            .lookup(CellKey::Var {
                script: S1,
                var: VarId::new(1),
                ctx: CTX0,
            })
            .unwrap();
        assert_eq!(e.ts(v1).obj, ObjType::ClassAny(ClassId(0)));
    }

    #[test]
    fn work_bound_scales_with_edges() {
        // A long chain: total evaluations must stay O(edges), not O(n^2).
        let mut e = Engine::default();
        let n = 2000u32;
        e.add_con(
            S1,
            Constraint::Const {
                dst: CKey::Var(VarId::new(0)),
                ts: TypeSet::prim(PRIM_INT32),
            },
        );
        for i in 0..n {
            e.add_con(
                S1,
                Constraint::Move {
                    src: CKey::Var(VarId::new(i)),
                    dst: CKey::Var(VarId::new(i + 1)),
                },
            );
        }
        e.instantiate(S1, CTX0);
        core_solver(&mut e);
        let last = e
            .lookup(CellKey::Var {
                script: S1,
                var: VarId::new(n),
                ctx: CTX0,
            })
            .unwrap();
        assert_eq!(e.ts(last).prims, PRIM_INT32);
        // Each edge fires at initial instantiation plus at most
        // MAX_CELL_CHANGES re-fires from its source growing.
        assert!(
            e.n_evals <= (u64::from(n) + 1) * (u64::from(MAX_CELL_CHANGES as u32) + 1),
            "evals {} exceed the lattice work bound",
            e.n_evals
        );
    }
}
