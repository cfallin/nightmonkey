/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! `LikelyFacts` production: the solved cell graph projected onto the
//! translator-facing tables.
//!
//! The facts fall into four families, and each has its own emission path
//! below. They are produced in this order because each depends on the one
//! before it:
//!
//! 1. **Value claims** -- what a value at a program point is likely to be.
//!    A script's receiver and formals, a call's result, a closure-slot
//!    read: each is its cell joined over the contexts the script was live
//!    at, projected through the claim tiers. Produced by
//!    [`Solver::emit_value_claims`].
//!
//! 2. **Call-site resolution** -- how each call site resolved, as one
//!    [`CallResolution`]: a modeled native with an inline arm, or a small
//!    set of scripted targets to guard on. Produced by
//!    [`Solver::emit_call_sites`], which also resolves the `.call`/`.apply`
//!    delegation targets the layout analysis walks through.
//!
//! 3. **The predicted heap** -- classes, the regions they meet in, the
//!    field order each class's instances get, and the value claim on each
//!    field. This is the constructor-body analysis, and it lives in
//!    [`LayoutPlan`]: it expands each constructor's `this` writes into an
//!    ordered layout row, assigns the dense keys that let one range guard
//!    cover a whole predictor group, and folds the group's members into the
//!    universal prefix table a range fact reads.
//!
//! 4. **Per-site heap facts** -- for each property and element site, the
//!    key range, slot and claim it may guard on, resolved against the plan.
//!    Produced by [`Solver::emit_site_facts`] and the class rows and array
//!    claims that follow it.

use super::heap::ClassKey;
use super::scan::TEvent;
use super::stats::CapDrops;
use super::types::{observe, Agreed, AgreedSet};
use super::types::{ClassId, NameId, ObjType, TypeSet};
use super::{SharedCtorSite, Solver};
use crate::constants::{LAY_CAP, MAX_DELEG_DEPTH, MAX_SITE_TARGETS, MAX_TRACKED_FORMALS};
use crate::facts::LikelyFacts;
use crate::facts::{CallResolution, Claim, ClassFacts, ClassFieldFacts, ValueRange};
use crate::ids::{
    ArgIndex, FormalIndex, LayoutKey, Pc, RegionRoot, ScriptId, Site, SlotIndex, VarId,
};
use crate::opsem::{Prims, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_UNDEFINED};
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
/// cover. A class that has a constructor groups with every other class of
/// that constructor; a class that does not (an allocation-site class, or
/// one of a shared-generated constructor's per-prototype classes) is its
/// own group.
///
/// The two cases are packed into one integer so the whole key assignment
/// can sort them together; the tag bit keeps the two id spaces from
/// colliding.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(super) struct GroupId(u64);

impl GroupId {
    const CTOR_TAG: u64 = 1 << 32;

    fn of_ctor(f: ScriptId) -> GroupId {
        GroupId(GroupId::CTOR_TAG | u64::from(f.get()))
    }

    fn of_class(c: ClassId) -> GroupId {
        GroupId(u64::from(c.0))
    }

    /// Whether this group is keyed by a constructor script. Only ctor
    /// instances are ever stamped, so a key range holding no ctor group
    /// can never be hit at runtime.
    fn is_ctor(self) -> bool {
        self.0 & GroupId::CTOR_TAG != 0
    }

    /// The constructor script, for a ctor group.
    fn ctor(self) -> Option<ScriptId> {
        self.is_ctor().then(|| ScriptId::new(self.0 as u32))
    }

    /// The class, for a group that is one class of its own.
    fn class(self) -> Option<ClassId> {
        (!self.is_ctor()).then_some(ClassId(self.0 as u32))
    }
}

/// An ordered layout row under construction: the field names a constructor
/// or literal site installs, in first-write order.
///
/// Bounded by `LAY_CAP` (a row longer than that is not a layout anybody
/// can guard on) and duplicate-free -- a field written twice keeps the
/// position of its first write, since that is where the slot was created.
#[derive(Default)]
struct LayoutRow {
    names: Vec<NameId>,
    /// Names refused because the row was already full.
    dropped: u64,
}

impl LayoutRow {
    fn push(&mut self, name: NameId) {
        if self.names.contains(&name) {
            return;
        }
        if self.names.len() >= LAY_CAP {
            self.dropped += 1;
            return;
        }
        self.names.push(name);
    }

    fn into_names(self) -> Vec<NameId> {
        self.names
    }
}

/// Where one field name sits across a set of layout rows.
#[derive(Clone, Copy)]
struct NameFold {
    /// The slot every row carrying the name put it at, or `None` once two
    /// rows disagreed. Only a name at the same slot in every row can join
    /// the group's universal prefix.
    slot: Option<SlotIndex>,
    /// How many of the folded rows carry the name at all.
    rows: u32,
}

/// The agreement between several layout rows.
///
/// A group's members do not have to share a layout, but the leading fields
/// they *do* share -- same name, same slot, in every member -- are what a
/// range guard over the whole group can serve. Folding the rows together
/// and then reading off slot 0, 1, 2, ... until one disagrees is how that
/// common prefix is found.
#[derive(Default)]
struct SlotFold {
    rows: u32,
    names: HashMap<NameId, NameFold>,
}

impl SlotFold {
    /// Fold one layout row into the running agreement.
    fn add_row(&mut self, row: &[NameId]) {
        self.rows += 1;
        for (i, name) in row.iter().enumerate() {
            let slot = SlotIndex::new(u32::try_from(i).unwrap());
            match self.names.get_mut(name) {
                None => {
                    self.names.insert(
                        *name,
                        NameFold {
                            slot: Some(slot),
                            rows: 1,
                        },
                    );
                }
                Some(e) => {
                    if e.slot != Some(slot) {
                        e.slot = None;
                    }
                    e.rows += 1;
                }
            }
        }
    }

    /// The names every folded row placed at the same slot, in slot order,
    /// stopping at the first slot they do not all agree on.
    fn universal_prefix(&self) -> Vec<NameId> {
        let mut by_slot: HashMap<SlotIndex, NameId> = HashMap::default();
        for (name, fold) in &self.names {
            if let Some(s) = fold.slot {
                if fold.rows == self.rows {
                    by_slot.insert(s, *name);
                }
            }
        }
        let mut prefix: Vec<NameId> = Vec::new();
        let mut i = 0u32;
        while (i as usize) < LAY_CAP {
            match by_slot.remove(&SlotIndex::new(i)) {
                Some(n) => {
                    prefix.push(n);
                    i += 1;
                }
                None => break,
            }
        }
        prefix
    }
}

/// Expands a constructor's `this`-write events into the ordered layout row
/// its instances end up with.
///
/// A constructor rarely installs every field itself: it hands `this` to
/// helpers (`Base.call(this, ...)`, `this.init(...)`) that install the
/// rest. The row is therefore the constructor's own writes with each
/// delegation target's row spliced in at the point of the call, which is
/// where those writes happen at runtime and so where the slots are
/// created.
///
/// One expander serves a whole emission pass: it carries the memo and the
/// participant attribution across every constructor it is asked about, so
/// a helper shared by two constructors is expanded once and noticed as
/// shared. The two channels (with and without `this.m(...)` delegates) are
/// separate expanders, so neither channel's attribution disturbs the
/// other's.
struct CtorRowExpander<'a> {
    /// Per-script `this` events, from the scan.
    events: &'a HashMap<ScriptId, Vec<TEvent>>,
    /// The single resolved `.call`/`.apply` target per site.
    apply_targets: &'a HashMap<Site, ScriptId>,
    /// The single scripted callee of a site, where it has exactly one:
    /// what a `this.m(...)` init delegate resolves through.
    single_call_target: &'a HashMap<Site, ScriptId>,
    /// Whether to follow `this.m(...)` init delegates as well as
    /// `.call`/`.apply` ones. The two-phase channel does; the row that
    /// gets stamped at constructor exit does not, since those calls have
    /// not happened yet.
    follow_this_method_delegates: bool,
    /// Rows already computed, one per script.
    memo: HashMap<ScriptId, Vec<NameId>>,
    /// Delegation target -> the top-level constructor that splices it,
    /// while exactly one does. A target spliced by one constructor can be
    /// attributed to that constructor's layout; one spliced by two cannot.
    participants: HashMap<ScriptId, Agreed<ScriptId>>,
    /// What the row and depth caps refused while expanding (see
    /// [`stats::CapDrops`]).
    caps: CapDrops,
}

impl<'a> CtorRowExpander<'a> {
    fn new(
        events: &'a HashMap<ScriptId, Vec<TEvent>>,
        apply_targets: &'a HashMap<Site, ScriptId>,
        single_call_target: &'a HashMap<Site, ScriptId>,
        follow_this_method_delegates: bool,
    ) -> CtorRowExpander<'a> {
        CtorRowExpander {
            events,
            apply_targets,
            single_call_target,
            follow_this_method_delegates,
            memo: HashMap::default(),
            participants: HashMap::default(),
            caps: CapDrops::default(),
        }
    }

    /// The layout row of constructor `top`.
    fn expand(&mut self, top: ScriptId) -> Vec<NameId> {
        self.expand_under(top, top, 0)
    }

    /// The memoization layer: a script's row does not depend on which
    /// top-level constructor asked for it, so it is computed once. The
    /// pre-insert of an empty row is also the cycle guard -- a delegation
    /// cycle sees the empty row rather than recursing forever.
    fn expand_under(&mut self, f: ScriptId, top: ScriptId, depth: u32) -> Vec<NameId> {
        if let Some(v) = self.memo.get(&f) {
            return v.clone();
        }
        if depth > MAX_DELEG_DEPTH {
            self.caps.deleg_depth += 1;
            return Vec::new();
        }
        self.memo.insert(f, Vec::new());
        let row = self.collect(f, top, depth);
        self.memo.insert(f, row.clone());
        row
    }

    /// Walk `f`'s own events in program order, appending its writes and
    /// splicing each delegation target's row where the call sits.
    fn collect(&mut self, f: ScriptId, top: ScriptId, depth: u32) -> Vec<NameId> {
        let mut out = LayoutRow::default();
        let Some(events) = self.events.get(&f).cloned() else {
            return out.into_names();
        };
        for ev in &events {
            let target = match ev {
                TEvent::Write(n) => {
                    out.push(*n);
                    None
                }
                TEvent::Deleg(pc) => self.apply_targets.get(&Site::new(f, *pc)).copied(),
                TEvent::DelegM(pc) => self
                    .follow_this_method_delegates
                    .then(|| self.single_call_target.get(&Site::new(f, *pc)).copied())
                    .flatten(),
            };
            let Some(t) = target else { continue };
            if t == f {
                continue;
            }
            self.note_participant(t, top);
            for n in &self.expand_under(t, top, depth + 1) {
                out.push(*n);
            }
        }
        self.caps.layout_fields += out.dropped;
        out.into_names()
    }

    fn note_participant(&mut self, target: ScriptId, top: ScriptId) {
        observe(&mut self.participants, target, top);
    }
}

/// The mask layout `key` claims for `name`, or empty when the layout does
/// not carry the name at all.
fn name_mask(rows: &HashMap<u32, LayoutRowFacts>, key: u32, name: NameId) -> Prims {
    rows.get(&key)
        .and_then(|r| {
            let p = r.names.iter().position(|n| *n == name)?;
            r.masks.get(p).copied()
        })
        .unwrap_or(Prims::EMPTY)
}

/// The per-slot masks of a universal prefix table over keys `lo..=hi`: the
/// all-members rule, so a slot claims only what every member of the range
/// claims, at that same slot. One member that puts a different name there,
/// or claims nothing, empties the slot for everybody -- the fact is read
/// through a range guard, so it has to hold for every key in range.
fn prefix_masks(
    rows: &HashMap<u32, LayoutRowFacts>,
    ptable: &[NameId],
    lo: u32,
    hi: u32,
) -> Vec<Prims> {
    ptable
        .iter()
        .enumerate()
        .map(|(slot, name)| {
            let mut bits = Prims::EMPTY;
            for k in lo..=hi {
                let m = name_mask(rows, k, *name);
                let at_slot = rows.get(&k).and_then(|r| r.names.get(slot)) == Some(name);
                if m == Prims::EMPTY || !at_slot {
                    bits = Prims::EMPTY;
                    break;
                }
                bits |= m;
            }
            bits
        })
        .collect()
}

// --- family 3: the predicted heap ----------------------------------------

/// Record a slot fact for `site`, if the site may take it. A read may
/// always take one; a write may only take a fact the whole key run agrees
/// on, since a store has to maintain the claim for whichever key its
/// receiver actually carries.
fn insert_prop_site(facts: &mut LikelyFacts, site: Site, f: SlotFact, is_read: bool) {
    if !is_read && !f.uniform {
        return;
    }
    facts.prop_sites.insert(
        site,
        (
            LayoutKey::new(f.lo),
            LayoutKey::new(f.hi),
            f.slot,
            Claim::of_prims(f.prims),
        ),
    );
}

/// The entries of an agreement table that still agree, in key order.
///
/// The tables this drains (`method_home`, an expander's `participants`) map
/// a script to the one constructor that claims it, and every consumer wants
/// the same thing: the settled pairs, deterministically ordered.
fn sole_participants(m: &HashMap<ScriptId, Agreed<ScriptId>>) -> Vec<(ScriptId, ScriptId)> {
    let mut v: Vec<(ScriptId, ScriptId)> = m
        .iter()
        .filter_map(|(&k, a)| a.value().map(|c| (k, c)))
        .collect();
    v.sort_unstable();
    v
}

/// The predictor groups in key-assignment order.
///
/// Region-contiguous: groups whose classes share a region (the class
/// union-find) occupy one contiguous super-range, so a region fact is a
/// range test over the same stamped key space. The sort key is (earliest
/// group of the region, group id), so singleton regions keep the plain
/// group-id order.
fn ordered_groups(sv: &Solver<'_>, rows: &RowSet) -> Vec<GroupId> {
    let mut groups: Vec<GroupId> = super::sorted_keys(&rows.folds);
    let mut region_rep: HashMap<ClassId, GroupId> = HashMap::default();
    for &g in &groups {
        if let Some(c) = sv.class_of_group(g) {
            region_rep.entry(sv.engine.region_root(c)).or_insert(g);
        }
    }
    // Regions with constructor rows key first: the construct-time early
    // key is a 12-bit field (EARLY_KEY_MAX), and a program with enough
    // object-literal classes can push every ctor key past it, leaving
    // every construct site to seed a keyless word that no add can be
    // checked against and no class can earn SLOTS through. Literal-only
    // regions take the high keys; a literal's key is never seeded as an
    // early key.
    let has_ctor: HashMap<ClassId, bool> = groups
        .iter()
        .filter_map(|&g| sv.class_of_group(g).map(|c| (sv.engine.region_root(c), g)))
        .fold(HashMap::default(), |mut m, (r, g)| {
            let e = m.entry(r).or_insert(false);
            *e |= rows.ctor_rows.get(&g).is_some_and(|v| !v.is_empty());
            m
        });
    groups.sort_by_key(|&g| match sv.class_of_group(g) {
        Some(c) => {
            let r = sv.engine.region_root(c);
            (
                !has_ctor.get(&r).copied().unwrap_or(false),
                region_rep[&r],
                g,
            )
        }
        None => (rows.ctor_rows.get(&g).is_none_or(|v| v.is_empty()), g, g),
    });
    groups
}

/// One predicted layout row: the field names in slot order, with the claim
/// and the value range each position carries.
///
/// Keying one map by a row makes "a key has all three, of the same length"
/// a type rather than a convention, and gives the mask/range pairing rule
/// (`pair_ranges`) exactly one place to be applied.
struct LayoutRowFacts {
    names: Vec<NameId>,
    masks: Vec<Prims>,
    ranges: Vec<Option<ValueRange>>,
}

/// The predicted-instance-layout half of the analysis: what each
/// constructor's objects look like, and the key space the guards range
/// over.
///
/// This is one analysis with three products, and they have to be built
/// together because each one's shape constrains the next:
///
/// - **Rows.** A constructor's layout row is the ordered list of fields its
///   instances get, expanded from its `this` writes with its delegates'
///   writes spliced in ([`CtorRowExpander`]). Object literals get a row
///   from their initializer order.
/// - **Keys.** Every row gets a dense [`LayoutKey`]. Keys are assigned so
///   that one predictor group is contiguous and one class region is
///   contiguous, which is what turns "is the receiver one of these
///   classes" into a range compare on the object's stamped class word.
/// - **Tables.** Members of a group rarely share a whole layout, but they
///   share a prefix; the fold of their rows ([`SlotFold`]) is the part a
///   range guard can serve, with the all-members mask rule.
///
/// Nothing here reads a per-site fact -- it is the map the per-site
/// emission resolves against.
#[derive(Default)]
pub(super) struct LayoutPlan {
    /// Layout key -> its row.
    rows: HashMap<u32, LayoutRowFacts>,
    /// Predictor group -> its contiguous key range.
    group_range: HashMap<GroupId, (u32, u32)>,
    /// Per-(script, formal): names written with the formal as receiver
    /// and one write site each -- the arg-restamp derivation's input.
    arg_fill: HashMap<(ScriptId, u32), Vec<(NameId, Site)>>,
    /// (script, formal) pairs the body reassigns (SetArg): a return-time
    /// stamp of the slot could stamp a different object.
    arg_reassigned: HashSet<(ScriptId, u32)>,
    /// Write sites per agreed receiver class and name, and every write
    /// site whose receiver was a local or formal (the fill channel): a
    /// fill row refuses when a suffix name is written on the class from
    /// outside the channel, whose add order it cannot see.
    class_writes: HashMap<(ClassId, NameId), Vec<Site>>,
    fill_sites: HashSet<Site>,
    /// Names written on a `this` with no agreed class at all.
    unplaced_writes: HashSet<NameId>,
    /// Names written on a `this` agreed to each class.
    this_writes: HashMap<ClassId, HashSet<NameId>>,
    /// Classes whose instances call a method whose `this` is pinned to
    /// another class: two identities for one population (box2d's
    /// b2Simplex, whose `ReadCache` is pinned to a rowless twin). A fill
    /// row refuses a name its aliases write on `this`.
    class_aliases: HashMap<ClassId, Vec<ClassId>>,
    /// The adds of every admitted fill run, and the run's reads of the
    /// names it adds: they execute on an object still at the prefix key,
    /// so a full-key fact there is a miss on every execution.
    fill_add_sites: HashSet<Site>,
    /// Group LO key -> the group's universal prefix table and its masks.
    group_tables: HashMap<u32, (Vec<NameId>, Vec<Prims>)>,
    /// Class region root -> the contiguous key range spanning its groups.
    region_range: HashMap<ClassId, (u32, u32)>,
    /// Class region root -> the region's universal prefix table and masks.
    region_tables: HashMap<ClassId, (Vec<NameId>, Vec<Prims>)>,
    /// Class-keyed groups whose key IS stamped (shared-ctor classes: the
    /// init delegate restamps at its returns), unlike lit-only class
    /// groups.
    stamped_class_groups: HashSet<GroupId>,
    /// Constructor -> (stamp key, full key). The two differ only for a
    /// two-phase constructor, whose pair is key-adjacent: the prefix it
    /// stamps at its own exit, and the full row its init delegate
    /// completes.
    ctor_key: HashMap<ScriptId, (u32, u32)>,
    /// Layout key -> the class whose view cell answers for it. Lit-row site
    /// classes are deliberately absent -- an unmapped key makes the range
    /// checks that consult this fail, which is the conservative direction.
    key_class: HashMap<u32, ClassId>,
    /// Script -> the constructor whose layout its `this` is attributed to
    /// (the constructor itself, a method homed to it, or a delegate only it
    /// splices).
    narrow: HashMap<ScriptId, ScriptId>,
    /// Next unassigned layout key.
    next_key: u32,
    /// What the layout caps refused, folded up from the expanders.
    caps: CapDrops,
}

/// One constructor's expanded rows: the prefix its own body installs, and
/// the full row when a `this.m(...)` init delegate extends it (two-phase
/// construction).
struct CtorRows {
    ctor: ScriptId,
    prefix: Vec<NameId>,
    full: Option<Vec<NameId>>,
}

/// The rows and per-group folds collected before any key is assigned.
#[derive(Default)]
struct RowSet {
    folds: HashMap<GroupId, SlotFold>,
    ctor_rows: HashMap<GroupId, Vec<CtorRows>>,
    lit_rows: HashMap<GroupId, Vec<(Site, Vec<NameId>)>>,
    /// Constructors whose full row extends their prefix row.
    two_phase: HashSet<ScriptId>,
    /// Two-phase constructor -> the init delegates attributed to it.
    tp_delegs: HashMap<ScriptId, Vec<ScriptId>>,
    /// Constructor whose full row a post-construction fill sequence
    /// completes -> the fill sites (script, local, pc of the last add).
    local_fills: HashMap<ScriptId, Vec<(ScriptId, u32, Pc)>>,
    /// Delegation targets of the ctor-exit expansion, sorted: the scripts
    /// whose `this.f = v` stores are instance inits rather than method-body
    /// overwrites.
    apply_delegates: Vec<ScriptId>,
}

impl LayoutPlan {
    /// Run the whole layout analysis, filling the layout-shaped facts
    /// (`ctor_stamps`, `ctor_nslots`, `deleg_restamps`, `this_layouts`,
    /// `deleg_inits`, `construct_site_keys`) as it goes.
    fn build(sv: &Solver<'_>, facts: &mut LikelyFacts, deleg: &Delegation) -> LayoutPlan {
        let mut plan = LayoutPlan::default();
        for (ci, con) in sv.engine.cons.iter().enumerate() {
            use super::engine::{CKey, Constraint};
            if let Constraint::Move {
                dst: CKey::Arg(i), ..
            } = con
            {
                let sid = sv.engine.con_script[ci];
                plan.arg_reassigned.insert((sid, i.get()));
            }
        }
        for (&(sid, i), writes) in &sv.tables.arg_writes {
            let list = plan.arg_fill.entry((sid, i.get())).or_default();
            for &(name, pc) in writes {
                list.push((name, Site::new(sid, pc)));
            }
        }
        for (ci, con) in sv.engine.cons.iter().enumerate() {
            use super::engine::{CKey, Constraint};
            if let Constraint::Write { recv, name, pc, .. } = con {
                let site = Site::new(sv.engine.con_script[ci], *pc);
                let agreed = sv.site_recv_class.get(&site).and_then(Agreed::get);
                if let Some(&c) = agreed {
                    plan.class_writes.entry((c, *name)).or_default().push(site);
                }
                if *recv == CKey::This {
                    match agreed {
                        Some(&c) => {
                            plan.this_writes.entry(c).or_default().insert(*name);
                        }
                        None => {
                            plan.unplaced_writes.insert(*name);
                        }
                    }
                }
            }
        }
        let mut callee_read: HashMap<(ScriptId, VarId), Site> = HashMap::default();
        for (ci, con) in sv.engine.cons.iter().enumerate() {
            use super::engine::{CKey, Constraint};
            if let Constraint::Read {
                dst: CKey::Var(v),
                pc,
                callee_pos: true,
                ..
            } = con
            {
                let sid = sv.engine.con_script[ci];
                callee_read.insert((sid, *v), Site::new(sid, *pc));
            }
        }
        for (ci, con) in sv.engine.cons.iter().enumerate() {
            use super::engine::{CKey, Constraint};
            let Constraint::Call {
                callee: CKey::Var(v),
                this_: Some(_),
                pc,
                construct: false,
                ..
            } = con
            else {
                continue;
            };
            let sid = sv.engine.con_script[ci];
            let Some(&rsite) = callee_read.get(&(sid, *v)) else {
                continue;
            };
            let Some(&a) = sv.site_recv_class.get(&rsite).and_then(Agreed::get) else {
                continue;
            };
            let Some(fns) = sv.site_calls.get(&Site::new(sid, *pc)) else {
                continue;
            };
            if fns.is_multi() {
                continue;
            }
            for f in fns.ids() {
                let Some(t) = f.as_script() else { continue };
                let Some(&b) = sv.this_pin.get(&t).and_then(Agreed::get) else {
                    continue;
                };
                if b != a {
                    plan.class_aliases.entry(a).or_default().push(b);
                    plan.class_aliases.entry(b).or_default().push(a);
                }
            }
        }
        for (&(sid, _), writes) in &sv.tables.local_writes {
            for &(_, pc) in writes {
                plan.fill_sites.insert(Site::new(sid, pc));
            }
        }
        let rows = plan.collect_rows(sv, facts, deleg);
        let groups = ordered_groups(sv, &rows);
        plan.assign_keys(sv, facts, &rows, &groups);
        plan.add_shared_ctor_classes(sv, facts, deleg);
        plan.add_region_tables(sv);
        plan.add_post_new_rows(sv, facts, deleg);
        plan.emit_this_layouts(sv, facts, &rows);
        plan
    }

    /// Caller-side init-after-new: for each allocation site whose result
    /// takes post-allocation `SetProp`s (the scan's `post_order` channel),
    /// mint ONE extension row per site -- the site's base row (a shared
    /// construct site's proto-keyed row, else the resolved ctor's full
    /// row) extended by the site's own recorded order. The base is a
    /// proper prefix of every extension, so the globally-recomputed
    /// prefix relations turn the caller's adds into add-prediction pairs:
    /// SLOTS and the epoch survive them, PER SITE -- no cross-site join
    /// (different callers legitimately init different subsets in
    /// different orders) and no new stamping (the base key stays the
    /// stamped one).
    fn add_post_new_rows(&mut self, sv: &Solver<'_>, facts: &mut LikelyFacts, deleg: &Delegation) {
        let mut sites: Vec<(&Site, &Vec<NameId>)> = sv.tables.post_order.iter().collect();
        sites.sort_unstable_by_key(|(s, _)| **s);
        let mut seen: HashSet<(u32, Vec<NameId>)> = HashSet::default();
        for (site, order) in sites {
            if order.is_empty() {
                continue;
            }
            let base_key = if let Some(k) = facts.construct_site_keys.get(site) {
                k.get()
            } else if let Some(&ctor) = deleg.single_call_target.get(site) {
                match self.ctor_key.get(&ctor) {
                    Some(&(_, kf)) => kf,
                    None => continue,
                }
            } else {
                continue;
            };
            let Some(base) = self.rows.get(&base_key) else {
                continue;
            };
            let mut extended = base.names.clone();
            for &n in order {
                if !extended.contains(&n) && extended.len() < LAY_CAP {
                    extended.push(n);
                }
            }
            if extended.len() == self.rows[&base_key].names.len() {
                continue;
            }
            if !seen.insert((base_key, extended.clone())) {
                continue;
            }
            if self.next_key as usize >= LayoutKey::LIMIT as usize {
                self.caps.layout_keys += 1;
                break;
            }
            let class = self.key_class.get(&base_key).copied();
            self.add_row(sv, class, extended);
        }
    }

    /// Expand every constructed script and every object literal into its
    /// layout row, and fold each group's rows together.
    fn collect_rows(
        &mut self,
        sv: &Solver<'_>,
        facts: &mut LikelyFacts,
        deleg: &Delegation,
    ) -> RowSet {
        let mut rows = RowSet::default();
        // The ctor-exit row: `.call`/`.apply` delegates only, since a
        // `this.m(...)` init call has not happened yet at the point the
        // stamp goes in.
        let mut prefix_rows = CtorRowExpander::new(
            &sv.tables.this_events,
            &deleg.apply_targets,
            &deleg.single_call_target,
            false,
        );
        // The full row: `this.m(...)` init delegates spliced too. Its
        // participant attribution is kept separate so a non-two-phase
        // ctor's attribution is unaffected by this channel.
        let mut full_rows = CtorRowExpander::new(
            &sv.tables.this_events,
            &deleg.apply_targets,
            &deleg.single_call_target,
            true,
        );
        let mut constructed: Vec<ScriptId> = sv.constructed.iter().copied().collect();
        constructed.sort_unstable();
        for &f in &constructed {
            let prefix = prefix_rows.expand(f);
            if prefix.is_empty() {
                // Empty-prefix two-phase ctor -- an empty `function(){}`
                // whose fields are all installed by a separate init
                // delegate: there is no stampable ctor-exit prefix, but the
                // Full expansion still names the allocation size. Record
                // just the nslots, so construct sites allocate the full
                // layout and the delegate's field adds ride the fixed-slot
                // inline arms instead of the set-miss helper. No
                // layout/stamp rows are minted.
                let full = full_rows.expand(f);
                if !full.is_empty() && full.len() <= LAY_CAP {
                    facts
                        .ctor_nslots
                        .insert(f, u32::try_from(full.len()).unwrap());
                }
                continue;
            }
            let mut full = full_rows.expand(f);
            let mut is_two_phase = full.len() > prefix.len()
                && full.len() <= LAY_CAP
                && full[..prefix.len()] == prefix[..];
            if !is_two_phase {
                if let Some((row, fillers, adds)) = self.local_fill_row(sv, f, &prefix) {
                    full = row;
                    is_two_phase = true;
                    rows.local_fills.insert(f, fillers);
                    self.fill_add_sites.extend(adds);
                }
            }
            let g = match sv.class_lookup_fn(f) {
                Some(c) => sv.group_of_class(c),
                None => GroupId::of_ctor(f),
            };
            rows.folds.entry(g).or_default().add_row(&prefix);
            let full = if is_two_phase {
                rows.two_phase.insert(f);
                rows.folds.entry(g).or_default().add_row(&full);
                Some(full)
            } else {
                None
            };
            rows.ctor_rows.entry(g).or_default().push(CtorRows {
                ctor: f,
                prefix,
                full,
            });
        }
        // Literal sites: ordered init evidence on the site class; skip
        // literals that became prototype objects (method tables).
        let mut lit_sites: Vec<(Site, Vec<NameId>)> = sv
            .tables
            .lit_order
            .iter()
            .map(|(&s, r)| (s, r.clone()))
            .collect();
        lit_sites.sort_unstable_by_key(|(s, _)| *s);
        for (site, order) in lit_sites {
            if order.is_empty() {
                continue;
            }
            if order.len() > LAY_CAP {
                self.caps.layout_rows += 1;
                continue;
            }
            if sv.heap.site_is_proto.contains(&site) {
                continue;
            }
            if sv.heap.dyn_named_writes.contains(&site) {
                continue;
            }
            let Some(c) = sv.heap.class_id(ClassKey::Site(site)) else {
                continue;
            };
            let g = sv.group_of_class(c);
            rows.folds.entry(g).or_default().add_row(&order);
            rows.lit_rows.entry(g).or_default().push((site, order));
        }
        // Which script's `this` each layout is attributed to: the ctor
        // itself, a method homed to it, or a delegate that exactly one ctor
        // splices.
        self.narrow_this_attribution(sv, &rows, &prefix_rows, &full_rows);
        // Delegates of two-phase ctors, for the full-row mask lookup and
        // the deleg_restamps emission.
        for (d, c) in sole_participants(&full_rows.participants) {
            if rows.two_phase.contains(&c) && d != c {
                rows.tp_delegs.entry(c).or_default().push(d);
            }
        }
        rows.apply_delegates = super::sorted_keys(&prefix_rows.participants);
        self.caps.add(&prefix_rows.caps);
        self.caps.add(&full_rows.caps);
        rows
    }

    /// The post-construction fill row of constructor `f`'s class: the
    /// prefix extended by the names a straight-line add sequence on one
    /// local receiver of the agreed class writes after construction
    /// (box2d's `ccp = c.points[j]; ccp.normalImpulse = ...`). Writes
    /// preceded by a read of the name off the same slot are overwrites and
    /// do not count; every remaining run in the program must be a prefix
    /// of the longest one (a partial fill on another path keeps the shape
    /// order; a run in another order refuses the class), and the longest
    /// becomes the row. The runs completing it restamp after their last
    /// add. The stamp's runtime gates (ownership, slot span, the
    /// add-prediction bits) refuse an instance filled any other way.
    fn local_fill_row(
        &self,
        sv: &Solver<'_>,
        f: ScriptId,
        prefix: &[NameId],
    ) -> Option<(Vec<NameId>, Vec<(ScriptId, u32, Pc)>, Vec<Site>)> {
        let class = sv.class_lookup_fn(f)?;
        if prefix.is_empty() {
            return None;
        }
        if sv.opts.diagnostics.propgap {
            crate::diag_line!(
                "night: fillrow ctor {} class {} prefix [{}]",
                f.get(),
                class.0,
                prefix
                    .iter()
                    .map(|&n| String::from_utf16_lossy(sv.names.get(n)))
                    .collect::<Vec<_>>()
                    .join(",")
            );
        }
        let mut keys: Vec<(ScriptId, u32)> = sv.tables.local_writes.keys().copied().collect();
        keys.sort_unstable();
        // One candidate per straight-line run of writes: a run ends at a
        // control pc or a rebind of the local between two writes, so the
        // arms of a branch never merge into one order.
        let mut cands: Vec<(Vec<NameId>, ScriptId, u32, Pc)> = Vec::new();
        let mut adds: Vec<Site> = Vec::new();
        for (s, l) in keys {
            match sv.source.object(s.source()) {
                crate::source::SourceObject::Script(sc)
                    if !sc.has_mapped_args && !sc.is_generator_or_async => {}
                _ => continue,
            }
            let control = sv.tables.control_pcs.get(&s);
            let sets = sv.tables.local_sets.get(&(s, l));
            let reads = sv.tables.local_reads.get(&(s, l));
            // A write preceded by a read of the same name off the same
            // slot, with no rebind between, overwrites a field the object
            // already has.
            let overwrites = |n: NameId, pc: Pc| {
                reads.is_some_and(|rs| {
                    rs.iter().any(|&(rn, rpc)| {
                        rn == n
                            && rpc < pc
                            && !sets.is_some_and(|v| v.iter().any(|&p| p > rpc && p < pc))
                    })
                })
            };
            if sv.opts.diagnostics.propgap
                && sv.tables.local_writes[&(s, l)].iter().any(|&(_, pc)| {
                    sv.site_recv_class
                        .get(&Site::new(s, pc))
                        .and_then(Agreed::get)
                        == Some(&class)
                })
            {
                let ws: Vec<String> = sv.tables.local_writes[&(s, l)]
                    .iter()
                    .map(|&(n, pc)| {
                        format!(
                            "{}@{}:{}",
                            String::from_utf16_lossy(sv.names.get(n)),
                            pc,
                            match sv.site_recv_class.get(&Site::new(s, pc)) {
                                Some(Agreed::One(c)) => c.0.to_string(),
                                Some(Agreed::Conflict) => "X".to_string(),
                                _ => "-".to_string(),
                            }
                        )
                    })
                    .collect();
                crate::diag_line!(
                    "night: fillrow writes class {} {}:l{} [{}]",
                    class.0,
                    s.get(),
                    l,
                    ws.join(" ")
                );
            }
            let breaks = |a: Pc, b: Pc| {
                [control, sets]
                    .iter()
                    .any(|v| v.is_some_and(|v| v.iter().any(|&p| p > a && p < b)))
            };
            let mut run: Vec<NameId> = Vec::new();
            let mut run_first = Pc::new(0);
            let mut run_last = Pc::new(0);
            let mut prev: Option<Pc> = None;
            let mut run_adds: Vec<Site> = Vec::new();
            let close = |run: &mut Vec<NameId>,
                         run_adds: &mut Vec<Site>,
                         first: Pc,
                         last: Pc,
                         cands: &mut Vec<(Vec<NameId>, ScriptId, u32, Pc)>,
                         adds: &mut Vec<Site>| {
                if run.is_empty() {
                    return;
                }
                cands.push((std::mem::take(run), s, l, last));
                adds.append(run_adds);
                if let Some(rs) = reads {
                    adds.extend(
                        rs.iter()
                            .filter(|&&(_, rpc)| rpc > first && rpc < last)
                            .map(|&(_, rpc)| Site::new(s, rpc)),
                    );
                }
            };
            for &(n, pc) in &sv.tables.local_writes[&(s, l)] {
                if prev.is_some_and(|q| breaks(q, pc)) {
                    close(
                        &mut run,
                        &mut run_adds,
                        run_first,
                        run_last,
                        &mut cands,
                        &mut adds,
                    );
                }
                prev = Some(pc);
                if sv
                    .site_recv_class
                    .get(&Site::new(s, pc))
                    .and_then(Agreed::get)
                    != Some(&class)
                {
                    continue;
                }
                if prefix.contains(&n) || run.contains(&n) || overwrites(n, pc) {
                    continue;
                }
                if run.is_empty() {
                    run_first = pc;
                }
                run.push(n);
                run_last = pc;
                run_adds.push(Site::new(s, pc));
            }
            close(
                &mut run,
                &mut run_adds,
                run_first,
                run_last,
                &mut cands,
                &mut adds,
            );
        }
        cands.retain(|c| prefix.len() + c.0.len() <= LAY_CAP);
        let longest = cands.iter().map(|c| &c.0).max_by_key(|s| s.len())?.clone();
        let ordered = |a: &[NameId]| longest.starts_with(a);
        let names = |ns: &[NameId]| {
            ns.iter()
                .map(|&n| String::from_utf16_lossy(sv.names.get(n)))
                .collect::<Vec<_>>()
                .join(",")
        };
        if sv.opts.diagnostics.propgap {
            for c in &cands {
                crate::diag_line!(
                    "night: fillrow class {} run {}:{} l{} [{}]{}",
                    class.0,
                    c.1.get(),
                    c.3,
                    c.2,
                    names(&c.0),
                    if ordered(&c.0) { "" } else { " REFUSES" }
                );
            }
        }
        if !cands.iter().all(|c| ordered(&c.0)) {
            return None;
        }
        let aliased = |n: NameId| {
            self.class_aliases.get(&class).is_some_and(|bs| {
                bs.iter()
                    .any(|b| self.this_writes.get(b).is_some_and(|ns| ns.contains(&n)))
            })
        };
        let outside = longest.iter().find(|&&n| {
            aliased(n)
                || self
                    .class_writes
                    .get(&(class, n))
                    .is_some_and(|sites| sites.iter().any(|s| !self.fill_sites.contains(s)))
        });
        if let Some(&n) = outside {
            if sv.opts.diagnostics.propgap {
                crate::diag_line!(
                    "night: fillrow class {} REFUSES: {} is written outside the channel ({})",
                    class.0,
                    String::from_utf16_lossy(sv.names.get(n)),
                    if self.unplaced_writes.contains(&n) {
                        "unresolved this"
                    } else if aliased(n) {
                        "an alias class's this"
                    } else {
                        "agreed site"
                    }
                );
            }
            return None;
        }
        let fillers = cands
            .iter()
            .filter(|c| c.0 == longest)
            .map(|c| (c.1, c.2, c.3))
            .collect();
        let mut row = prefix.to_vec();
        row.extend(longest);
        Some((row, fillers, adds))
    }

    /// Fill `narrow`: the constructor each script's `this` belongs to.
    fn narrow_this_attribution(
        &mut self,
        sv: &Solver<'_>,
        rows: &RowSet,
        prefix_rows: &CtorRowExpander<'_>,
        full_rows: &CtorRowExpander<'_>,
    ) {
        let mut ctor_set: HashSet<ScriptId> = HashSet::default();
        for group in rows.ctor_rows.values() {
            for r in group {
                ctor_set.insert(r.ctor);
                self.narrow.insert(r.ctor, r.ctor);
            }
        }
        let mut mh: Vec<(ScriptId, Option<ScriptId>)> = sv
            .heap
            .method_home
            .iter()
            .map(|(&m, c)| (m, c.value()))
            .collect();
        mh.sort_unstable();
        for (m, c) in mh {
            if let Some(c) = c {
                if ctor_set.contains(&c) {
                    self.narrow.entry(m).or_insert(c);
                }
            }
        }
        for (d, c) in sole_participants(&prefix_rows.participants) {
            if ctor_set.contains(&c) {
                self.narrow.entry(d).or_insert(c);
            }
        }
        // Two-phase init delegates (`this.m(...)` splices) narrow to
        // their sole splicing ctor like apply delegates -- but only for
        // Two-phase ctors, so everything else keeps its attribution
        // unchanged.
        for (d, c) in sole_participants(&full_rows.participants) {
            if rows.two_phase.contains(&c) {
                self.narrow.entry(d).or_insert(c);
            }
        }
    }

    /// Assign the dense layout keys, in `groups` order, and build the
    /// per-group universal prefix tables.
    fn assign_keys(
        &mut self,
        sv: &Solver<'_>,
        facts: &mut LikelyFacts,
        rows: &RowSet,
        groups: &[GroupId],
    ) {
        for &root in groups {
            let lo = self.next_key;
            let rows_needed = rows.ctor_rows.get(&root).map_or(0, |r| {
                r.iter().map(|e| 1 + usize::from(e.full.is_some())).sum()
            }) + rows.lit_rows.get(&root).map_or(0, |r| r.len());
            if self.next_key as usize + rows_needed >= LayoutKey::LIMIT as usize {
                self.caps.layout_keys += 1;
                continue;
            }
            let mut ctor_rows: Vec<&CtorRows> =
                rows.ctor_rows.get(&root).into_iter().flatten().collect();
            ctor_rows.sort_by(|x, y| x.prefix.cmp(&y.prefix).then(x.ctor.cmp(&y.ctor)));
            let mut lit_rows: Vec<&(Site, Vec<NameId>)> =
                rows.lit_rows.get(&root).into_iter().flatten().collect();
            lit_rows.sort_by(|x, y| x.1.cmp(&y.1).then(x.0.cmp(&y.0)));
            for cr in ctor_rows {
                self.assign_ctor_key(sv, facts, rows, cr, lo);
            }
            for (site, row) in lit_rows {
                self.assign_lit_key(sv, facts, *site, row.clone());
            }
            let hi = self.next_key.wrapping_sub(1);
            if self.next_key == lo {
                continue;
            }
            self.group_range.insert(root, (lo, hi));
            let ptable = rows.folds[&root].universal_prefix();
            if !ptable.is_empty() && hi > lo {
                let pmasks = prefix_masks(&self.rows, &ptable, lo, hi);
                self.group_tables.insert(lo, (ptable, pmasks));
            }
        }
        // Layout key -> ClassId, for the two places that need to ask a
        // *key* what its class's view cell says: the per-site
        // type-dimension mask (which unions the member classes' claims
        // across a key range) and the typed-tier layout claims.
        for (&f, &(kp, kf)) in &self.ctor_key {
            if let Some(c) = sv.class_lookup_fn(f) {
                self.key_class.insert(kp, c);
                self.key_class.insert(kf, c);
            }
        }
    }

    /// Mint the key (or the adjacent key pair) of one constructor's row.
    fn assign_ctor_key(
        &mut self,
        sv: &Solver<'_>,
        facts: &mut LikelyFacts,
        rows: &RowSet,
        cr: &CtorRows,
        group_lo: u32,
    ) {
        let f = cr.ctor;
        // The stamped mask of a name under ctor `f` is read off the class
        // view cell -- the estimate over the field's whole lifetime, not
        // just the ctor's own writes.
        let class = sv.class_lookup_fn(f);
        let key = self.add_row(sv, class, cr.prefix.clone());
        facts.ctor_stamps.insert(f, LayoutKey::new(key));
        facts.ctor_nslots.insert(
            f,
            u32::try_from(cr.full.as_ref().map_or(cr.prefix.len(), Vec::len)).unwrap(),
        );
        let Some(frow) = cr.full.as_ref() else {
            self.ctor_key.insert(f, (key, key));
            return;
        };
        let kf = self.add_row(sv, class, frow.clone());
        self.ctor_key.insert(f, (key, kf));
        for &(s, l, pc) in rows.local_fills.get(&f).into_iter().flatten() {
            facts
                .local_restamps
                .insert(Site::new(s, pc), (l, LayoutKey::new(kf)));
        }
        // Pair prefix table (all-members masks over the pair), for method
        // homes when the pair does not start its group (the group's own
        // table then keys elsewhere).
        if key != group_lo {
            let pmasks: Vec<Prims> = self.rows[&key]
                .masks
                .iter()
                .zip(&self.rows[&kf].masks)
                .map(|(&a, &b)| {
                    if a != Prims::EMPTY && b != Prims::EMPTY {
                        a | b
                    } else {
                        Prims::EMPTY
                    }
                })
                .collect();
            self.group_tables
                .insert(key, (self.rows[&key].names.clone(), pmasks));
        }
        // Re-stamp tails only on delegates whose own direct writes
        // contribute a suffix name (the row-completing scripts);
        // transitively-reached delegates that write nothing on `this` would
        // pay the tail on every hot return for no stamp.
        let suffix = &frow[self.names(key).len()..];
        for &d in rows.tp_delegs.get(&f).into_iter().flatten() {
            let completes = sv.tables.this_events.get(&d).is_some_and(|evs| {
                evs.iter()
                    .any(|e| matches!(e, TEvent::Write(n) if suffix.contains(n)))
            });
            if completes {
                facts.deleg_restamps.entry(d).or_insert(LayoutKey::new(kf));
            }
        }
        // The formal-receiver siblings of the delegate rule: fill scripts
        // completing the WHOLE suffix through one formal whose write sites
        // agree on this ctor's class (the fresh-object-then-fill idiom --
        // `nbi()` handing the result to `multiplyTo(a, r)`). Each return
        // re-stamps the formal's object under the same validated-shape
        // gates, so an unfilled early-return receiver just refuses. The
        // whole-suffix requirement keeps the per-return tail off scripts
        // whose stamp could never pass the span gate.
        if !suffix.is_empty() {
            if let Some(class) = class {
                let mut cands: Vec<(ScriptId, u32)> = Vec::new();
                for (&(s, i), writes) in &self.arg_fill {
                    if s == f
                        || self.arg_reassigned.contains(&(s, i))
                        || facts.deleg_restamps.contains_key(&s)
                    {
                        continue;
                    }
                    match sv.source.object(s.source()) {
                        crate::source::SourceObject::Script(sc)
                            if !sc.has_mapped_args && !sc.is_generator_or_async => {}
                        _ => continue,
                    }
                    let covered = suffix.iter().all(|n| {
                        writes.iter().any(|(wn, site)| {
                            wn == n
                                && sv
                                    .site_recv_class
                                    .get(site)
                                    .and_then(super::types::Agreed::get)
                                    == Some(&class)
                        })
                    });
                    if covered {
                        cands.push((s, i));
                    }
                }
                cands.sort_unstable();
                for (s, i) in cands {
                    facts
                        .arg_restamps
                        .entry(s)
                        .or_insert((i, LayoutKey::new(kf)));
                }
            }
        }
    }

    /// Mint the key of one object-literal site's row. The joined read
    /// evidence has no per-class cell here, so the masks come from the site
    /// class's view cell directly.
    fn assign_lit_key(
        &mut self,
        sv: &Solver<'_>,
        facts: &mut LikelyFacts,
        site: Site,
        row: Vec<NameId>,
    ) {
        let class = sv.heap.class_id(ClassKey::Site(site));
        let key = self.add_row(sv, class, row);
        facts.lit_stamps.insert(site, LayoutKey::new(key));
    }

    /// Region ranges and tables (the fenced hierarchy's middle rung): a
    /// region with two or more keyed groups spans their key ranges --
    /// contiguous by the ordering `assign_keys` used -- and its table is
    /// the fold over every member row, masks by the all-members rule.
    fn add_region_tables(&mut self, sv: &Solver<'_>) {
        // Every keyed group, not the ordered row list: shared-generated-ctor
        // classes (the prototype.js `Class.create()` idiom) key their own
        // single-key groups in `add_shared_ctor_classes`, which runs first
        // -- built from the row list alone, a region whose members are all
        // such classes had no range at all and every region-typed site
        // resolved against nothing.
        let mut region_groups: HashMap<ClassId, Vec<GroupId>> = HashMap::default();
        for &g in self.group_range.keys() {
            if let Some(c) = sv.class_of_group(g) {
                region_groups
                    .entry(sv.engine.region_root(c))
                    .or_default()
                    .push(g);
            }
        }
        for (&r, groups) in &region_groups {
            if groups.len() < 2 {
                continue;
            }
            // A region fact's range guard tests the stamped header key, so
            // some key in range must actually get stamped: ctor instances
            // stamp at the ctor's exit, shared-ctor classes restamp at
            // their init delegate's returns. A range holding only lit keys
            // can never hit, so every read through it pays the miss for
            // nothing.
            if !groups
                .iter()
                .any(|g| g.is_ctor() || self.stamped_class_groups.contains(g))
            {
                continue;
            }
            let lo = groups.iter().map(|g| self.group_range[g].0).min().unwrap();
            let hi = groups.iter().map(|g| self.group_range[g].1).max().unwrap();
            self.region_range.insert(r, (lo, hi));
            // The spanning range may interleave keys of groups outside the
            // region, and the emitted guard admits any key in it -- so the
            // prefix folds every key in the span, member or not.
            let mut fold = SlotFold::default();
            for k in lo..=hi {
                let row = self.names(k).to_vec();
                fold.add_row(&row);
            }
            let ptable = fold.universal_prefix();
            if ptable.is_empty() {
                continue;
            }
            let pmasks = prefix_masks(&self.rows, &ptable, lo, hi);
            self.region_tables.insert(r, (ptable, pmasks));
        }
    }

    /// Shared-generated-ctor classes (the prototype.js `Class.create()`
    /// idiom): the pre-solve concrete resolution (`resolve_shared_ctor_sites`)
    /// mapped each construct site to (ctor script, prototype object,
    /// init-delegate script) and the model already ran with the
    /// per-prototype classes. Here each distinct prototype mints a layout
    /// key whose row is the init delegate's expansion; the delegate rides
    /// the existing deleg_restamps/deleg_inits/this_layouts rails (static
    /// add checks + full-key restamp at its returns), and
    /// `construct_site_keys` seeds the keyed alloc word per site.
    fn add_shared_ctor_classes(
        &mut self,
        sv: &Solver<'_>,
        facts: &mut LikelyFacts,
        deleg: &Delegation,
    ) {
        use crate::source::{ObjectData, SourceObject, SourceObjectId};
        let mut sites: Vec<(Site, &SharedCtorSite)> =
            sv.shared_ctor_sites.iter().map(|(&s, v)| (s, v)).collect();
        sites.sort_unstable_by_key(|(s, _)| *s);
        // Per distinct prototype object: the minted layout key.
        let mut proto_key: HashMap<SourceObjectId, u32> = HashMap::default();
        // Method home candidates: member script -> the keys claiming it.
        let mut method_homes: HashMap<ScriptId, Vec<u32>> = HashMap::default();
        for (site, shared) in sites {
            let (f, proto, init_sid) = (shared.ctor, shared.proto, shared.init);
            if self.next_key as usize >= LayoutKey::LIMIT as usize {
                self.caps.layout_keys += 1;
                break;
            }
            // A ctor the script-keyed machinery already rows (the
            // single-class apply-delegate idiom) keeps that path whole:
            // minting a second proto-keyed key for the same class makes the
            // alloc-seeded and delegate-restamped ids fight, and the two
            // then disagree about which slots the object has.
            if facts.ctor_stamps.contains_key(&f) {
                continue;
            }
            let key = match proto_key.get(&proto) {
                Some(&k) => k,
                None => {
                    if facts.ctor_stamps.contains_key(&init_sid)
                        || facts.deleg_restamps.contains_key(&init_sid)
                    {
                        continue;
                    }
                    let mut expander = CtorRowExpander::new(
                        &sv.tables.this_events,
                        &deleg.apply_targets,
                        &deleg.single_call_target,
                        true,
                    );
                    let row = expander.expand(init_sid);
                    self.caps.add(&expander.caps);
                    if row.is_empty() {
                        continue;
                    }
                    if row.len() > LAY_CAP {
                        self.caps.layout_rows += 1;
                        continue;
                    }
                    // Masks from the per-prototype class view (the model
                    // ran with these classes, so the views are
                    // class-precise).
                    let pcl = sv.heap.class_id(ClassKey::Proto(proto));
                    let key = self.add_row(sv, pcl, row);
                    // The class keys its own group (ctor: None, the
                    // lit-class rule), so registering the exact key range
                    // here is what lets the per-site emission resolve
                    // receivers of this class.
                    if let Some(c) = pcl {
                        self.group_range.insert(GroupId::of_class(c), (key, key));
                        self.key_class.insert(key, c);
                        self.stamped_class_groups.insert(GroupId::of_class(c));
                    }
                    // Scripted members of the prototype (the class's
                    // methods) are this-home candidates.
                    if let SourceObject::Object(ObjectData { properties, .. }) =
                        sv.source.object(proto)
                    {
                        for (_, v) in properties {
                            if let Some(m) = sv.source.fn_script(*v) {
                                method_homes.entry(m).or_default().push(key);
                            }
                        }
                    }
                    facts.deleg_restamps.insert(init_sid, LayoutKey::new(key));
                    facts
                        .this_layouts
                        .entry(init_sid)
                        .or_insert((LayoutKey::new(key), LayoutKey::new(key)));
                    proto_key.insert(proto, key);
                    key
                }
            };
            facts.construct_site_keys.insert(site, LayoutKey::new(key));
        }
        // Method this-homes: only members claimed by exactly one class and
        // not already homed.
        for (m, keys) in {
            let mut v: Vec<_> = method_homes.into_iter().collect();
            v.sort_unstable();
            v
        } {
            if let [k] = keys.as_slice() {
                if !facts.ctor_stamps.contains_key(&m) {
                    facts
                        .this_layouts
                        .entry(m)
                        .or_insert((LayoutKey::new(*k), LayoutKey::new(*k)));
                }
            }
        }
    }

    /// Per-method this-layouts: for each script that is not itself a
    /// constructor, the layout key (or key range) its `this` is predicted
    /// to carry. The lowering consumes this at method entry --
    /// `wasm::bbv::facts` primes the shape/generation cell from it, and
    /// `wasm::bbv::property` serves fixed-slot reads off `this` against it
    /// without a per-site class check. Two keys because a two-phase
    /// constructor stamps a prefix key at its own exit and the full key at
    /// its init delegate's, so a method that may see either guards the
    /// range.
    fn emit_this_layouts(&self, sv: &Solver<'_>, facts: &mut LikelyFacts, rows: &RowSet) {
        for m in super::sorted_keys(&sv.engine.script_cons) {
            if facts.ctor_stamps.contains_key(&m) {
                continue;
            }
            if let Some(&c) = self.narrow.get(&m) {
                if let Some(&(kp, kf)) = self.ctor_key.get(&c) {
                    facts
                        .this_layouts
                        .insert(m, (LayoutKey::new(kp), LayoutKey::new(kf)));
                    continue;
                }
            }
            let Some(c) = sv.script_this_class(m) else {
                continue;
            };
            let Some((lo, hi)) = self.range_of(sv.group_of_class(c)) else {
                continue;
            };
            if lo == hi {
                facts
                    .this_layouts
                    .insert(m, (LayoutKey::new(lo), LayoutKey::new(lo)));
            } else if self.group_tables.contains_key(&lo) {
                facts
                    .this_layouts
                    .insert(m, (LayoutKey::new(lo), LayoutKey::new(hi)));
            }
        }
        // Delegates whose `this.f = v` stores are instance inits rather
        // than method-body overwrites: the layout-set slow tail carries the
        // add-transition arm there, and only there (it is pure bloat on a
        // method-overwrite tail). Both delegation channels qualify, and a
        // script that is itself a stamped ctor does not.
        for &p in &rows.apply_delegates {
            if !facts.ctor_stamps.contains_key(&p) {
                facts.deleg_inits.insert(p);
            }
        }
        for p in super::sorted_keys(&facts.deleg_restamps) {
            if !facts.ctor_stamps.contains_key(&p) {
                facts.deleg_inits.insert(p);
            }
        }
    }

    pub(super) fn range_of(&self, g: GroupId) -> Option<(u32, u32)> {
        self.group_range.get(&g).copied()
    }

    fn name_mask(&self, key: u32, name: NameId) -> Prims {
        name_mask(&self.rows, key, name)
    }

    /// The field names of a layout row, or nothing if the key has none.
    fn names(&self, key: u32) -> &[NameId] {
        self.rows.get(&key).map_or(&[], |r| &r.names)
    }

    /// Mint a key for `names`, reading each position's claim and range off
    /// `class`'s view cells. The one place a layout row is created, so the
    /// one place the mask/range pairing has to hold.
    fn add_row(&mut self, sv: &Solver<'_>, class: Option<ClassId>, names: Vec<NameId>) -> u32 {
        let key = self.next_key;
        self.next_key += 1;
        let masks: Vec<Prims> = names
            .iter()
            .map(|n| {
                class
                    .and_then(|c| sv.class_view_prims(c, *n))
                    .unwrap_or(Prims::EMPTY)
            })
            .collect();
        let ranges = pair_ranges(
            &masks,
            names
                .iter()
                .map(|n| class.and_then(|c| sv.class_view_range(c, *n)))
                .collect(),
        );
        self.rows.insert(
            key,
            LayoutRowFacts {
                names,
                masks,
                ranges,
            },
        );
        key
    }

    /// `name`'s position in a universal prefix table over `lo..=hi`, with
    /// the claim that position makes. `masks` is the table's own mask row
    /// where it has one (a group or region table) and `None` for an exact
    /// single-key row, where the layout's own mask answers.
    fn table_slot_fact(
        &self,
        lo: u32,
        hi: u32,
        table: &[NameId],
        masks: Option<&[Prims]>,
        name: NameId,
    ) -> Option<SlotFact> {
        let pos = table.iter().position(|n| *n == name)?;
        let slot = SlotIndex::new(u32::try_from(pos).unwrap());
        let prims = match masks {
            Some(ms) => ms.get(pos).copied().unwrap_or(Prims::EMPTY),
            None => self.name_mask(lo, name),
        };
        // A single-key run claims uniformly by definition; over a range,
        // either the table claims for everybody or nobody may.
        let uniform = lo == hi
            || !prims.is_empty()
            || (lo..=hi).all(|k| self.name_mask(k, name) == Prims::EMPTY);
        Some(SlotFact {
            lo,
            hi,
            slot,
            prims,
            uniform,
        })
    }

    /// The longest run of adjacent keys in `glo..=ghi` that all place
    /// `name` at the same slot, with the claim over that run.
    ///
    /// A group's universal prefix table only covers names every member
    /// agrees on; this is the fallback for a name only part of the group
    /// carries, and it narrows the fact's range guard to exactly the keys
    /// that agree. `uniform` says whether every key in the run claims (so a
    /// store site may maintain the claim) or none does.
    fn subrange_in(&self, glo: u32, ghi: u32, name: NameId) -> Option<SlotFact> {
        if glo == ghi {
            return None;
        }
        let mut best: Option<(u32, u32, SlotIndex)> = None;
        let mut run: Option<(u32, SlotIndex)> = None;
        for k in glo..=ghi {
            let pos = self
                .names(k)
                .iter()
                .position(|n| *n == name)
                .map(|p| SlotIndex::new(u32::try_from(p).unwrap()));
            match (pos, run) {
                (Some(s), Some((rl, rs))) if s == rs => {
                    let len = k - rl + 1;
                    if best.is_none_or(|(bl, bh, _)| len > bh - bl + 1) {
                        best = Some((rl, k, s));
                    }
                }
                (Some(s), _) => {
                    run = Some((k, s));
                    if best.is_none() {
                        best = Some((k, k, s));
                    }
                }
                (None, _) => {
                    run = None;
                }
            }
        }
        let (lo, hi, slot) = best?;
        // A run that leaves out group members which ALSO carry the name
        // is a coin flip: a receiver of any excluded member misses the
        // guard on every execution (a run that omits a group member which
        // carries the name at a different slot leaves that member
        // permanently unstamped for it). No fact beats a wrong one: the
        // site takes the IC, which serves every member.
        let conflict = (glo..=ghi)
            .filter(|k| *k < lo || *k > hi)
            .any(|k| self.names(k).contains(&name));
        if conflict {
            return None;
        }
        let mut bits = Prims::EMPTY;
        let mut claimed = 0u32;
        for k in lo..=hi {
            let m = self
                .rows
                .get(&k)
                .and_then(|r| r.masks.get(slot.get() as usize))
                .copied()
                .unwrap_or(Prims::EMPTY);
            if m != Prims::EMPTY {
                claimed += 1;
            }
            bits |= m;
        }
        let n = hi - lo + 1;
        let all_claim = claimed == n;
        Some(SlotFact {
            lo,
            hi,
            slot,
            prims: if all_claim { bits } else { Prims::EMPTY },
            uniform: all_claim || claimed == 0,
        })
    }
}

/// A range row is meaningful only where the mask row claims: pair them at
/// every insertion so the two can never drift apart.
///
/// Narrowed further to INT32-only masks. The store-side check that
/// maintains a range is then two compares on the int32 payload, licensed by
/// the tag check the mask arm already emits; an int|double field would need
/// the same bounds tested in f64 as well, which buys nothing on the
/// populations this targets (integer digit arrays and plain int fields).
fn pair_ranges(masks: &[Prims], ranges: Vec<Option<ValueRange>>) -> Vec<Option<ValueRange>> {
    masks
        .iter()
        .zip(ranges)
        .map(|(&m, r)| {
            if m == Prims::from_bits(PRIM_INT32.bits()) {
                r
            } else {
                None
            }
        })
        .collect()
}

/// The slot half of a property fact: which keys agree, where the field
/// sits in them, and what the position claims.
#[derive(Clone, Copy)]
struct SlotFact {
    lo: u32,
    hi: u32,
    slot: SlotIndex,
    prims: Prims,
    /// Whether every key in the run claims, or none does. A read may take
    /// the fact either way; a write may only maintain a claim the whole
    /// run makes, since it cannot know which key its receiver carries.
    uniform: bool,
}

/// A write site's name-keyed typed mask, held back until every read site
/// has been seen: the mask upgrades the store fence, which is pure cost
/// unless some typed read actually consumes the position it covers.
struct PendingTypedWrite {
    site: Site,
    row: (LayoutKey, LayoutKey, Claim),
    /// The layout slot the site's prop fact settled on, when its key range
    /// matches the typed row's -- only then can a read consume, or a write
    /// maintain, the position.
    slot: Option<SlotIndex>,
}

/// The delegation edges the layout analysis walks through. Analysis-
/// internal: codegen keys on `apply_sites` rather than a resolved apply
/// target, since the forward helper reads the real one off the stack.
struct Delegation {
    /// The single resolved `.call`/`.apply` target per site. The form it
    /// spells is not carried: codegen reads that off `apply_sites`, and
    /// the layout walk only needs to know where the delegation goes.
    apply_targets: HashMap<Site, ScriptId>,
    /// The single scripted callee per ordinary call site: what a
    /// `this.m(...)` init delegate resolves through.
    single_call_target: HashMap<Site, ScriptId>,
}

/// What `emit_site_facts` learned that the phases after it need.
#[derive(Default)]
struct SiteFactTotals {
    /// (key, slot) positions some typed read site actually consumes.
    typed_read_positions: HashSet<(LayoutKey, SlotIndex)>,
    /// Element read sites an array claim could fold at.
    array_fold_reads: u32,
    /// Element write sites whose receiver did not resolve to one array
    /// population, and which therefore owe the maintenance duty
    /// unconditionally.
    array_unresolved_writes: u32,
}

impl Solver<'_> {
    /// Non-minting class lookup for a ctor script.
    fn class_lookup_fn(&self, f: ScriptId) -> Option<ClassId> {
        let key = match self.heap.script_proto.get(&f) {
            Some(&p) => ClassKey::Proto(p),
            None => ClassKey::Script(f),
        };
        self.heap.class_id(key)
    }

    /// The predictor group a class belongs to.
    pub(super) fn group_of_class(&self, c: ClassId) -> GroupId {
        match self.heap[c].ctor {
            Some(f) => GroupId::of_ctor(f),
            None => GroupId::of_class(c),
        }
    }

    /// The class a group speaks for, if it has one.
    fn class_of_group(&self, g: GroupId) -> Option<ClassId> {
        match g.ctor() {
            Some(f) => self.class_lookup_fn(f),
            None => g.class(),
        }
    }

    pub(super) fn emit(&mut self) -> LikelyFacts {
        let mut facts = LikelyFacts::default();
        let mut caps = CapDrops::default();
        self.emit_value_claims(&mut facts);
        let deleg = self.emit_call_sites(&mut facts, &mut caps);
        // The analysis half of the speculation trace (see `viz`).
        if let Some(mut out) = super::viz::stream(self.opts) {
            super::viz::write_arg_types(self, &mut out);
            super::viz::write_gname_cells(self, &self.names, &mut out);
            super::viz::write_field_cells(self, &self.names, &mut out);
            super::viz::write_regions(self, &mut out);
            super::viz::write_arith_dsts(self, &mut out);
        }
        let plan = LayoutPlan::build(self, &mut facts, &deleg);
        caps.add(&plan.caps);
        let totals = self.emit_site_facts(&mut facts, &plan);
        self.emit_arg_cls(&mut facts, &plan);
        self.emit_class_rows(&mut facts, &plan, &totals.typed_read_positions);
        self.emit_array_claims(&mut facts, &totals);
        super::effects::emit_effect_summaries(self, &mut facts, &plan);
        facts.n_classes = self.heap.classes.len();
        facts.n_cons = self.engine.cons.len();
        // Drops the fixpoint recorded but never reported, plus everything
        // the emission phase refused.
        caps.add(&self.tables.caps);
        caps.fn_set = u64::try_from(self.engine.sink.dropped_fns.len()).unwrap();
        caps.snap_absorb = u64::try_from(self.engine.sink.snap_absorbs.len()).unwrap();
        self.stats.caps.add(&caps);
        facts
    }

    // --- family 1: value claims ------------------------------------------

    /// The dataflow facts: what a value at a program point is likely to be.
    /// Three producers, all the same shape -- take a cell, join it over the
    /// contexts its script was live at, and run the result through a claim
    /// tier.
    /// Per-formal VALUE class, the advisory sibling of the `arg_types`
    /// claims: the arg cell's obj half joined over live ctxs, mapped
    /// through the plan's key ranges exactly like the per-site value
    /// classes. Post-plan (the mapping needs the key space); regions
    /// accepted.
    fn emit_arg_cls(&self, facts: &mut LikelyFacts, plan: &LayoutPlan) {
        use super::engine::CellKey;
        use super::heap::RegionLabels;
        for (&sid, ctxs) in &self.engine.live_ctxs {
            for i in 1..=MAX_TRACKED_FORMALS {
                let mk = |ctx| CellKey::Arg {
                    script: sid,
                    arg: FormalIndex::new(i - 1),
                    ctx,
                };
                let Some(j) = self.engine.join_over_ctxs(ctxs, mk) else {
                    continue;
                };
                let Some(Some(vc)) = self.recv_class(j.obj, j.unknown, RegionLabels::Accept) else {
                    continue;
                };
                let range = if self.engine.region_root(vc) == vc
                    && self
                        .engine
                        .region_members
                        .get(&vc)
                        .is_some_and(|ms| ms.len() > 1)
                {
                    plan.region_range.get(&vc).copied()
                } else {
                    plan.range_of(self.group_of_class(vc))
                };
                if let Some((lo, hi)) = range {
                    facts.arg_cls.insert(
                        (sid, ArgIndex::new(i)),
                        (LayoutKey::new(lo), LayoutKey::new(hi)),
                    );
                }
            }
        }
    }

    fn emit_value_claims(&self, facts: &mut LikelyFacts) {
        use super::engine::{CKey, CellKey, Constraint};
        // Per-script this/arg claims (the guard-at-defs family), projected
        // to either a purely-numeric mask or the object-only claim. Mixed
        // prim/object evidence and unresolved evidence emit nothing.
        for (&sid, ctxs) in &self.engine.live_ctxs {
            for i in 0..=MAX_TRACKED_FORMALS {
                let mk = |ctx| {
                    if i == 0 {
                        CellKey::This { script: sid, ctx }
                    } else {
                        CellKey::Arg {
                            script: sid,
                            arg: FormalIndex::new(i - 1),
                            ctx,
                        }
                    }
                };
                let Some(j) = self.engine.join_over_ctxs(ctxs, mk) else {
                    continue;
                };
                let Some(claim) = j.value_claim_full() else {
                    continue;
                };
                facts.arg_types.insert((sid, ArgIndex::new(i)), claim);
            }
        }
        // Receiver demand (the guard-at-defs demand filter): Object claims
        // are emitted only for defs whose result is consumed as an element
        // receiver -- there the guard's tag test migrates (the consumer's
        // receiver test elides, dead non-object arms die). An unconsumed
        // object proof is a per-read cost with no payer, and claiming them
        // blanket-wide is a substantial loss. Property receivers guard on
        // class-idx words, which a bare object proof does not elide, so an
        // object claim there is pure cost. Numeric claims stay demand-free.
        let recv_demand: HashSet<(ScriptId, CKey)> = {
            let mut d = HashSet::default();
            for ci in 0..self.engine.cons.len() {
                let sid = self.engine.con_script[ci];
                match &self.engine.cons[ci] {
                    Constraint::Read { recv, name, .. } | Constraint::Write { recv, name, .. }
                        if *name == self.names_of.elems =>
                    {
                        d.insert((sid, *recv));
                    }
                    _ => {}
                }
            }
            d
        };
        // Call-result per-site claims (the call def family): each call
        // constraint's ret var joined over live ctxs, through the full
        // claim tier -- numeric demand-free, object only under receiver
        // demand.
        let elem_pcs: HashSet<(ScriptId, Pc)> = (0..self.engine.cons.len())
            .filter_map(|ci| match &self.engine.cons[ci] {
                Constraint::ElemBuiltin { pc, .. } => Some((self.engine.con_script[ci], *pc)),
                _ => None,
            })
            .collect();
        for ci in 0..self.engine.cons.len() {
            let Constraint::Call { ret, pc, .. } = &self.engine.cons[ci] else {
                continue;
            };
            let CKey::Var(def) = *ret else { continue };
            let (ret, pc) = (*ret, *pc);
            let sid = self.engine.con_script[ci];
            // An array builtin's result is the element-node model's, and
            // the builtin arm has no use for a claim on it.
            if elem_pcs.contains(&(sid, pc)) {
                continue;
            }
            let Some(ctxs) = self.engine.live_ctxs.get(&sid) else {
                continue;
            };
            let Some(j) = self.engine.join_over_ctxs(ctxs, |ctx| CellKey::Var {
                script: sid,
                var: def,
                ctx,
            }) else {
                continue;
            };
            let Some(m) = j.site_claim() else { continue };
            if m.is_object() && !recv_demand.contains(&(sid, ret)) {
                continue;
            }
            facts.call_types.insert(Site::new(sid, pc), m);
        }
        // Fractional-reachable arith sites: the result var of each arith
        // constraint, joined over live ctxs -- double evidence at range Top
        // means a real double population flows through the op, and its
        // both-number arm may keep the Opt track (the numeric-category
        // policy). See LikelyFacts::fractional_arith_sites.
        for ci in 0..self.engine.cons.len() {
            let Constraint::Arith { dst, pc, .. } = &self.engine.cons[ci] else {
                continue;
            };
            let CKey::Var(def) = *dst else { continue };
            let pc = *pc;
            let sid = self.engine.con_script[ci];
            let Some(ctxs) = self.engine.live_ctxs.get(&sid) else {
                continue;
            };
            let Some(j) = self.engine.join_over_ctxs(ctxs, |ctx| CellKey::Var {
                script: sid,
                var: def,
                ctx,
            }) else {
                continue;
            };
            if j.fractional_reachable() {
                facts.fractional_arith_sites.insert(Site::new(sid, pc));
            }
            if j.string_reachable() {
                facts.string_arith_sites.insert(Site::new(sid, pc));
            }
        }
        // Aliased-var per-site claims (the closure-scope analog of the
        // elem value claims): each statically resolved GetAliasedVar site
        // projects its (scope, slot) cell through the purely-numeric gate.
        for read in &self.tables.aliased_reads {
            let key = CellKey::Aliased {
                scope: read.scope,
                slot: read.slot,
            };
            let Some(cid) = self.engine.lookup(key) else {
                continue;
            };
            let Some(m) = self.engine.ts(cid).value_claim_full() else {
                continue;
            };
            if m.is_object()
                && !recv_demand.contains(&(
                    read.site.script,
                    CKey::Aliased {
                        scope: read.scope,
                        slot: read.slot,
                    },
                ))
            {
                continue;
            }
            facts.aliased_sites.insert(read.site, m);
        }
        // Gname value claims (the guard-at-defs family applied to the
        // global store): each context-free GName cell through the full
        // claim tier. Numeric claims demand-free; object claims only where
        // some script consumes the name as an element receiver (the
        // arg_types discipline -- a blanket object proof is a per-read
        // cost with no payer).
        let gname_recv_demand: HashSet<NameId> = recv_demand
            .iter()
            .filter_map(|&(_, k)| match k {
                CKey::GName(n) => Some(n),
                _ => None,
            })
            .collect();
        for (name, cid) in self.engine.gname_cells() {
            let ts = self.engine.ts(cid);
            let Some(m) = ts.value_claim_full().or_else(|| ts.object_claim_nullish()) else {
                continue;
            };
            if m.is_object() && !gname_recv_demand.contains(&name) {
                continue;
            }
            // An element-receiver global whose every value is one
            // typed-array kind claims the kind too: the read's ladder tests
            // the clasp once and the element ops on the value skip theirs.
            let m = match (m.is_object(), self.obj_ta_kind(ts.obj)) {
                (true, Some(k)) => Claim::object_of_ta(k),
                _ => m,
            };
            facts.gname_types.insert(name, m);
        }
    }

    // --- family 2: call-site resolution ----------------------------------

    /// How each call site resolved, plus the delegation edges the layout
    /// analysis walks through.
    fn emit_call_sites(&self, facts: &mut LikelyFacts, caps: &mut CapDrops) -> Delegation {
        // Scripted targets: 1..=MAX_SITE_TARGETS, emitted as a guard chain.
        for (&site, fns) in &self.site_likely_calls {
            if fns.is_multi() || fns.is_empty() {
                continue;
            }
            if fns.ids().len() > MAX_SITE_TARGETS {
                caps.call_targets += 1;
                continue;
            }
            facts.call_sites.insert(
                site,
                CallResolution::Scripted(fns.ids().iter().filter_map(|f| f.as_script()).collect()),
            );
        }
        // accessor_sites: property sites whose agreeing receiver class
        // carries a modeled defineProperty accessor for the name. The
        // target also resolves the site as a scripted call so the
        // accessor-call arm inherits the likely-callee machinery (funcidx
        // patch, typed entries).
        if !self.accessors.is_empty() {
            for &(_, n) in self.accessors.keys() {
                facts.accessor_names.insert(n);
            }
            for ci in 0..self.engine.cons.len() {
                let (name, pc, is_write) = match &self.engine.cons[ci] {
                    super::engine::Constraint::Read { name, pc, .. } => (*name, *pc, false),
                    super::engine::Constraint::Write { name, pc, .. } => (*name, *pc, true),
                    _ => continue,
                };
                let sid = self.engine.con_script[ci];
                let site = Site::new(sid, pc);
                let Some(&c) = self.site_recv_class.get(&site).and_then(Agreed::get) else {
                    continue;
                };
                let Some(&(g, s)) = self.accessors.get(&(c, name)) else {
                    continue;
                };
                let target = if is_write { s } else { g };
                let Some(target) = target else { continue };
                facts
                    .accessor_sites
                    .insert(site, (target, u8::from(is_write)));
                facts
                    .call_sites
                    .entry(site)
                    .or_insert_with(|| CallResolution::Scripted(vec![target]));
            }
        }
        // Native resolution: sites settled on one bare-name modeled native
        // the translator has an arm for. The runtime callee native-pointer
        // guard makes a wrong resolution a missed fast path, never a
        // miscompile. Exclusive with the scripted arm by construction: a
        // site resolves to one native only if every evaluation saw exactly
        // that native, which leaves no scripted id for `site_calls`.
        for (&site, id) in &self.site_native {
            let Some(&id) = id.get() else { continue };
            let Some(info) = self.natives.get(id) else {
                continue;
            };
            if info.kind != super::builtins::NativeKind::Bare {
                continue;
            }
            if super::builtins::has_translator_arm(self.names.get(info.name)) {
                debug_assert!(
                    !facts.call_sites.contains_key(&site),
                    "call site resolved both native and scripted"
                );
                facts.call_sites.insert(site, CallResolution::Native);
            }
        }
        for (&site, &form) in &self.tables.apply_sites {
            facts.apply_sites.insert(site, form);
        }
        let is_hasown = |chars: &[u16]| super::builtins::name_eq(chars, "hasOwnProperty");
        for (&site, id) in &self.site_apply_native {
            let Some(&id) = id.get() else { continue };
            let Some(info) = self.natives.get(id) else {
                continue;
            };
            if info.kind == super::builtins::NativeKind::Bare
                && is_hasown(self.names.get(info.name))
            {
                facts
                    .apply_natives
                    .insert(site, crate::facts::ApplyNative::HasOwnProperty);
            }
        }
        // A self-hosted builtin transcribed with its script
        // (`Object.prototype.hasOwnProperty`) is a mono SCRIPTED apply
        // target; a function object's own name says which. The arm's
        // identity guard makes a same-named user function a miss.
        let mut hasown_scripts: HashSet<ScriptId> = HashSet::default();
        for (_, obj) in self.source.objects() {
            if let crate::source::SourceObject::Object(crate::source::ObjectData {
                kind: crate::source::ObjectKind::Function,
                script: Some(s),
                name: Some(n),
                ..
            }) = obj
            {
                if let crate::source::SourceObject::String(st) = self.source.object(*n) {
                    if is_hasown(st.chars()) {
                        hasown_scripts.insert(ScriptId::new(s.id()));
                    }
                }
            }
        }
        for (&site, (fns, _)) in &self.site_apply {
            if fns.is_multi() || fns.ids().len() != 1 {
                continue;
            }
            let Some(t) = fns.ids()[0].as_script() else {
                continue;
            };
            if hasown_scripts.contains(&t) {
                facts
                    .apply_natives
                    .insert(site, crate::facts::ApplyNative::HasOwnProperty);
            }
        }
        let mut apply_targets: HashMap<Site, ScriptId> = HashMap::default();
        for (&site, (fns, _)) in &self.site_apply {
            if fns.is_multi() || fns.ids().len() != 1 {
                continue;
            }
            let Some(target) = fns.ids()[0].as_script() else {
                continue;
            };
            apply_targets.insert(site, target);
        }
        facts.apply_targets = apply_targets.clone();
        // The per-context resolution, re-keyed by the site that entered
        // the context: joined over every context minted at that site, and
        // kept only where the join is still one script.
        let enter_sites = self.ctxs.enter_sites();
        let mut by_entry: HashMap<(Site, Site), Agreed<ScriptId>> = HashMap::default();
        for (&(cx, site), fns) in &self.site_apply_ctx {
            let Some(entries) = enter_sites.get(&cx) else {
                continue;
            };
            let verdict = match fns.ids() {
                [f] if !fns.is_multi() => f.as_script(),
                _ => None,
            };
            for &entry in entries {
                let e = by_entry.entry((entry, site)).or_default();
                match verdict {
                    Some(t) => e.observe(t),
                    None => *e = Agreed::Conflict,
                }
            }
        }
        let mut sets: HashMap<Site, Vec<ScriptId>> = HashMap::default();
        for (&site, (fns, _)) in &self.site_apply {
            if fns.is_multi() {
                continue;
            }
            let e = sets.entry(site).or_default();
            e.extend(fns.ids().iter().filter_map(|f| f.as_script()));
        }
        for (key, a) in by_entry {
            if let Some(&t) = a.get() {
                facts.apply_targets_in.insert(key, t);
                sets.entry(key.1).or_default().push(t);
            }
        }
        for (site, mut v) in sets {
            v.sort_unstable();
            v.dedup();
            facts.apply_target_sets.insert(site, v);
        }
        // Snapshot of the single-scripted-target sites, so the layout
        // analysis can follow `this.m(...)` delegation without holding a
        // borrow of `facts` while it fills the layout tables.
        let single_call_target: HashMap<Site, ScriptId> = facts
            .scripted_call_sites()
            .filter_map(|(site, targets)| match targets {
                [t] => Some((site, *t)),
                _ => None,
            })
            .collect();
        Delegation {
            apply_targets,
            single_call_target,
        }
    }

    // --- family 4: per-site heap facts -----------------------------------

    /// Per property and element site: the key range, slot and claim it may
    /// guard on, resolved against the layout plan.
    fn emit_site_facts(&self, facts: &mut LikelyFacts, plan: &LayoutPlan) -> SiteFactTotals {
        use super::engine::{CKey, Constraint};
        let mut totals = SiteFactTotals::default();
        // Write-site typed masks are deferred: they upgrade the store
        // fence, which is pure cost unless some typed read consumes the
        // position, and the reads are not all seen yet.
        let mut typed_write_pending: Vec<PendingTypedWrite> = Vec::new();
        for ci in 0..self.engine.cons.len() {
            let (recv, name, pc, is_read) = match &self.engine.cons[ci] {
                Constraint::Read { recv, name, pc, .. } => (*recv, *name, *pc, true),
                Constraint::Write { recv, name, pc, .. } => (*recv, *name, *pc, false),
                _ => continue,
            };
            let sid = self.engine.con_script[ci];
            let site = Site::new(sid, pc);
            // The value-CLASS tier, elems included: the agreed class of the
            // loaded object, mapped through the same plan ranges the
            // receiver rows use. Consumed as an ADVISORY likely-class on
            // the result -- unchecked until a use guards it -- so
            // recording it costs nothing at sites whose values never need
            // identity.
            if is_read {
                if self.opts.diagnostics.propgap {
                    crate::diag_line!(
                        "night: valcls {site} name {} {:?} readts {:?}",
                        String::from_utf16_lossy(self.names.get(name)),
                        self.site_value_class.get(&site),
                        self.site_read_ts.get(&site).map(|t| t.obj)
                    );
                }
                if let Some(&vc) = self.site_value_class.get(&site).and_then(Agreed::get) {
                    let range = if self.engine.region_root(vc) == vc
                        && self
                            .engine
                            .region_members
                            .get(&vc)
                            .is_some_and(|ms| ms.len() > 1)
                    {
                        plan.region_range.get(&vc).copied()
                    } else {
                        plan.range_of(self.group_of_class(vc))
                    };
                    if let Some((lo, hi)) = range {
                        facts
                            .field_cls_sites
                            .insert(site, (LayoutKey::new(lo), LayoutKey::new(hi)));
                    }
                }
            }
            if name == self.names_of.elems {
                self.emit_elem_site(facts, site, is_read, &mut totals);
                continue;
            }
            if is_read {
                // The full claim tier, not just the numeric one: a property
                // read whose value is always an object gets the object-only
                // claim, which the layout mask (a store-conformance claim,
                // numeric by construction) cannot express.
                if let Some(m) = self.site_read_ts.get(&site).and_then(TypeSet::site_claim) {
                    facts.field_sites.insert(site, m);
                }
            }
            if plan.fill_add_sites.contains(&site) {
                // Inside a fill run: the object is still at the prefix
                // key, so the full-key fact would miss every time.
                self.dump_prop_gap(site, name, is_read, "fill-run", recv);
                continue;
            }
            let is_this_recv = recv == CKey::This;
            if is_this_recv
                && (facts.ctor_stamps.contains_key(&sid)
                    || facts.deleg_restamps.contains_key(&sid)
                    || facts.deleg_inits.contains(&sid))
            {
                // Mid-construction: an idx-guarded arm can never hit. An
                // init delegate's `this` is exactly as unstamped as a
                // stamping ctor's -- its own return is what stamps it.
                // Gated before BOTH resolution paths: the region tables
                // serve this-typed sites too.
                self.dump_prop_gap(site, name, is_read, "ctor-this", recv);
                continue;
            }
            let Some(&c) = self.site_recv_class.get(&site).and_then(Agreed::get) else {
                // This-layout precedence: an own-method `this` with a homed
                // layout resolves against that key range even when the
                // solver's receiver evidence stayed a region or conflict
                // (a method's `this` cell can join a wider region than the
                // method's own class). The emitted fact is key-range
                // guarded, so a receiver outside the layout misses at
                // runtime rather than misbehaving.
                if is_this_recv {
                    if let Some(&(klo, khi)) = facts.this_layouts.get(&sid) {
                        let (lo, hi) = (klo.get(), khi.get());
                        let table: &[NameId] = if lo != hi {
                            if let Some((pt, _)) = plan.group_tables.get(&lo) {
                                pt.as_slice()
                            } else {
                                plan.names(lo)
                            }
                        } else {
                            plan.names(lo)
                        };
                        let table_masks = (lo != hi).then(|| {
                            plan.group_tables
                                .get(&lo)
                                .map_or(&[][..], |(_, mk)| mk.as_slice())
                        });
                        let found = plan
                            .table_slot_fact(lo, hi, table, table_masks, name)
                            .or_else(|| plan.subrange_in(lo, hi, name));
                        if let Some(f) = found {
                            insert_prop_site(facts, site, f, is_read);
                            continue;
                        }
                    }
                }
                let had = facts.prop_sites.contains_key(&site);
                self.emit_region_prop_site(facts, plan, site, name, is_read);
                if !had && !facts.prop_sites.contains_key(&site) {
                    self.dump_prop_gap(site, name, is_read, "no-agreed-class", recv);
                }
                continue;
            };
            // A receiver whose agreed class is a REGION ROOT stands for the
            // whole region (an `AnyOf` receiver names its root), and the
            // region's merged fact is the region table -- the universal
            // prefix over every member's rows, guarded by the region's
            // spanning key range. Resolving it against the root's own
            // group instead guards on a range most members are outside of:
            // a miss on every execution whose receiver is another member.
            if self.engine.region_root(c) == c
                && self
                    .engine
                    .region_members
                    .get(&c)
                    .is_some_and(|ms| ms.len() > 1)
            {
                let found = plan.region_range.get(&c).and_then(|&(rlo, rhi)| {
                    plan.region_tables
                        .get(&c)
                        .and_then(|(pt, pm)| plan.table_slot_fact(rlo, rhi, pt, Some(pm), name))
                        .or_else(|| plan.subrange_in(rlo, rhi, name))
                });
                match found {
                    Some(f) => insert_prop_site(facts, site, f, is_read),
                    None => self.dump_prop_gap(site, name, is_read, "region-no-fact", recv),
                }
                continue;
            }
            let group = self.group_of_class(c);
            let this_narrowed = if is_this_recv {
                plan.narrow
                    .get(&sid)
                    .and_then(|cn| plan.ctor_key.get(cn))
                    .copied()
            } else {
                None
            };
            let (lo, hi, table): (u32, u32, Option<&[NameId]>) =
                if let Some((kp, kf)) = this_narrowed {
                    // Two-phase pair: the prefix row is the pair's universal
                    // table (full-only names resolve through subrange_in to
                    // an exact full-key fact below).
                    (kp, kf, Some(plan.names(kp)))
                } else {
                    let Some((lo, hi)) = plan.range_of(group) else {
                        self.dump_prop_gap(site, name, is_read, "no-key-range", recv);
                        continue;
                    };
                    if lo == hi {
                        (lo, lo, Some(plan.names(lo)))
                    } else if let Some((pt, _)) = plan.group_tables.get(&lo) {
                        (lo, hi, Some(pt.as_slice()))
                    } else {
                        (lo, hi, None)
                    }
                };
            // Name-keyed type-dimension mask: the class view cell's numeric
            // claim for the accessed name, uniform across the site's key
            // range -- independent of whether any slot fact exists (it
            // covers post-init fields the layout row never named). Range
            // sites merge member claims by union (the merged mask must
            // cover every member's values); any member without a claim
            // drops the site.
            let nm: Option<Prims> = if lo == hi {
                self.class_view_prims(c, name)
            } else {
                (lo..=hi).try_fold(Prims::EMPTY, |acc, k| {
                    let c2 = plan.key_class.get(&k)?;
                    Some(acc | self.class_view_prims(*c2, name)?)
                })
            };
            // Over a range the masks come from the group's own table, not
            // from the layout the names came from -- and a two-phase pair
            // takes its names from the prefix layout while its masks may
            // have no table at all, in which case the range claims
            // nothing. An exact key answers from its own layout instead.
            let table_masks = (lo != hi).then(|| {
                plan.group_tables
                    .get(&lo)
                    .map_or(&[][..], |(_, mk)| mk.as_slice())
            });
            let found = table
                .and_then(|t| plan.table_slot_fact(lo, hi, t, table_masks, name))
                .or_else(|| {
                    let (glo, ghi) = plan.range_of(group)?;
                    plan.subrange_in(glo, ghi, name)
                });
            if found.is_none() {
                self.dump_prop_gap(site, name, is_read, "no-slot-fact", recv);
                if self.opts.diagnostics.propgap {
                    let names: Vec<String> = table
                        .map(|t| {
                            t.iter()
                                .map(|n| String::from_utf16_lossy(self.names.get(*n)))
                                .collect()
                        })
                        .unwrap_or_default();
                    crate::diag_line!(
                        "night: propgap-detail {site} keys {lo}..{hi} group-range {:?} table {}",
                        plan.range_of(group),
                        names.join(",")
                    );
                }
            }
            if let Some(f) = found {
                insert_prop_site(facts, site, f, is_read);
            }
            if let Some(m) = nm {
                // The typed row's range must equal the prop row's -- only
                // then does a read consume (or a write maintain) the
                // position.
                let slot_pos = match found {
                    Some(f) if f.lo == lo && f.hi == hi => Some(f.slot),
                    _ => None,
                };
                let row = (LayoutKey::new(lo), LayoutKey::new(hi), Claim::of_prims(m));
                if is_read {
                    facts.typed_sites.insert(site, row);
                    if let Some(s) = slot_pos {
                        for k in lo..=hi {
                            totals.typed_read_positions.insert((LayoutKey::new(k), s));
                        }
                    }
                } else {
                    typed_write_pending.push(PendingTypedWrite {
                        site,
                        row,
                        slot: slot_pos,
                    });
                }
            }
        }
        // Consumer-driven store-claim admission: a write site's typed mask
        // upgrades the fence only when some typed read consumes its (key,
        // slot) position; an unconsumed claim is pure per-store cost, and a
        // construction-heavy program pays it at every field init.
        for w in typed_write_pending {
            let consumed = w.slot.is_some_and(|s| {
                (w.row.0.get()..=w.row.1.get()).any(|k| {
                    totals
                        .typed_read_positions
                        .contains(&(LayoutKey::new(k), s))
                })
            });
            if consumed {
                facts.typed_sites.insert(w.site, w.row);
            }
        }
        if !self.tables.saw_ta_ctor {
            facts.elem_poly_sites.clear();
        }
        // Fenced-claim subsumption: a site served by a prop_sites fact with
        // a value claim rides the store fence, so the unfenced per-read
        // value guard there is pure double-guarding -- a measurable loss in
        // a hot method. The mask union upgrades prop_sites masks from
        // typed_sites, so those sites are fenced too. field_sites survives
        // only where no fenced table applies.
        facts.field_sites.retain(|site, _| {
            let prop = facts.prop_sites.get(site);
            let fenced = matches!(prop, Some(&(_, _, _, m)) if m != Claim::NONE)
                || (prop.is_some()
                    && matches!(facts.typed_sites.get(site), Some(&(_, _, m)) if m != Claim::NONE));
            !fenced
        });
        totals
    }

    /// One element site: the typed-array kind, the value claim, and the
    /// array-claim cost/benefit tally.
    fn emit_elem_site(
        &self,
        facts: &mut LikelyFacts,
        site: Site,
        is_read: bool,
        totals: &mut SiteFactTotals,
    ) {
        let recv_root = self
            .site_recv_class
            .get(&site)
            .and_then(Agreed::get)
            .map(|&c| self.engine.region_root(c))
            .filter(|&r| self.heap[r].is_array);
        if is_read {
            if recv_root.is_some() {
                totals.array_fold_reads += 1;
            }
        } else if recv_root.is_none() {
            totals.array_unresolved_writes += 1;
        }
        if let Some(&tk) = self.site_recv_ta.get(&site).and_then(Agreed::get) {
            facts.ta_elem_sites.insert(site, tk);
        }
        facts.elem_poly_sites.insert(site);
        if is_read {
            if let Some(m) = self
                .site_read_ts
                .get(&site)
                .and_then(TypeSet::value_claim_full)
                .filter(|m| !m.is_object())
            {
                facts.elem_sites.insert(site, m);
            }
        } else if let Some(m) = self.write_site_elem_claim(site) {
            facts.elem_write_sites.insert(site, m);
        }
    }

    /// The element claim of a WRITE site, read post-fixpoint: the join of
    /// the `[]` view typesets of every region label the receiver agreed
    /// on (a label without a view, or no agreement, yields nothing).
    fn write_site_elem_claim(&self, site: Site) -> Option<Claim> {
        let labels = self.site_recv_labels.get(&site).and_then(AgreedSet::get)?;
        let mut prims: Option<Prims> = None;
        for &c in labels {
            let root = self.engine.region_root(c);
            let cell = self
                .engine
                .existing_cell(crate::likelier::engine::CellKey::ClassView {
                    class: root,
                    name: self.names_of.elems,
                })?;
            let m = self.engine.ts(cell).value_claim_full()?;
            if m.is_object() {
                return None;
            }
            prims = Some(prims.map_or(m.prims(), |p| p | m.prims()));
        }
        prims.map(Claim::of_prims)
    }

    /// The region rung: a property site whose receiver never resolved to
    /// one class, but whose class labels all live in one region, gets the
    /// region-range fact -- the same guard form over a wider range.
    /// One record per property-access site the analysis leaves WITHOUT a
    /// `prop_sites` row (`--dump-propgap`), naming the gate that refused.
    ///
    /// The class-fact arm is the compact property lowering; a site with no
    /// row falls to the inline cache, which is the same ~540 bytes at every
    /// one of them. The kill censuses say a fact died and `--dump-clsfact`
    /// says whether a consumer wanted one; this says why the analysis never
    /// made one, which is the only question the other two leave open.
    fn dump_prop_gap(
        &self,
        site: Site,
        name: NameId,
        is_read: bool,
        why: &str,
        recv: super::engine::CKey,
    ) {
        use super::engine::CKey;
        if !self.opts.diagnostics.propgap {
            return;
        }
        // The receiver's own shape is most of the answer: a `Var` receiver
        // is a value the body computed -- overwhelmingly a field or element
        // read -- and there is no fact saying which class a field holds.
        let r = match recv {
            CKey::This => "this",
            CKey::Arg(_) => "arg",
            CKey::Var(_) => "var",
            CKey::Ret => "ret",
            CKey::GName(_) => "gname",
            CKey::Aliased { .. } => "aliased",
        };
        // The receiver's abstract object type is the whole story for
        // `no-agreed-class`: `One`/`ClassAny` carry a class, `AnyOf` carries
        // only a region label, `AnyObject` carries nothing and is the state
        // a read off an unclassed receiver produces.
        let k = match self.site_recv.get(&site) {
            None => "unseen",
            Some(super::RecvKind::Empty) => "Empty",
            Some(super::RecvKind::One) => "One",
            Some(super::RecvKind::ClassAny) => "ClassAny",
            Some(super::RecvKind::AnyOf) => "AnyOf",
            Some(super::RecvKind::AnyObject) => "AnyObject",
        };
        crate::diag_line!(
            "night: propgap {site} why {why} recv {r} objty {k} kind {} name {}",
            if is_read { "get" } else { "set" },
            String::from_utf16_lossy(self.names.get(name)),
        );
    }

    fn emit_region_prop_site(
        &self,
        facts: &mut LikelyFacts,
        plan: &LayoutPlan,
        site: Site,
        name: NameId,
        is_read: bool,
    ) {
        let Some(labels) = self.site_recv_labels.get(&site).and_then(AgreedSet::get) else {
            if self.opts.diagnostics.propgap {
                crate::diag_line!("night: propgap-region {site} no-labels");
            }
            return;
        };
        let mut it = labels.iter().map(|c| self.engine.region_root(*c));
        let Some(r0) = it.next() else { return };
        if !it.all(|r| r == r0) {
            if self.opts.diagnostics.propgap {
                crate::diag_line!("night: propgap-region {site} label-roots-disagree");
            }
            return;
        }
        let found = plan.region_range.get(&r0).and_then(|&(rlo, rhi)| {
            plan.region_tables
                .get(&r0)
                .and_then(|(pt, pm)| plan.table_slot_fact(rlo, rhi, pt, Some(pm), name))
                .or_else(|| plan.subrange_in(rlo, rhi, name))
        });
        if self.opts.diagnostics.propgap && found.is_none() {
            crate::diag_line!(
                "night: propgap-region {site} root cls{} range {:?} name {}",
                r0.0,
                plan.region_range.get(&r0),
                String::from_utf16_lossy(self.names.get(name))
            );
        }
        if let Some(f) = found {
            // A fact whose key range excludes a class the site itself
            // observed is self-contradicted: that population misses the
            // guard on every execution. No fact beats a wrong one: the
            // site keeps the IC, which serves everybody.
            let excluded = labels.iter().any(|&c| {
                plan.range_of(self.group_of_class(c))
                    .is_some_and(|(glo, ghi)| ghi < f.lo || glo > f.hi)
            });
            if excluded {
                if self.opts.diagnostics.propgap {
                    crate::diag_line!(
                        "night: propgap-region {site} fact-excludes-seen-class name {}",
                        String::from_utf16_lossy(self.names.get(name))
                    );
                }
                return;
            }
            insert_prop_site(facts, site, f, is_read);
        }
    }

    /// The per-layout field rows the translator reads: name, write-tier
    /// claim, value range, and the typed-tier claim.
    fn emit_class_rows(
        &self,
        facts: &mut LikelyFacts,
        plan: &LayoutPlan,
        typed_read_positions: &HashSet<(LayoutKey, SlotIndex)>,
    ) {
        // Typed-tier layout claims: per layout position, the name-keyed
        // claim where the wmask tier has none. Consumed only in
        // fullword/dims mode as the store-fence + covered-read union.
        let mut typed_prims_by_class: HashMap<u32, Vec<Prims>> = HashMap::default();
        for (&key, row) in &plan.rows {
            let Some(&c) = plan.key_class.get(&key) else {
                continue;
            };
            let base = &row.masks;
            let tm: Vec<Prims> = row
                .names
                .iter()
                .zip(base)
                .enumerate()
                .map(|(i, (name, &m0))| {
                    if !m0.is_empty() {
                        m0
                    } else if typed_read_positions.contains(&(
                        LayoutKey::new(key),
                        SlotIndex::new(u32::try_from(i).unwrap()),
                    )) {
                        self.class_view_prims(c, *name)
                            .filter(|m| m.is_nonempty_subset_of(PRIM_INT32 | PRIM_DOUBLE))
                            .unwrap_or(Prims::EMPTY)
                    } else {
                        Prims::EMPTY
                    }
                })
                .collect();
            if tm.iter().zip(base).any(|(a, b)| a != b) {
                typed_prims_by_class.insert(key, tm);
            }
        }
        for (&k, row) in &plan.rows {
            let prims = &row.masks;
            let ranges = &row.ranges;
            let typed = typed_prims_by_class.get(&k);
            let fields = row
                .names
                .iter()
                .enumerate()
                .map(|(i, n)| ClassFieldFacts {
                    name: *n,
                    prims: prims.get(i).copied().unwrap_or(Prims::EMPTY),
                    range: ranges.get(i).copied().flatten(),
                    // An absent typed row means "same as the write tier",
                    // so the effective fullword claim is the write claim.
                    typed_prims: typed
                        .and_then(|t| t.get(i).copied())
                        .unwrap_or_else(|| prims.get(i).copied().unwrap_or(Prims::EMPTY)),
                })
                .collect();
            facts
                .classes
                .insert(LayoutKey::new(k), ClassFacts { fields });
        }
        for (&lo, (pt, pm)) in &plan.group_tables {
            facts
                .group_tables
                .insert(LayoutKey::new(lo), (pt.to_vec(), pm.clone()));
        }
    }

    /// Array element claims. A claim is keyed on the class-region root,
    /// never a member site: `region_root` already merged the sites whose
    /// arrays flowed together, and the root's cell holds their joined
    /// evidence -- keying a member would let a tight sibling claim cover a
    /// wilder population.
    ///
    /// Cost gate. An element write whose receiver did not resolve to a
    /// single array population owes the maintenance duty unconditionally:
    /// an element has no name to gate on, so unlike a field store it cannot
    /// be shown irrelevant to every claim. That duty is paid at every such
    /// site in the bundle, while the benefit accrues only at read sites a
    /// claim can fold. Where the writes outnumber the folds the dimension
    /// is pure tax, which is the shape of a large compiled-to-JS bundle:
    /// one claiming population against thousands of unresolved element
    /// writes. Static site counts only; no profile.
    fn emit_array_claims(&self, facts: &mut LikelyFacts, totals: &SiteFactTotals) {
        if totals.array_fold_reads <= totals.array_unresolved_writes {
            return;
        }
        let n_elems = self.names_of.elems;
        let mut roots: Vec<ClassId> = Vec::new();
        for (i, ci) in self.heap.classes.iter().enumerate() {
            if !ci.is_array || ci.ta_kind.is_some() {
                continue;
            }
            let c = ClassId(u32::try_from(i).unwrap());
            let root = self.engine.region_root(c);
            if let ClassKey::Site(site) = ci.key {
                facts
                    .array_alloc_sites
                    .insert(site, RegionRoot::new(root.0));
            }
            if !roots.contains(&root) {
                roots.push(root);
            }
        }
        // Per-site receiver root, for both reads (the fold) and writes (the
        // maintenance duty). Keyed by pc, so a field site on an array
        // receiver can land here too -- harmless, the translator only
        // consults this at element ops.
        for (&site, c) in &self.site_recv_class {
            if let Some(&c) = c.get() {
                let root = self.engine.region_root(c);
                if self.heap[root].is_array {
                    facts.array_elem_recv.insert(site, RegionRoot::new(root.0));
                }
            }
        }
        for root in roots {
            // The claim needs both: the range is the value's magnitude, the
            // mask its tag, and the fold serves one int32 arm.
            let (Some(m), Some(range)) = (
                self.class_view_prims(root, n_elems),
                self.class_view_range(root, n_elems),
            ) else {
                continue;
            };
            if m != PRIM_INT32 {
                continue;
            }
            // A claim spanning all of int32 buys a consumer nothing -- an
            // i32 operand already carries IV_I32 -- while still costing the
            // fold and the store duty. A digit array whose hull is
            // full-width lands exactly here: it needs a narrower range
            // before the claim is worth anything.
            if range.lo <= i64::from(i32::MIN) && range.hi >= i64::from(i32::MAX) {
                continue;
            }
            facts
                .array_elem_claims
                .insert(RegionRoot::new(root.0), (m, range));
        }
    }

    /// The predicted value range of a class's view cell, if bounded. The
    /// interval component is already int32-clipped and quantized, so this is
    /// just a projection; callers pair it with `class_view_prims` and drop
    /// it wherever the mask claim is absent.
    fn class_view_range(&self, c: ClassId, name: NameId) -> Option<ValueRange> {
        let cell = self
            .engine
            .lookup(super::engine::CellKey::ClassView { class: c, name })?;
        match self.engine.ts(cell).interval {
            super::types::Interval::In(r) => Some(r),
            _ => None,
        }
    }

    /// The numeric mask of a class's view cell, if any. These masks ride
    /// the store fence, so poison over numeric evidence gets the
    /// optimistic int|double tier rather than a kill:
    ///   - unknown-only poison, same as the this-wmask path;
    ///   - an AnyObject obj part accompanied by unresolved evidence (the
    ///     unresolved-evidence typeset carries both -- poison, not object
    ///     evidence);
    ///   - null/undefined riding with numeric bits (the init-default /
    ///     reset idiom: `this.id = null` then ints forever; the fence
    ///     covers the resets per store).
    ///
    /// Definite string/bool/fn evidence, classed obj parts, and
    /// objectness without the unknown bit stay honest kills: there the
    /// whole-lifetime estimate says the claim would just decay.
    ///
    /// The claim is per-object ("SHALLOW set => claimed fields are
    /// numbers"), the store fence clears SHALLOW on any non-conforming
    /// store, and a wrong prediction costs the degrade path, never a deopt.
    fn class_view_prims(&self, c: ClassId, name: NameId) -> Option<Prims> {
        let cell = self
            .engine
            .lookup(super::engine::CellKey::ClassView { class: c, name })?;
        let ts = self.engine.ts(cell);
        ts.pure_numeric().or_else(|| {
            let base = ts.prims;
            let unknown = ts.unknown;
            let poisoned = unknown || base.intersects(PRIM_NULL | PRIM_UNDEFINED);
            let obj_ok = match ts.obj {
                ObjType::Empty => true,
                ObjType::AnyObject => unknown,
                _ => false,
            };
            (poisoned
                && base.intersects(PRIM_INT32 | PRIM_DOUBLE)
                && base.subset_of(PRIM_INT32 | PRIM_DOUBLE | PRIM_NULL | PRIM_UNDEFINED)
                && ts.fns.is_empty()
                && obj_ok)
                .then_some(if unknown {
                    // Unknown writes could add either numeric kind.
                    PRIM_INT32 | PRIM_DOUBLE
                } else {
                    // Defaults-only poison: every numeric writer is in the
                    // cell, so the numeric projection is exact. Widening an
                    // int32-in-practice field to int|double from here costs
                    // real speed downstream -- the reads lose the int32
                    // track.
                    base & (PRIM_INT32 | PRIM_DOUBLE)
                })
        })
    }

    /// The class a script's `this` settled on, joined over live contexts.
    fn script_this_class(&self, m: ScriptId) -> Option<ClassId> {
        let ctxs = self.engine.live_ctxs.get(&m)?;
        let mut found: Option<ClassId> = None;
        for &cx in ctxs {
            let Some(cell) = self
                .engine
                .lookup(super::engine::CellKey::This { script: m, ctx: cx })
            else {
                continue;
            };
            let c = match self.engine.ts(cell).obj {
                ObjType::One(a) => self.heap.abs_class(a)?,
                ObjType::ClassAny(c) => c,
                ObjType::Empty => continue,
                ObjType::AnyOf(_) | ObjType::AnyObject => return None,
            };
            match found {
                None => found = Some(c),
                Some(prev) if prev != c => return None,
                _ => {}
            }
        }
        found
    }
}
