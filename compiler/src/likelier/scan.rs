/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Bytecode -> constraints, one `OpcodeVisitor` pass per script. The
//! abstract operand stack holds resolved cell references (`CKey`): pure
//! stack shuffling emits nothing, only real dataflow emits constraints.
//!
//! Locals are flow-sensitive: a definition rebinds the slot rather than
//! merging into it, so reusing one bytecode local for unrelated values does
//! not merge their types. Definitions that genuinely meet are joined by
//! directed `Move` edges into a join var at the branch target, which the
//! fixpoint re-propagates through -- so a join neither retroactively
//! coarsens the definitions feeding it nor starves a target that is written
//! later. Join vars are materialized lazily (only when two edges disagree),
//! except at `LoopHead`, where every slot is force-joined so back edges
//! have a standing target.

use super::builtins;
use super::engine::{AllocKind, CKey, Constraint, ElemBuiltinKind, Engine};
use super::types::{arith_transfer, FnId, Interval, NameId, Names, NumOp, TypeSet, ValueRange};
use crate::bytecode::{JSOp, OpcodeVisitor, Script};
use crate::constants::{PRIMARY_EVENT_CAP, TOTAL_EVENT_CAP};
use crate::facts::CallForm;
use crate::ids::{EnvSlot, FormalIndex, JsString, Pc, ScriptId, Site, VarId};
use crate::opsem::{
    Prims, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_NULL, PRIM_STRING, PRIM_UNDEFINED,
};
use crate::source::{Source, SourceObject, SourceObjectId};
use rustc_hash::FxHashMap as HashMap;

pub const ELEMS: &[u16] = &['[' as u16, ']' as u16];
const APPLY: &[u16] = &['a' as u16, 'p' as u16, 'p' as u16, 'l' as u16, 'y' as u16];
const CALL: &[u16] = &['c' as u16, 'a' as u16, 'l' as u16, 'l' as u16];

/// The element-node effect of an array builtin called by this name, if it
/// is one the analysis models.
fn elem_builtin_kind(name: &[u16]) -> Option<ElemBuiltinKind> {
    use ElemBuiltinKind::*;
    for (s, k) in [
        ("push", Write),
        ("unshift", Write),
        ("pop", Read),
        ("shift", Read),
    ] {
        if super::builtins::name_eq(name, s) {
            return Some(k);
        }
    }
    None
}

/// The primary event count (Write/Deleg only). The event budget keys on
/// this, so recording a DelegM never displaces slot evidence.
pub(super) fn primary_events(ev: &[TEvent]) -> usize {
    ev.iter()
        .filter(|e| !matches!(e, TEvent::DelegM(_)))
        .count()
}

/// A construction event in a script's `this`-flow, in program order. Order
/// is load-bearing: this is the slot-order evidence channel, and losing
/// init-time store order costs half the slot facts.
#[derive(Clone, PartialEq)]
pub enum TEvent {
    Write(NameId),
    Deleg(Pc),
    /// `this.m(...)` delegation (the two-phase construction channel);
    /// resolved through the calls table at emission. Kept a separate
    /// variant with its own cap accounting so recording it never displaces
    /// Write/Deleg evidence from the 64-event budget.
    DelegM(Pc),
}

/// One `GetAliasedVar` site whose defining scope the scanner resolved
/// statically.
pub struct AliasedRead {
    pub site: Site,
    pub scope: SourceObjectId,
    pub slot: EnvSlot,
}

/// Scan-side outputs beyond the constraint graph.
#[derive(Default)]
pub struct ScanTables {
    pub this_events: HashMap<ScriptId, Vec<TEvent>>,
    pub lit_order: HashMap<Site, Vec<NameId>>,
    /// Post-allocation `SetProp` name order per allocation site (literal or
    /// resolved `new`): the caller-side init-after-new channel. Recording is
    /// linear and may over-record conditional writes -- the rows are
    /// predictions, so that is safe; order divergence just fails to match.
    pub post_order: HashMap<Site, Vec<NameId>>,
    /// Property writes whose receiver was read from a formal (per script
    /// and formal, capped): the formal-receiver fill channel behind
    /// `arg_restamps`.
    pub arg_writes: HashMap<(ScriptId, FormalIndex), Vec<(NameId, Pc)>>,
    /// Property writes whose receiver was read from a local or a formal
    /// (`RESTAMP_FORMAL | index`), per script and slot, capped: the
    /// post-construction fill channel behind `local_restamps`.
    pub local_writes: HashMap<(ScriptId, u32), Vec<(NameId, Pc)>>,
    /// The reads off the same slots (a write preceded by a read of its
    /// name is an overwrite, not an add).
    pub local_reads: HashMap<(ScriptId, u32), Vec<(NameId, Pc)>>,
    /// `SetLocal`/`SetArg` pcs per (script, slot), for the fill channel's
    /// straight-line check.
    pub local_sets: HashMap<(ScriptId, u32), Vec<Pc>>,
    /// Per script, ascending: the pcs of jump targets, loop heads,
    /// branches and returns.
    pub control_pcs: HashMap<ScriptId, Vec<Pc>>,
    /// Syntactic apply/call-shaped call sites and the form each spells.
    pub apply_sites: HashMap<Site, CallForm>,
    /// Scripts with a `return <expr>` that is not (syntactically)
    /// undefined. Gates the object-returning-constructor rule: a plain
    /// ctor (no explicit return) always yields its `this` allocation.
    pub explicit_ret: rustc_hash::FxHashSet<ScriptId>,
    pub saw_ta_ctor: bool,
    /// What the per-script event budget refused (see [`stats::CapDrops`]).
    pub caps: super::stats::CapDrops,
    pub n_scripts: usize,
    /// GetAliasedVar sites with a statically resolved defining scope.
    /// Ambiguous resolutions are not recorded. Resolved post-solve into
    /// `LikelyFacts::aliased_sites`.
    pub aliased_reads: Vec<AliasedRead>,
    /// Closure-variable accesses whose defining scope the walk resolved /
    /// did not resolve (an unresolved read is analysis-EMPTY).
    pub aliased_resolved: u64,
    pub aliased_unresolved: u64,
    /// 3-argument call sites whose second argument is a String constant
    /// (the `defineProperty(target, name, descriptor)` shape): the
    /// interned name.
    pub call_str_arg1: HashMap<Site, NameId>,
}

#[derive(Clone, PartialEq)]
enum Val {
    Key(CKey),
    /// Unmaterialized constant prim mask (0 = unknown scratch). Becomes a
    /// var + `Const` only if real dataflow consumes it.
    Imm(Prims),
}

#[derive(Clone)]
struct Entry {
    val: Val,
    /// Exact literal interval when the value is a known numeric constant
    /// (or a scan-folded chain of them): feeds `Const` seeds and the
    /// `Arith` constraints' literal fields, where the shift/mask interval
    /// rules need the unquantized value.
    num: Option<ValueRange>,
    is_arguments: bool,
    lit_site: Option<Site>,
    /// The allocation site this value was born at (an object literal or a
    /// resolved `new`), while it flows linearly through stack and locals:
    /// post-allocation `SetProp`s on it record into `post_order`, the
    /// caller-side init-after-new channel that extends layout rows.
    alloc_site: Option<Site>,
    /// `.apply`/`.call` property read: the receiver and which form.
    apply: Option<(CKey, CallForm)>,
    /// `push`/`unshift`/`pop`/`shift` read: the receiver and the effect.
    elem: Option<(CKey, ElemBuiltinKind)>,
    /// Calling this value allocates rather than dispatching: the
    /// `Array` or typed-array constructor, however it was named.
    ctor_alloc: Option<AllocKind>,
    /// The formal this value was read from (set at every `GetArg`,
    /// surviving the slot's flow-sensitive rebinds): property writes on it
    /// record into `arg_writes`, the formal-receiver fill channel. A body
    /// that reassigns the formal is vetoed wholesale by the consumer, so
    /// the unconditional set stays truthful.
    arg_origin: Option<FormalIndex>,
    /// The local this value was read from (set at every `GetLocal`):
    /// property writes on it record into `local_writes`.
    local_origin: Option<u32>,
    /// The property-read constraint that produced this value, so a
    /// consuming call can flag it callee-position.
    read_con: Option<super::engine::ConId>,
    /// Interned chars when the value is a String constant (feeds the
    /// defineProperty name argument).
    str_const: Option<NameId>,
}

impl Entry {
    fn key(k: CKey) -> Entry {
        Entry {
            val: Val::Key(k),
            num: None,
            is_arguments: false,
            lit_site: None,
            alloc_site: None,
            apply: None,
            elem: None,
            ctor_alloc: None,
            arg_origin: None,
            local_origin: None,
            read_con: None,
            str_const: None,
        }
    }

    fn imm(p: Prims) -> Entry {
        Entry {
            val: Val::Imm(p),
            ..Entry::key(CKey::This)
        }
    }

    fn imm_val(p: Prims, v: i64) -> Entry {
        Entry {
            num: Some(ValueRange::new(v, v)),
            ..Entry::imm(p)
        }
    }
}

#[derive(Clone)]
enum Slot {
    Direct(Entry),
    Joined(VarId),
}

pub struct Scan<'a, 'b> {
    pub engine: &'a mut Engine,
    pub names: &'a mut Names,
    pub tables: &'a mut ScanTables,
    pub source: &'b Source,
    pub script: &'b Script,
    pub script_id: ScriptId,
    pub gname_fns: &'a HashMap<NameId, ScriptId>,
    stack: Vec<Entry>,
    locals: HashMap<u32, Entry>,
    next_var: u32,
    join_rows: HashMap<Pc, Vec<Slot>>,
    join_locals: HashMap<Pc, HashMap<u32, Slot>>,
    ft_dead: bool,
    cur_pc: Pc,
}

/// Formals live in the flow-sensitive slot map above every real local slot.
/// Bytecode local slots are dense from 0 and never approach this.
const ARG_SLOT_BASE: u32 = 1 << 24;

/// The slot-map key for formal `i`.
///
/// Formals share the flow-sensitive slot map with locals. A formal differs
/// from a local in exactly one way -- it starts out holding the incoming
/// actual (`CKey::Arg`) rather than nothing -- so `get_arg` seeds it with
/// that on first touch, after which a `SetArg` rebinds it like any other
/// definition and the branch-target joins in `merge_locals_into` / `adopt`
/// apply unchanged.
///
/// Reading the one `CKey::Arg` cell instead would give the join of every
/// caller's actual AND every in-body assignment to the slot. Minifiers reuse
/// formal slots for unrelated values, so a single unclassed assignment
/// anywhere in a body would erase the receiver class at every read of that
/// formal; in minified code one such slot can erase a field's class for the
/// whole program.
fn arg_slot(i: u16) -> u32 {
    ARG_SLOT_BASE + u32::from(i)
}

impl<'a, 'b> Scan<'a, 'b> {
    /// Record a construction event for the current script, subject to the
    /// event budget.
    ///
    /// The budget is one policy with three clauses: a `Write` is
    /// deduplicated by name (a field written twice keeps the slot its
    /// first write created), every event is refused past
    /// `PRIMARY_EVENT_CAP` primaries, and a `DelegM` additionally stops at
    /// `TOTAL_EVENT_CAP` overall -- since it does not count as a primary,
    /// nothing else would ever stop it.
    fn record_this_event(&mut self, ev: TEvent) {
        let events = self.tables.this_events.entry(self.script_id).or_default();
        if let TEvent::Write(n) = ev {
            if events
                .iter()
                .any(|e| matches!(e, TEvent::Write(m) if *m == n))
            {
                return;
            }
        }
        let capped = primary_events(events) >= PRIMARY_EVENT_CAP
            || (matches!(ev, TEvent::DelegM(_)) && events.len() >= TOTAL_EVENT_CAP);
        if capped {
            self.tables.caps.this_events += 1;
            return;
        }
        events.push(ev);
    }

    /// A fresh temporary holding `ts`, as a stack entry.
    fn const_entry(&mut self, ts: TypeSet) -> Entry {
        let v = self.fresh_var();
        self.con(Constraint::Const {
            dst: CKey::Var(v),
            ts,
        });
        Entry::key(CKey::Var(v))
    }

    pub fn new(
        engine: &'a mut Engine,
        names: &'a mut Names,
        tables: &'a mut ScanTables,
        source: &'b Source,
        script: &'b Script,
        script_id: ScriptId,
        gname_fns: &'a HashMap<NameId, ScriptId>,
    ) -> Self {
        Scan {
            engine,
            names,
            tables,
            source,
            script,
            script_id,
            gname_fns,
            stack: Vec::new(),
            locals: HashMap::default(),
            next_var: 0,
            join_rows: HashMap::default(),
            join_locals: HashMap::default(),
            ft_dead: false,
            cur_pc: Pc::new(0),
        }
    }

    fn fresh_var(&mut self) -> VarId {
        let v = self.next_var;
        self.next_var += 1;
        VarId::new(v)
    }

    fn con(&mut self, c: Constraint) {
        self.engine.add_con(self.script_id, c);
    }

    /// The `Const` seed of a materialized `Imm`: the literal interval
    /// (quantized -- cells hold only quantized bounds) upgrades the bare
    /// mask claim.
    fn imm_ts(p: Prims, num: Option<ValueRange>) -> TypeSet {
        let mut ts = TypeSet::prim(p);
        if let Some(r) = num {
            ts.interval = Interval::of_range(r.lo, r.hi);
        }
        ts
    }

    /// Materialize an entry's value as a cell reference. `Imm` becomes a
    /// fresh var (+ a `Const` when the mask is non-empty).
    fn key_of(&mut self, e: &Entry) -> CKey {
        match e.val {
            Val::Key(k) => k,
            Val::Imm(p) => {
                let v = self.fresh_var();
                if p != Prims::EMPTY {
                    self.con(Constraint::Const {
                        dst: CKey::Var(v),
                        ts: Self::imm_ts(p, e.num),
                    });
                }
                CKey::Var(v)
            }
        }
    }

    fn push_e(&mut self, e: Entry) {
        self.stack.push(e);
    }

    fn pop_e(&mut self) -> Entry {
        self.stack.pop().unwrap_or_else(|| Entry::imm(Prims::EMPTY))
    }

    /// Emit the flow of `val` into join var `v`.
    fn flow_into_var(&mut self, val: &Val, num: Option<ValueRange>, v: VarId) {
        match *val {
            Val::Key(k) => {
                if k != CKey::Var(v) {
                    self.con(Constraint::Move {
                        src: k,
                        dst: CKey::Var(v),
                    });
                }
            }
            Val::Imm(Prims::EMPTY) => {}
            Val::Imm(p) => {
                self.con(Constraint::Const {
                    dst: CKey::Var(v),
                    ts: Self::imm_ts(p, num),
                });
            }
        }
    }

    /// Merge an incoming binding into a join-row slot: identical bindings
    /// stay direct (and Imms widen in place); differing bindings upgrade the
    /// slot to a join var fed by both.
    fn merge_slot(&mut self, slot: &mut Slot, incoming: &Entry) {
        match slot {
            Slot::Joined(v) => {
                let v = *v;
                self.flow_into_var(&incoming.val, incoming.num, v);
            }
            Slot::Direct(e) => {
                if e.val == incoming.val {
                    if e.num != incoming.num {
                        e.num = match (e.num, incoming.num) {
                            (Some(a), Some(b)) => Some(a.hull(b)),
                            _ => None,
                        };
                    }
                    return;
                }
                if let (Val::Imm(a), Val::Imm(b)) = (&e.val, &incoming.val) {
                    let w = *a | *b;
                    let n = match (e.num, incoming.num) {
                        (Some(x), Some(y)) => Some(x.hull(y)),
                        _ => None,
                    };
                    if let Val::Imm(m) = &mut e.val {
                        *m = w;
                    }
                    e.num = n;
                    return;
                }
                let v = self.fresh_var();
                let old = e.clone();
                self.flow_into_var(&old.val, old.num, v);
                self.flow_into_var(&incoming.val, incoming.num, v);
                *slot = Slot::Joined(v);
            }
        }
    }

    fn slot_entry(s: &Slot) -> Entry {
        match s {
            Slot::Direct(e) => e.clone(),
            Slot::Joined(v) => Entry::key(CKey::Var(*v)),
        }
    }

    /// A snapshot of the current locals, as a fresh join row.
    fn locals_row(&self) -> HashMap<u32, Slot> {
        self.locals
            .iter()
            .map(|(&s, e)| (s, Slot::Direct(e.clone())))
            .collect()
    }

    /// A snapshot of the current operand stack, as a fresh join row.
    fn stack_row(&self) -> Vec<Slot> {
        self.stack.iter().map(|e| Slot::Direct(e.clone())).collect()
    }

    /// Merge the current locals into an existing join row: a slot the row
    /// already has meets, a slot it does not is adopted outright.
    ///
    /// The state is moved out and put back rather than cloned. `merge_slot`
    /// reaches only `next_var` and the engine -- never `locals` or `stack`
    /// -- so it cannot observe the gap, and a branch edge is a hot enough
    /// path to be worth not copying the whole frame at.
    fn merge_locals_into(&mut self, row: &mut HashMap<u32, Slot>) {
        let locals = std::mem::take(&mut self.locals);
        for (slot, e) in &locals {
            match row.get_mut(slot) {
                Some(rs) => self.merge_slot(rs, e),
                None => {
                    row.insert(*slot, Slot::Direct(e.clone()));
                }
            }
        }
        self.locals = locals;
    }

    /// Merge the current operand stack into an existing join row. A
    /// depth-mismatched edge is skipped: the facts there are
    /// under-constrained and every consumer runtime-guards anyway.
    fn merge_stack_into(&mut self, row: &mut [Slot]) {
        if row.len() != self.stack.len() {
            return;
        }
        let stack = std::mem::take(&mut self.stack);
        for (rs, e) in row.iter_mut().zip(&stack) {
            self.merge_slot(rs, e);
        }
        self.stack = stack;
    }

    /// Record the current state as an edge into the branch target at
    /// `cur_pc + off`.
    fn join_into(&mut self, off: i32) {
        let target = self.cur_pc.branch(off);
        self.join_into_abs(target);
    }

    /// Record the current state as an edge into the branch target at
    /// absolute `target` (table-switch targets arrive absolute).
    fn join_into_abs(&mut self, target: Pc) {
        let row = match self.join_locals.remove(&target) {
            None => self.locals_row(),
            Some(mut row) => {
                self.merge_locals_into(&mut row);
                row
            }
        };
        self.join_locals.insert(target, row);
        let row = match self.join_rows.remove(&target) {
            None => self.stack_row(),
            Some(mut row) => {
                self.merge_stack_into(&mut row);
                row
            }
        };
        self.join_rows.insert(target, row);
    }

    /// Adopt the join rows at a `JumpTarget`/`LoopHead`: merge the
    /// fall-through state in (unless dead), rebind to the row, and at loop
    /// heads force-join every slot so back edges have a standing target.
    fn adopt(&mut self, pc: Pc, loop_head: bool) {
        // The asymmetries against `join_into` are all here, in the two
        // gates: a fall-through that cannot be reached contributes nothing
        // to the merge, and it seeds a fresh locals row only at a loop
        // head (where the back edge will need something to meet with).
        let ft_dead = self.ft_dead;
        match self.join_locals.remove(&pc) {
            None => {
                if loop_head || !ft_dead {
                    let row = self.locals_row();
                    self.join_locals.insert(pc, row);
                }
            }
            Some(mut row) => {
                if !ft_dead {
                    self.merge_locals_into(&mut row);
                }
                self.locals = row
                    .iter()
                    .map(|(&s, sl)| (s, Self::slot_entry(sl)))
                    .collect();
                self.join_locals.insert(pc, row);
            }
        }
        match self.join_rows.remove(&pc) {
            None => {
                let row = self.stack_row();
                self.join_rows.insert(pc, row);
            }
            Some(mut row) => {
                if !ft_dead {
                    self.merge_stack_into(&mut row);
                }
                self.stack = row.iter().map(Self::slot_entry).collect();
                self.join_rows.insert(pc, row);
            }
        }
        if loop_head {
            let mut row = self.join_locals.remove(&pc).unwrap_or_default();
            for (slot, rs) in row.iter_mut() {
                if let Slot::Direct(e) = rs {
                    // Keep `this`-bound slots direct: This is a stable cell,
                    // and losing This-ness here strips the write-attribution
                    // and slot-order channels from `var t = this` loops. A
                    // rare in-loop rebind still upgrades lazily at the back
                    // edge.
                    if e.val == Val::Key(CKey::This) {
                        self.locals.insert(*slot, e.clone());
                        continue;
                    }
                    let v = self.fresh_var();
                    let (val, num) = (e.val.clone(), e.num);
                    self.flow_into_var(&val, num, v);
                    *rs = Slot::Joined(v);
                }
                self.locals.insert(*slot, Self::slot_entry(rs));
            }
            self.join_locals.insert(pc, row);
            let mut srow = self.join_rows.remove(&pc).unwrap_or_default();
            for (i, rs) in srow.iter_mut().enumerate() {
                if let Slot::Direct(e) = rs {
                    let v = self.fresh_var();
                    let (val, num) = (e.val.clone(), e.num);
                    self.flow_into_var(&val, num, v);
                    *rs = Slot::Joined(v);
                }
                if let Some(se) = self.stack.get_mut(i) {
                    *se = Self::slot_entry(rs);
                }
            }
            self.join_rows.insert(pc, srow);
        }
        self.ft_dead = false;
    }

    fn atom(&self, name_index: u32) -> Option<JsString> {
        match self.source.object(self.gcthing_obj(name_index)?) {
            SourceObject::String(s) => Some(JsString::from_chars(s.chars().to_vec())),
            _ => None,
        }
    }

    fn gcthing_fn(&self, index: u32) -> Option<ScriptId> {
        self.source.fn_script(self.gcthing_obj(index)?)
    }

    fn gcthing_obj(&self, index: u32) -> Option<SourceObjectId> {
        let gc = *self.script.gcthings.get(index as usize)?;
        if gc.is_other() {
            return None;
        }
        Some(gc)
    }

    /// Resolve an aliased-var op at the current pc to its defining scope's
    /// source id (innermost covering scope note, else the body scope, then
    /// `hops` environment scopes up).
    fn aliased_scope(&mut self, hops: u16) -> Option<SourceObjectId> {
        let r = self.aliased_scope_inner(hops);
        match r {
            Some(_) => self.tables.aliased_resolved += 1,
            None => self.tables.aliased_unresolved += 1,
        }
        r
    }

    fn aliased_scope_inner(&mut self, hops: u16) -> Option<SourceObjectId> {
        let r = crate::source::aliased_scope_at(self.source, self.script, self.cur_pc, hops);
        if r.is_none() && super::tracers().propgap {
            crate::diag_line!(
                "night: aliased-unresolved {}:{} hops {} body_scope {:?} notes {}",
                self.script_id.get(),
                self.cur_pc,
                hops,
                self.script.body_scope,
                self.script.scope_notes.len()
            );
        }
        r
    }

    /// The fill-channel slot a value was read from: a local, or a formal
    /// under `RESTAMP_FORMAL`.
    fn fill_slot(e: &Entry) -> Option<u32> {
        e.local_origin
            .or_else(|| e.arg_origin.map(|i| crate::facts::RESTAMP_FORMAL | i.get()))
    }

    fn prop_read(&mut self, name_index: u32) {
        let obj = self.pop_e();
        let Some(name) = self.atom(name_index) else {
            self.push_e(Entry::imm(Prims::EMPTY));
            return;
        };
        if let Some(slot) = Self::fill_slot(&obj) {
            let n = self.names.intern(&name);
            let o = self
                .tables
                .local_reads
                .entry((self.script_id, slot))
                .or_default();
            if o.len() < 64 {
                o.push((n, self.cur_pc));
            }
        }
        let recv = self.key_of(&obj);
        let v = self.fresh_var();
        let mut out = Entry::key(CKey::Var(v));
        let apply_form = if name.chars() == APPLY {
            Some(CallForm::Apply)
        } else if name.chars() == CALL {
            Some(CallForm::Call)
        } else {
            None
        };
        if let Some(form) = apply_form {
            out.apply = Some((recv, form));
        }
        if let Some(ek) = elem_builtin_kind(&name) {
            out.elem = Some((recv, ek));
        }
        let name = self.names.intern(&name);
        let pc = self.cur_pc;
        let cid = self.engine.add_con(
            self.script_id,
            Constraint::Read {
                recv,
                name,
                dst: CKey::Var(v),
                pc,
                callee_pos: false,
            },
        );
        out.read_con = Some(cid);
        self.push_e(out);
    }

    fn prop_write(&mut self, name_index: u32, is_init: bool) {
        // SetProp: [obj, val] -> [val]. InitProp: [obj, val] -> [obj].
        let val = self.pop_e();
        let obj = self.pop_e();
        if let Some(name) = self.atom(name_index) {
            let name_id = self.names.intern(&name);
            if obj.val == Val::Key(CKey::This) {
                self.record_this_event(TEvent::Write(name_id));
            }
            if is_init {
                if let Some(site) = obj.lit_site {
                    let o = self.tables.lit_order.entry(site).or_default();
                    if !o.contains(&name_id) && o.len() < 16 {
                        o.push(name_id);
                    }
                }
            } else if let Some(site) = obj.alloc_site {
                let o = self.tables.post_order.entry(site).or_default();
                if !o.contains(&name_id) && o.len() < 16 {
                    o.push(name_id);
                }
            }
            if let Some(ai) = obj.arg_origin {
                let o = self
                    .tables
                    .arg_writes
                    .entry((self.script_id, ai))
                    .or_default();
                if o.len() < 16 {
                    o.push((name_id, self.cur_pc));
                }
            }
            if let Some(slot) = Self::fill_slot(&obj) {
                if !is_init {
                    let o = self
                        .tables
                        .local_writes
                        .entry((self.script_id, slot))
                        .or_default();
                    if o.len() < 32 {
                        o.push((name_id, self.cur_pc));
                    }
                }
            }
            let recv = self.key_of(&obj);
            let src = self.key_of(&val);
            let pc = self.cur_pc;
            self.con(Constraint::Write {
                recv,
                name: name_id,
                src,
                pc,
            });
        }
        self.push_e(if is_init { obj } else { val });
    }

    fn elem_write(&mut self) {
        // [obj, key, val] -> [val]
        let val = self.pop_e();
        self.pop_e();
        let obj = self.pop_e();
        let recv = self.key_of(&obj);
        let src = self.key_of(&val);
        let name = self.names.intern(ELEMS);
        let pc = self.cur_pc;
        self.con(Constraint::Write {
            recv,
            name,
            src,
            pc,
        });
        self.push_e(val);
    }

    fn gname_write(&mut self, name_index: u32) {
        // SetGName: [env, val] -> [val]
        let val = self.pop_e();
        self.pop_e();
        if let Some(name) = self.atom(name_index) {
            let name = self.names.intern(&name);
            let src = self.key_of(&val);
            self.con(Constraint::Move {
                src,
                dst: CKey::GName(name),
            });
        }
        self.push_e(val);
    }

    fn lit_alloc(&mut self, kind: AllocKind) -> Entry {
        let v = self.fresh_var();
        let pc = self.cur_pc;
        self.con(Constraint::Alloc {
            dst: CKey::Var(v),
            pc,
            kind,
        });
        Entry::key(CKey::Var(v))
    }

    fn elem_array_init(&mut self) {
        // InitElemArray: [arr, val] -> [arr]; InitElemInc pops idx too
        // (handled by callers).
        let val = self.pop_e();
        let arr = match self.stack.last() {
            Some(e) => e.clone(),
            None => {
                let e = Entry::imm(Prims::EMPTY);
                self.push_e(e.clone());
                e
            }
        };
        let recv = self.key_of(&arr);
        let src = self.key_of(&val);
        let name = self.names.intern(ELEMS);
        let pc = self.cur_pc;
        self.con(Constraint::Write {
            recv,
            name,
            src,
            pc,
        });
    }

    fn call_op(&mut self, argc: u16, construct: bool) {
        // Call: [callee, this, args]; New: [callee, isCtor, args, newTarget].
        if construct {
            self.pop_e();
        }
        let mut arg_entries: Vec<Entry> = Vec::with_capacity(argc as usize);
        for _ in 0..argc {
            arg_entries.push(self.pop_e());
        }
        arg_entries.reverse();
        let this_ = self.pop_e();
        let callee = self.pop_e();
        let pc = self.cur_pc;
        let v = self.fresh_var();
        let ret = CKey::Var(v);

        if argc == 3 && !construct {
            if let Some(n) = arg_entries[1].str_const {
                self.tables
                    .call_str_arg1
                    .insert(Site::new(self.script_id, pc), n);
            }
        }

        if let Some((recv, form)) = callee.apply {
            if !construct && argc >= 1 {
                self.tables
                    .apply_sites
                    .insert(Site::new(self.script_id, pc), form);
                if arg_entries[0].val == Val::Key(CKey::This) {
                    self.record_this_event(TEvent::Deleg(pc));
                }
                let arg1_is_arguments = arg_entries.get(1).is_some_and(|e| e.is_arguments);
                let args: std::rc::Rc<[CKey]> =
                    arg_entries.iter().map(|e| self.key_of(e)).collect();
                self.con(Constraint::Apply {
                    target: recv,
                    args,
                    arg1_is_arguments,
                    ret,
                    pc,
                    form,
                });
                self.push_e(Entry::key(ret));
                return;
            }
        }
        // `this.m(...)`: a this-method delegation event (the two-phase
        // construction channel). Resolution to the callee happens at
        // emission through the calls table, exactly like apply_targets
        // for the `.call/.apply` shape above.
        if !construct && this_.val == Val::Key(CKey::This) {
            self.record_this_event(TEvent::DelegM(pc));
        }
        // The element-node effect of an array builtin rides beside the
        // call itself: the callee is still resolved and bound, so a
        // receiver whose `push` is a scripted method (react's
        // `destination`) is evaluated, and one the analysis cannot name
        // collapses the site's callee set as any other call would.
        if let Some((recv, kind)) = callee.elem {
            if !construct {
                let arg = arg_entries.first().map(|e| self.key_of(e));
                self.con(Constraint::ElemBuiltin {
                    recv,
                    arg,
                    ret,
                    pc,
                    kind,
                });
            }
        }
        if let Some(kind) = callee.ctor_alloc {
            // `Array(n)` and `new Array(n)` are the same allocation, and so
            // is every typed-array constructor's.
            self.con(Constraint::Alloc { dst: ret, pc, kind });
            self.push_e(Entry::key(ret));
            return;
        }
        if let Some(cid) = callee.read_con {
            if let Constraint::Read { callee_pos, .. } = &mut self.engine.cons[cid.0 as usize] {
                *callee_pos = true;
            }
        }
        let callee_k = self.key_of(&callee);
        let this_k = if construct {
            None
        } else {
            Some(self.key_of(&this_))
        };
        let args: std::rc::Rc<[CKey]> = arg_entries.iter().map(|e| self.key_of(e)).collect();
        self.con(Constraint::Call {
            callee: callee_k,
            this_: this_k,
            args,
            ret,
            pc,
            construct,
        });
        let mut e = Entry::key(ret);
        if construct {
            e.alloc_site = Some(Site::new(self.script_id, pc));
        }
        self.push_e(e);
    }

    fn ret_flow(&mut self) {
        let v = self.pop_e();
        if v.val != Val::Imm(PRIM_UNDEFINED) && v.val != Val::Key(CKey::This) {
            self.tables.explicit_ret.insert(self.script_id);
        }
        let src = self.key_of(&v);
        self.con(Constraint::Move {
            src,
            dst: CKey::Ret,
        });
    }

    /// Whether `op` is handled by a specific callback (so `before_op` must
    /// not apply the generic stack effect).
    fn special(op: JSOp) -> bool {
        use JSOp::*;
        matches!(
            op,
            Pop | PopN
                | Dup
                | Dup2
                | DupAt
                | Swap
                | Pick
                | Unpick
                | Undefined
                | Null
                | True
                | False
                | Int32
                | Zero
                | One
                | Int8
                | Uint16
                | Uint24
                | Double
                | String
                | Lambda
                | Object
                | GetGName
                | GetIntrinsic
                | GetLocal
                | SetLocal
                | InitLexical
                | GetArg
                | GetFrameArg
                | SetArg
                | FunctionThis
                | GetProp
                | SetProp
                | StrictSetProp
                | InitProp
                | InitHiddenProp
                | InitLockedProp
                | NewInit
                | NewObject
                | SetGName
                | StrictSetGName
                | InitGLexical
                | GetAliasedVar
                | SetAliasedVar
                | InitAliasedLexical
                | Arguments
                | NewArray
                | InitElemArray
                | InitElemInc
                | GetElem
                | SetElem
                | StrictSetElem
                | ToPropertyKey
                | Call
                | CallContent
                | CallIter
                | CallContentIter
                | CallIgnoresRv
                | New
                | NewContent
                | Return
                | SetRval
        )
    }

    /// Coarse result-prim mask for generically-handled ops.
    fn result_prims(op: JSOp) -> Prims {
        use JSOp::*;
        match op {
            Eq | Ne | StrictEq | StrictNe | Lt | Gt | Le | Ge | Not | In | HasOwn | Instanceof
            | IsNullOrUndefined => PRIM_BOOLEAN,
            // A for-in key is always a string (symbols are skipped, indexes
            // stringified); the no-iter magic never reaches a use.
            Typeof | TypeofExpr | ToString | MoreIter => PRIM_STRING,
            _ => Prims::EMPTY,
        }
    }

    /// Ops with an operand-sensitive arithmetic transfer function.
    fn arith_op(op: JSOp) -> Option<NumOp> {
        use JSOp::*;
        Some(match op {
            Add => NumOp::Add,
            Sub => NumOp::Sub,
            Mul => NumOp::Mul,
            Div => NumOp::Div,
            Mod => NumOp::Mod,
            Pow => NumOp::Pow,
            Inc => NumOp::Inc,
            Dec => NumOp::Dec,
            Neg => NumOp::Neg,
            Pos => NumOp::Pos,
            Ursh => NumOp::Ursh,
            ToNumeric => NumOp::ToNumeric,
            // The bitops speak the vocabulary too (same (int32, I32)
            // claims the generic path made, now operand-routed).
            BitAnd => NumOp::BitAnd,
            BitOr => NumOp::BitOr,
            BitXor => NumOp::BitXor,
            Lsh => NumOp::Lsh,
            Rsh => NumOp::Rsh,
            BitNot => NumOp::BitNot,
            _ => return None,
        })
    }

    /// An arith operand that is unmodeled scratch (`Imm(0)`) coerces to
    /// the generic numeric mask: some number.
    fn arith_operand(e: Entry) -> Entry {
        if e.val == Val::Imm(Prims::EMPTY) {
            Entry::imm(PRIM_INT32 | PRIM_DOUBLE)
        } else {
            e
        }
    }

    fn do_arith(&mut self, op: NumOp) {
        let b = if op.unary() {
            None
        } else {
            Some(Self::arith_operand(self.pop_e()))
        };
        let a = Self::arith_operand(self.pop_e());
        let imm = |e: &Entry| match e.val {
            Val::Imm(p) => Some(p),
            Val::Key(_) => None,
        };
        // Constant operands fold at scan time; a constraint is emitted only
        // when real dataflow feeds the op. The literal interval folds
        // exactly alongside (the `(1 << 28) - 1` mask chains must reach
        // later `&`/shift sites unquantized).
        if let Some(pa) = imm(&a) {
            let pb = b.as_ref().map(imm);
            let folded = match pb {
                None => Some(arith_transfer(op, &TypeSet::prim(pa), None)),
                Some(Some(pb)) => Some(arith_transfer(
                    op,
                    &TypeSet::prim(pa),
                    Some(&TypeSet::prim(pb)),
                )),
                Some(None) => None,
            };
            if let Some((m, _)) = folded {
                let mut out = Entry::imm(m);
                if let Some(na) = a.num {
                    let nb = b.as_ref().map(|e| e.num);
                    if nb != Some(None) {
                        out.num = super::types::arith_lit(op, na, nb.flatten());
                    }
                }
                self.push_e(out);
                return;
            }
        }
        let (a_lit, b_lit) = (a.num, b.as_ref().and_then(|e| e.num));
        let ka = self.key_of(&a);
        let kb = b.map(|e| self.key_of(&e));
        let v = self.fresh_var();
        let pc = self.cur_pc;
        self.con(Constraint::Arith {
            op,
            a: ka,
            b: kb,
            dst: CKey::Var(v),
            a_lit,
            b_lit,
            pc,
        });
        self.push_e(Entry::key(CKey::Var(v)));
    }
}

impl OpcodeVisitor for Scan<'_, '_> {
    fn before_op(&mut self, pc: Pc, op: JSOp, nuses: usize, ndefs: usize) {
        use JSOp::*;
        self.cur_pc = pc;
        if matches!(
            op,
            JumpTarget
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
                | RetRval
                | Throw
                | ThrowWithStack
                | ThrowMsg
        ) {
            self.tables
                .control_pcs
                .entry(self.script_id)
                .or_default()
                .push(pc);
        }
        if matches!(op, JumpTarget | LoopHead) {
            self.adopt(pc, op == LoopHead);
            return;
        }
        if Self::special(op) {
            return;
        }
        if let Some(ak) = Self::arith_op(op) {
            let need = if ak.unary() { 1 } else { 2 };
            if nuses == need && ndefs == 1 {
                self.do_arith(ak);
                return;
            }
        }
        for _ in 0..nuses {
            self.pop_e();
        }
        let prims = Self::result_prims(op);
        for _ in 0..ndefs {
            self.push_e(Entry::imm(prims));
        }
    }

    // --- branches ---
    fn goto_(&mut self, off: i32) {
        self.join_into(off);
        self.stack.clear();
        self.ft_dead = true;
    }
    fn jump_if_false(&mut self, off: i32) {
        self.join_into(off);
    }
    fn jump_if_true(&mut self, off: i32) {
        self.join_into(off);
    }
    fn and_(&mut self, off: i32) {
        self.join_into(off);
    }
    fn or_(&mut self, off: i32) {
        self.join_into(off);
    }
    fn coalesce(&mut self, off: i32) {
        self.join_into(off);
    }
    // Switch dispatch. Each case/default target needs its own join edge,
    // so a case body whose predecessor ended dead does not inherit the
    // previous case's locals -- a `SetArg` rebind in one case would
    // otherwise leak into its siblings.
    fn case_(&mut self, off: i32) {
        // val, cond => val (if !cond); the taken edge consumes val too.
        let _cond = self.pop_e();
        let val = self.pop_e();
        self.join_into(off);
        self.push_e(val);
    }
    fn default_(&mut self, off: i32) {
        let _val = self.pop_e();
        self.join_into(off);
        self.stack.clear();
        self.ft_dead = true;
    }
    fn table_switch(&mut self, default_offset: i32, _low: i32, _high: i32, offsets: &[Pc]) {
        let _i = self.pop_e();
        self.join_into(default_offset);
        for &t in offsets {
            self.join_into_abs(t);
        }
        self.stack.clear();
        self.ft_dead = true;
    }

    // --- stack manipulation (exact, so entries keep their references) ---
    fn pop(&mut self) {
        self.pop_e();
    }
    fn pop_n(&mut self, n: u16) {
        for _ in 0..n {
            self.pop_e();
        }
    }
    fn dup(&mut self) {
        let e = self.pop_e();
        self.push_e(e.clone());
        self.push_e(e);
    }
    fn dup2(&mut self) {
        let b = self.pop_e();
        let a = self.pop_e();
        self.push_e(a.clone());
        self.push_e(b.clone());
        self.push_e(a);
        self.push_e(b);
    }
    fn dup_at(&mut self, n: u32) {
        let len = self.stack.len();
        let e = if (n as usize) < len {
            self.stack[len - 1 - n as usize].clone()
        } else {
            Entry::imm(Prims::EMPTY)
        };
        self.push_e(e);
    }
    fn swap(&mut self) {
        let b = self.pop_e();
        let a = self.pop_e();
        self.push_e(b);
        self.push_e(a);
    }
    fn pick(&mut self, n: u8) {
        let len = self.stack.len();
        if (n as usize) < len {
            let e = self.stack.remove(len - 1 - n as usize);
            self.push_e(e);
        } else {
            self.stack.clear();
            self.push_e(Entry::imm(Prims::EMPTY));
        }
    }
    fn unpick(&mut self, n: u8) {
        let len = self.stack.len();
        if (n as usize) < len {
            let e = self.pop_e();
            let at = self.stack.len() - n as usize;
            self.stack.insert(at, e);
        } else {
            self.stack.clear();
        }
    }

    // --- constants ---
    fn undefined(&mut self) {
        self.push_e(Entry::imm(PRIM_UNDEFINED));
    }
    fn null(&mut self) {
        self.push_e(Entry::imm(PRIM_NULL));
    }
    fn true_(&mut self) {
        self.push_e(Entry::imm(PRIM_BOOLEAN));
    }
    fn false_(&mut self) {
        self.push_e(Entry::imm(PRIM_BOOLEAN));
    }
    fn int32(&mut self, v: u32) {
        self.push_e(Entry::imm_val(PRIM_INT32, i64::from(v as i32)));
    }
    fn zero(&mut self) {
        self.push_e(Entry::imm_val(PRIM_INT32, 0));
    }
    fn one(&mut self) {
        self.push_e(Entry::imm_val(PRIM_INT32, 1));
    }
    fn int8(&mut self, v: u8) {
        self.push_e(Entry::imm_val(PRIM_INT32, i64::from(v as i8)));
    }
    fn uint16(&mut self, v: u16) {
        self.push_e(Entry::imm_val(PRIM_INT32, i64::from(v)));
    }
    fn uint24(&mut self, v: u32) {
        self.push_e(Entry::imm_val(PRIM_INT32, i64::from(v)));
    }
    fn double(&mut self, v: u64) {
        let f = f64::from_bits(v);
        let mut e = Entry::imm(PRIM_DOUBLE);
        if f.fract() == 0.0 && f.abs() <= (1u64 << 53) as f64 && !(f == 0.0 && f.is_sign_negative())
        {
            e.num = Some(ValueRange::new(f as i64, f as i64));
        }
        self.push_e(e);
    }
    fn string(&mut self, i: u32) {
        let mut e = Entry::imm(PRIM_STRING);
        if let Some(chars) = self.atom(i) {
            e.str_const = Some(self.names.intern(&chars));
        }
        self.push_e(e);
    }

    // --- function values / literals ---
    fn lambda(&mut self, func_index: u32) {
        let e = match self.gcthing_fn(func_index) {
            Some(s) => self.const_entry(TypeSet::fn_one(FnId::script(s))),
            None => Entry::imm(Prims::EMPTY),
        };
        self.push_e(e);
    }
    fn object(&mut self, object_index: u32) {
        let e = match self.gcthing_obj(object_index) {
            Some(oid) => self.lit_alloc(AllocKind::Snapshot(oid)),
            None => Entry::imm(Prims::EMPTY),
        };
        self.push_e(e);
    }
    fn new_init(&mut self, _property_count: u8) {
        let mut e = self.lit_alloc(AllocKind::Plain);
        e.lit_site = Some(Site::new(self.script_id, self.cur_pc));
        e.alloc_site = e.lit_site;
        self.push_e(e);
    }
    fn new_object(&mut self, _shape_index: u32) {
        let mut e = self.lit_alloc(AllocKind::Plain);
        e.lit_site = Some(Site::new(self.script_id, self.cur_pc));
        e.alloc_site = e.lit_site;
        self.push_e(e);
    }
    fn new_array(&mut self, _length: u32) {
        let e = self.lit_alloc(AllocKind::Array);
        self.push_e(e);
    }
    fn init_elem_array(&mut self, _index: u32) {
        self.elem_array_init();
    }
    fn init_elem_inc(&mut self) {
        // [arr, idx, val] -> [arr, idx+1]
        let val = self.pop_e();
        self.pop_e();
        self.push_e(val);
        self.elem_array_init();
        self.push_e(Entry::imm(PRIM_INT32));
    }
    fn get_elem(&mut self) {
        // [obj, key] -> [val]
        self.pop_e();
        let obj = self.pop_e();
        let recv = self.key_of(&obj);
        let v = self.fresh_var();
        let name = self.names.intern(ELEMS);
        let pc = self.cur_pc;
        let cid = self.engine.add_con(
            self.script_id,
            Constraint::Read {
                recv,
                name,
                dst: CKey::Var(v),
                pc,
                callee_pos: false,
            },
        );
        let mut e = Entry::key(CKey::Var(v));
        e.read_con = Some(cid);
        self.push_e(e);
    }
    fn set_elem(&mut self) {
        self.elem_write();
    }
    fn strict_set_elem(&mut self) {
        self.elem_write();
    }
    fn to_property_key(&mut self) {
        // Identity for the scan's purposes: the canonicalized key keeps
        // the value's number-vs-name classification (the compound-assign
        // `a[k] op= v` key path).
    }

    // --- names / locals / args / this ---
    fn get_intrinsic(&mut self, name_index: u32) {
        // A self-hosted intrinsic reference: the %-mangled gname cell the
        // heap seeding arms for modeled kernels (an unmodeled name reads
        // an unseeded, empty cell).
        let e = match self.atom(name_index) {
            Some(n) => {
                let mut chars: Vec<u16> = vec![u16::from(b'%')];
                chars.extend_from_slice(n.chars());
                Entry::key(CKey::GName(self.names.intern(&chars)))
            }
            None => Entry::imm(Prims::EMPTY),
        };
        self.push_e(e);
    }
    fn get_g_name(&mut self, name_index: u32) {
        let name = self.atom(name_index);
        let e = match &name {
            Some(n) => {
                if let Some(&s) = self.gname_fns.get(&self.names.intern(n.chars())) {
                    self.const_entry(TypeSet::fn_one(FnId::script(s)))
                } else if builtins::is_array_ctor_name(n) {
                    // The marker serves the direct `new Array(n)` form; the
                    // typeset value survives aliasing (`var Vector = Array`).
                    let mut e = self.const_entry(TypeSet::fn_one(FnId::ARRAY_CTOR));
                    e.ctor_alloc = Some(AllocKind::Array);
                    e
                } else if let Some(k) = builtins::ta_kind_for_ctor_name(n) {
                    self.tables.saw_ta_ctor = true;
                    let mut e = self.const_entry(TypeSet::fn_one(FnId::typed_array_ctor(k)));
                    e.ctor_alloc = Some(AllocKind::TypedArray(k));
                    e
                } else {
                    let id = self.names.intern(n);
                    Entry::key(CKey::GName(id))
                }
            }
            None => Entry::imm(Prims::EMPTY),
        };
        self.push_e(e);
    }
    fn set_g_name(&mut self, name_index: u32) {
        self.gname_write(name_index);
    }
    fn strict_set_g_name(&mut self, name_index: u32) {
        self.gname_write(name_index);
    }
    fn init_g_lexical(&mut self, name_index: u32) {
        // [val] -> [val]
        if let Some(name) = self.atom(name_index) {
            if let Some(top) = self.stack.last().cloned() {
                let name = self.names.intern(&name);
                let src = self.key_of(&top);
                self.con(Constraint::Move {
                    src,
                    dst: CKey::GName(name),
                });
            }
        }
    }
    fn get_local(&mut self, n: u32) {
        if let Some(e) = self.locals.get(&n) {
            let mut e = e.clone();
            e.local_origin = Some(n);
            self.push_e(e);
            return;
        }
        // Give an unbound slot a stable identity so later reads share it.
        let v = self.fresh_var();
        let mut e = Entry::key(CKey::Var(v));
        self.locals.insert(n, e.clone());
        e.local_origin = Some(n);
        self.push_e(e);
    }
    fn set_local(&mut self, n: u32) {
        self.tables
            .local_sets
            .entry((self.script_id, n))
            .or_default()
            .push(self.cur_pc);
        // A definition rebinds the slot (flow-sensitive locals; the joins
        // happen at branch targets). [val] -> [val].
        if self.stack.is_empty() {
            self.push_e(Entry::imm(Prims::EMPTY));
        }
        let top = self.stack.last().unwrap().clone();
        self.locals.insert(n, top);
    }
    fn init_lexical(&mut self, n: u32) {
        self.set_local(n);
    }
    fn get_arg(&mut self, i: u16) {
        let e = if i < self.script.nargs {
            let slot = arg_slot(i);
            let mut e = match self.locals.get(&slot) {
                Some(e) => e.clone(),
                None => {
                    // First touch: the formal still holds the incoming
                    // actual, which is what `CKey::Arg` names.
                    let e = Entry::key(CKey::Arg(FormalIndex::new(u32::from(i))));
                    self.locals.insert(slot, e.clone());
                    e
                }
            };
            e.arg_origin = Some(FormalIndex::new(u32::from(i)));
            e
        } else {
            Entry::imm(Prims::EMPTY)
        };
        self.push_e(e);
    }
    fn get_frame_arg(&mut self, i: u16) {
        // The frame slot the engine reads when an (unmapped) `arguments`
        // exists is the formal itself; same dataflow as `GetArg` (the
        // codegen lowers both through `read_arg`), so a closure capturing
        // a formal in a body that also reads `arguments` sees the same
        // value `GetArg` would give it.
        self.get_arg(i);
    }
    fn set_arg(&mut self, i: u16) {
        self.tables
            .local_sets
            .entry((self.script_id, crate::facts::RESTAMP_FORMAL | u32::from(i)))
            .or_default()
            .push(self.cur_pc);
        if i < self.script.nargs {
            if let Some(top) = self.stack.last().cloned() {
                let src = self.key_of(&top);
                // The `Move` stays: `CKey::Arg` remains the upper bound over
                // everything the slot ever holds, which is what a mapped
                // `arguments` object aliases and what the formal-type facts
                // read. Precision comes from the rebind below, which is what
                // later `GetArg`s in this body now see.
                self.con(Constraint::Move {
                    src,
                    dst: CKey::Arg(FormalIndex::new(u32::from(i))),
                });
                self.locals.insert(arg_slot(i), top);
            }
        }
    }
    fn function_this(&mut self) {
        self.push_e(Entry::key(CKey::This));
    }
    fn get_aliased_var(&mut self, hops: u16, slot: u32) {
        let slot = EnvSlot::new(slot);
        let e = match self.aliased_scope(hops) {
            Some(scope) => {
                self.tables.aliased_reads.push(AliasedRead {
                    site: Site::new(self.script_id, self.cur_pc),
                    scope,
                    slot,
                });
                Entry::key(CKey::Aliased { scope, slot })
            }
            None => Entry::imm(Prims::EMPTY),
        };
        self.push_e(e);
    }
    fn set_aliased_var(&mut self, hops: u16, slot: u32) {
        // [val] -> [val]
        let slot = EnvSlot::new(slot);
        if let Some(scope) = self.aliased_scope(hops) {
            if let Some(top) = self.stack.last().cloned() {
                let src = self.key_of(&top);
                self.con(Constraint::Move {
                    src,
                    dst: CKey::Aliased { scope, slot },
                });
            }
        }
    }
    fn init_aliased_lexical(&mut self, hops: u16, slot: u32) {
        self.set_aliased_var(hops, slot);
    }

    // --- properties ---
    fn get_prop(&mut self, name_index: u32) {
        self.prop_read(name_index);
    }
    fn set_prop(&mut self, name_index: u32) {
        self.prop_write(name_index, false);
    }
    fn strict_set_prop(&mut self, name_index: u32) {
        self.prop_write(name_index, false);
    }
    fn init_prop(&mut self, name_index: u32) {
        self.prop_write(name_index, true);
    }
    fn init_hidden_prop(&mut self, name_index: u32) {
        self.prop_write(name_index, true);
    }
    fn init_locked_prop(&mut self, name_index: u32) {
        self.prop_write(name_index, true);
    }
    fn arguments(&mut self) {
        let mut e = Entry::imm(Prims::EMPTY);
        e.is_arguments = true;
        self.push_e(e);
    }

    // --- calls ---
    fn call(&mut self, argc: u16) {
        self.call_op(argc, false);
    }
    fn call_content(&mut self, argc: u16) {
        self.call_op(argc, false);
    }
    fn call_iter(&mut self, argc: u16) {
        self.call_op(argc, false);
    }
    fn call_content_iter(&mut self, argc: u16) {
        self.call_op(argc, false);
    }
    fn call_ignores_rv(&mut self, argc: u16) {
        self.call_op(argc, false);
    }
    fn new_(&mut self, argc: u16) {
        self.call_op(argc, true);
    }
    fn new_content(&mut self, argc: u16) {
        self.call_op(argc, true);
    }

    // --- returns ---
    fn return_(&mut self) {
        self.ret_flow();
    }
    fn set_rval(&mut self) {
        self.ret_flow();
    }
}

/// Scan every script in the bundle into the shared engine.
pub fn scan_all(
    engine: &mut Engine,
    names: &mut Names,
    tables: &mut ScanTables,
    source: &Source,
    gname_fns: &HashMap<NameId, ScriptId>,
) {
    for (id, obj) in source.objects() {
        let SourceObject::Script(script) = obj else {
            continue;
        };
        let scan = Scan::new(
            engine,
            names,
            tables,
            source,
            script,
            ScriptId::new(id.id()),
            gname_fns,
        );
        script.parser().visit(scan);
        tables.n_scripts += 1;
    }
}
