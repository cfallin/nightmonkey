/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Post-fixpoint per-script effect summaries: a per-script op walk
//! classifying every op against a known-benign set, a call-edge fold over
//! the solved resolution tables, and a transitive fixpoint that fills
//! `LikelyFacts::script_effects`. Produced from the solved state only --
//! never fed back into the solve.

use super::builtins::{self, NativeEffect};
use super::emit::LayoutPlan;
use super::types::{Agreed, ClassId, NameId, Names};
use super::Solver;
use crate::bytecode::{JSOp, OpcodeVisitor, Script};
use crate::facts::{CallResolution, EffectSummary, LikelyFacts};
use crate::ids::{LayoutKey, Pc, ScriptId, Site};
use crate::source::{Source, SourceObject};
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;

const FIELD_CAP: usize = 16;
const GNAME_CAP: usize = 8;

/// A field write's receiver, pre-plan-mapping.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FieldRecv {
    Cls(ClassId),
    /// The write's receiver is the script's own `this` (no agreed class at
    /// the site): mapped through `this_layouts`.
    This,
    Unknown,
}

/// The op that pushed a value, for the unresolved-callee labels: a linear
/// per-block guess (joins keep the fall-through path), diagnostic-only.
#[derive(Clone, Copy, Default)]
struct Origin {
    op: Option<JSOp>,
    name: Option<NameId>,
    num: Option<u32>,
}

#[derive(Default)]
struct LocalEffects {
    sum: EffectSummary,
    field_writes: Vec<(FieldRecv, NameId)>,
    /// Call and construct sites whose targets fold in transitively.
    calls: Vec<Site>,
    /// Property reads of a registered accessor name: fold the resolved
    /// getter, saturate when unresolved.
    accessor_reads: Vec<Site>,
    /// Per call pc, what pushed the callee.
    callee_origin: HashMap<Pc, Origin>,
}

struct EffectWalk<'a> {
    sid: ScriptId,
    script: &'a Script,
    source: &'a Source,
    names: &'a mut Names,
    recv_class: &'a HashMap<Site, Agreed<ClassId>>,
    this_writes: &'a HashSet<Site>,
    accessor_names: &'a HashSet<NameId>,
    cur_pc: Pc,
    stack: Vec<Origin>,
    out: LocalEffects,
}

impl<'a> EffectWalk<'a> {
    fn sim_stack(&mut self, pc: Pc, op: JSOp, nuses: usize, ndefs: usize) {
        use JSOp::*;
        match op {
            Dup => {
                let t = self.stack.last().copied().unwrap_or_default();
                self.stack.push(t);
            }
            Dup2 => {
                let n = self.stack.len();
                let a = self
                    .stack
                    .get(n.wrapping_sub(2))
                    .copied()
                    .unwrap_or_default();
                let b = self.stack.last().copied().unwrap_or_default();
                self.stack.push(a);
                self.stack.push(b);
            }
            Swap => {
                let n = self.stack.len();
                if n >= 2 {
                    self.stack.swap(n - 1, n - 2);
                }
            }
            // Operand-carrying shufflers: net effect applied in the
            // per-op methods below.
            DupAt => self.stack.push(Origin::default()),
            Pick | Unpick => {}
            Call | CallContent | CallIgnoresRv | New | NewContent => {
                let n = self.stack.len();
                let callee = n
                    .checked_sub(nuses)
                    .and_then(|i| self.stack.get(i))
                    .copied()
                    .unwrap_or_default();
                self.out.callee_origin.insert(pc, callee);
                self.pop_push(op, nuses, ndefs);
            }
            _ => self.pop_push(op, nuses, ndefs),
        }
    }

    fn pop_push(&mut self, op: JSOp, nuses: usize, ndefs: usize) {
        let keep = self.stack.len().saturating_sub(nuses);
        self.stack.truncate(keep);
        for _ in 0..ndefs {
            self.stack.push(Origin {
                op: Some(op),
                name: None,
                num: None,
            });
        }
    }

    fn patch_top_name(&mut self, name_index: u32) {
        let name = self.atom_id(name_index);
        if let Some(t) = self.stack.last_mut() {
            t.name = name;
        }
    }

    fn patch_top_num(&mut self, n: u32) {
        if let Some(t) = self.stack.last_mut() {
            t.num = Some(n);
        }
    }
    fn atom_id(&mut self, index: u32) -> Option<NameId> {
        let gc = *self.script.gcthings.get(index as usize)?;
        if gc.is_other() {
            return None;
        }
        match self.source.object(gc) {
            SourceObject::String(s) => Some(self.names.intern(s.chars())),
            _ => None,
        }
    }

    fn prop_write(&mut self, name_index: u32) {
        if self.out.sum.top {
            return;
        }
        let Some(name) = self.atom_id(name_index) else {
            self.out.sum.saturate("prop-name");
            return;
        };
        let site = Site::new(self.sid, self.cur_pc);
        let cls = match self.recv_class.get(&site).and_then(|a| a.get().copied()) {
            Some(c) => FieldRecv::Cls(c),
            None if self.this_writes.contains(&site) => FieldRecv::This,
            None => FieldRecv::Unknown,
        };
        if !self.out.field_writes.contains(&(cls, name)) {
            if self.out.field_writes.len() >= FIELD_CAP {
                self.out.sum.saturate("field-cap");
                return;
            }
            self.out.field_writes.push((cls, name));
        }
    }

    fn gname_write(&mut self, name_index: u32) {
        if self.out.sum.top {
            return;
        }
        let Some(name) = self.atom_id(name_index) else {
            self.out.sum.saturate("gname-name");
            return;
        };
        if !self.out.sum.gname_writes.contains(&name) {
            if self.out.sum.gname_writes.len() >= GNAME_CAP {
                self.out.sum.saturate("gname-cap");
                return;
            }
            self.out.sum.gname_writes.push(name);
        }
    }
}

impl<'a> OpcodeVisitor for EffectWalk<'a> {
    fn before_op(&mut self, pc: Pc, op: JSOp, nuses: usize, ndefs: usize) {
        self.cur_pc = pc;
        self.sim_stack(pc, op, nuses, ndefs);
        if self.out.sum.top {
            return;
        }
        use JSOp::*;
        match op {
            // Classified by the operand-carrying methods below.
            SetProp | StrictSetProp | InitProp | InitHiddenProp | InitLockedProp | SetGName
            | StrictSetGName | InitGLexical | GetProp => {}
            // Element writes. The Init* forms hit the fresh literal under
            // construction, folded in conservatively.
            SetElem | StrictSetElem | InitElem | InitHiddenElem | InitLockedElem
            | InitElemArray | InitElemInc => self.out.sum.elems_write = true,
            SetAliasedVar => self.out.sum.env_write = true,
            Call | CallContent | CallIgnoresRv | New | NewContent => {
                self.out.calls.push(Site::new(self.sid, pc));
            }
            // The known-benign set: literals, stack shuffling, frame-local
            // reads/writes, arithmetic and comparison, control flow, fresh
            // allocations, and heap reads. Coercions and reads can reach
            // user code on exotic receivers, which is why consumers keep
            // only guarded/recoverable state on a summary's strength.
            Undefined | Null | False | True | Int32 | Zero | One | Int8 | Uint16 | Uint24
            | Double | String | Symbol | Void | Typeof | TypeofExpr | TypeofEq | Pos | Neg
            | BitNot | Not | BitOr | BitXor | BitAnd | Eq | Ne | StrictEq | StrictNe
            | StrictConstantEq | StrictConstantNe | Lt | Gt | Le | Ge | Instanceof | In | Lsh
            | Rsh | Ursh | Add | Sub | Inc | Dec | Mul | Div | Mod | Pow | NopIsAssignOp
            | ToPropertyKey | ToNumeric | ToString | IsNullOrUndefined | GlobalThis | GetElem
            | HasOwn | CheckIsObj | CheckObjCoercible | JumpTarget | LoopHead | Goto
            | JumpIfFalse | JumpIfTrue | And | Or | Coalesce | Case | Default | TableSwitch
            | Return | GetRval | SetRval | RetRval | CheckReturn | Throw | ThrowMsg
            | Uninitialized | InitLexical | CheckLexical | CheckAliasedLexical | CheckThis
            | GetGName | GetArg | GetFrameArg | GetLocal | ArgumentsLength | GetActualArg
            | GetAliasedVar | GetIntrinsic | Callee | SetArg | SetLocal | FunctionThis | Pop
            | PopN | Dup | Dup2 | DupAt | Swap | Pick | Unpick | Nop | Lineno
            | NopDestructuring | NewInit | NewObject | NewArray | Arguments | IsConstructing
            | Try | Exception | Finally | Lambda | DebugLeaveLexicalEnv | BindUnqualifiedGName => {}
            _ => self.out.sum.saturate(format!("{op:?}")),
        }
    }

    fn set_prop(&mut self, name_index: u32) {
        self.prop_write(name_index);
    }
    fn strict_set_prop(&mut self, name_index: u32) {
        self.prop_write(name_index);
    }
    fn init_prop(&mut self, name_index: u32) {
        self.prop_write(name_index);
    }
    fn init_hidden_prop(&mut self, name_index: u32) {
        self.prop_write(name_index);
    }
    fn init_locked_prop(&mut self, name_index: u32) {
        self.prop_write(name_index);
    }
    fn set_g_name(&mut self, name_index: u32) {
        self.gname_write(name_index);
    }
    fn strict_set_g_name(&mut self, name_index: u32) {
        self.gname_write(name_index);
    }
    fn init_g_lexical(&mut self, name_index: u32) {
        self.gname_write(name_index);
    }

    fn get_prop(&mut self, name_index: u32) {
        self.patch_top_name(name_index);
        if self.out.sum.top {
            return;
        }
        let pc = self.cur_pc;
        if let Some(name) = self.atom_id(name_index) {
            if self.accessor_names.contains(&name) {
                self.out.accessor_reads.push(Site::new(self.sid, pc));
            }
        }
    }

    fn get_g_name(&mut self, name_index: u32) {
        self.patch_top_name(name_index);
    }
    fn get_intrinsic(&mut self, name_index: u32) {
        self.patch_top_name(name_index);
    }
    fn get_arg(&mut self, argno: u16) {
        self.patch_top_num(u32::from(argno));
    }
    fn get_frame_arg(&mut self, argno: u16) {
        self.patch_top_num(u32::from(argno));
    }
    fn get_local(&mut self, localno: u32) {
        self.patch_top_num(localno);
    }
    fn get_aliased_var(&mut self, _hops: u16, slot: u32) {
        self.patch_top_num(slot);
    }

    fn dup_at(&mut self, n: u32) {
        let len = self.stack.len();
        let src = len
            .checked_sub(2 + n as usize)
            .and_then(|i| self.stack.get(i))
            .copied()
            .unwrap_or_default();
        if let Some(t) = self.stack.last_mut() {
            *t = src;
        }
    }
    fn pick(&mut self, n: u8) {
        let len = self.stack.len();
        if let Some(i) = len.checked_sub(1 + usize::from(n)) {
            let v = self.stack.remove(i);
            self.stack.push(v);
        }
    }
    fn unpick(&mut self, n: u8) {
        let len = self.stack.len();
        if len == 0 {
            return;
        }
        if let Some(i) = len.checked_sub(1 + usize::from(n)) {
            let v = self.stack.pop().unwrap();
            self.stack.insert(i.min(self.stack.len()), v);
        }
    }
}

fn origin_str(names: &Names, o: Origin) -> String {
    use std::fmt::Write as _;
    let Some(op) = o.op else {
        return "?".to_string();
    };
    let mut s = format!("{op:?}");
    if let Some(n) = o.name {
        let _ = write!(s, ":{}", String::from_utf16_lossy(names.get(n).chars()));
    } else if let Some(i) = o.num {
        let _ = write!(s, ":{i}");
    }
    s
}

fn native_summary(effect: NativeEffect, sum: &mut EffectSummary) {
    match effect {
        NativeEffect::Pure => {}
        NativeEffect::Elems => sum.elems_write = true,
        NativeEffect::Top => sum.saturate("native"),
    }
}

/// Fold one resolved callable into (deps, sum): scripts become fixpoint
/// dependencies, natives classify by table, the Array/typed-array ctors
/// are allocation-only.
fn fold_fn(
    sv: &Solver<'_>,
    f: super::types::FnId,
    deps: &mut Vec<ScriptId>,
    sum: &mut EffectSummary,
) {
    if let Some(s) = f.as_script() {
        if !deps.contains(&s) {
            deps.push(s);
        }
    } else if let Some(info) = sv.natives.get(f) {
        let name = sv.names.get(info.name);
        native_summary(
            builtins::native_effect(info.kind, name.chars(), info.result.is_some()),
            sum,
        );
    } else if f == super::types::FnId::ARRAY_CTOR || f.typed_array_kind().is_some() {
        // Allocation-only.
    } else {
        sum.saturate("callable");
    }
}

pub(super) fn emit_effect_summaries(
    sv: &mut Solver<'_>,
    facts: &mut LikelyFacts,
    plan: &LayoutPlan,
) {
    // Sites whose Write constraint names the script's own `this` as
    // receiver, for the `this_layouts` fallback when the site carries no
    // agreed class.
    let mut this_writes: HashSet<Site> = HashSet::default();
    for (ci, con) in sv.engine.cons.iter().enumerate() {
        if let super::engine::Constraint::Write { recv, pc, .. } = con {
            if matches!(recv, super::engine::CKey::This) {
                this_writes.insert(Site::new(sv.engine.con_script[ci], *pc));
            }
        }
    }
    // Phase A: per-script local walks.
    let mut sids: Vec<ScriptId> = sv
        .source
        .objects()
        .filter_map(|(oid, obj)| match obj {
            SourceObject::Script(_) => Some(ScriptId::new(oid.id())),
            _ => None,
        })
        .collect();
    sids.sort();
    let mut locals: HashMap<ScriptId, LocalEffects> = HashMap::default();
    for &sid in &sids {
        let SourceObject::Script(script) = sv.source.object(sid.source()) else {
            continue;
        };
        let mut walk = EffectWalk {
            sid,
            script,
            source: sv.source,
            names: &mut sv.names,
            recv_class: &sv.site_recv_class,
            this_writes: &this_writes,
            accessor_names: &facts.accessor_names,
            cur_pc: Pc::new(0),
            stack: Vec::new(),
            out: LocalEffects::default(),
        };
        if script.is_generator_or_async {
            walk.out.sum.saturate("generator");
        } else {
            walk = script.parser().visit(walk);
        }
        locals.insert(sid, walk.out);
    }

    // Call ops the scan lowered to non-Call constraints: elem-builtin
    // forms (`a.push(v)`) write elements; alloc forms (`new Array(n)`,
    // typed-array ctors) are allocation-only. Neither enters the call
    // census, so without these sets they mislabel as uncensused.
    let mut elem_sites: HashSet<Site> = HashSet::default();
    let mut alloc_call_sites: HashSet<Site> = HashSet::default();
    for (ci, con) in sv.engine.cons.iter().enumerate() {
        match con {
            super::engine::Constraint::ElemBuiltin { pc, .. } => {
                elem_sites.insert(Site::new(sv.engine.con_script[ci], *pc));
            }
            super::engine::Constraint::Alloc { pc, .. } => {
                alloc_call_sites.insert(Site::new(sv.engine.con_script[ci], *pc));
            }
            _ => {}
        }
    }

    // Phase B: map agreed write-site classes to planned key ranges, and
    // resolve every call edge once. Unresolvable edges saturate here.
    let mut deps: HashMap<ScriptId, Vec<ScriptId>> = HashMap::default();
    for &sid in &sids {
        let local = locals.get_mut(&sid).unwrap();
        let mut sum = std::mem::take(&mut local.sum);
        for &(recv, name) in &local.field_writes {
            let range = match recv {
                FieldRecv::Cls(c) => plan
                    .range_of(sv.group_of_class(c))
                    .map(|(lo, hi)| (LayoutKey::new(lo), LayoutKey::new(hi))),
                FieldRecv::This => facts.this_layouts.get(&sid).copied(),
                FieldRecv::Unknown => None,
            };
            sum.field_writes.push((range, name));
        }
        let mut dep_list: Vec<ScriptId> = Vec::new();
        for &site in &local.calls {
            if sum.top {
                break;
            }
            // An empty non-multi scripted set says the eval saw no
            // callables -- fall through to the native/apply tables rather
            // than saturating on it (a native callee often leaves an empty
            // scripted record beside its `site_native` answer). A multi
            // set saturates regardless (its ids are dropped on collapse).
            let scripted = sv
                .site_calls
                .get(&site)
                .filter(|f| f.is_multi() || !f.ids().is_empty());
            if let Some(fns) = scripted {
                if fns.is_multi() {
                    sum.saturate(format!("multi@{}", site.pc));
                } else {
                    for &f in fns.ids() {
                        fold_fn(sv, f, &mut dep_list, &mut sum);
                    }
                }
            } else if let Some(&f) = sv.site_native.get(&site).and_then(Agreed::get) {
                fold_fn(sv, f, &mut dep_list, &mut sum);
            } else if let Some((fns, _)) = sv.site_apply.get(&site) {
                if fns.is_multi() || fns.ids().is_empty() {
                    sum.saturate(format!("multi-apply@{}", site.pc));
                } else {
                    for &f in fns.ids() {
                        fold_fn(sv, f, &mut dep_list, &mut sum);
                    }
                }
            } else if let Some(&f) = sv.site_ctor_native.get(&site).and_then(Agreed::get) {
                fold_fn(sv, f, &mut dep_list, &mut sum);
            } else if elem_sites.contains(&site) {
                // The receiver resolved to nothing callable in the census:
                // the element-node effect below is the whole story.
            } else if alloc_call_sites.contains(&site) {
                // Allocation-only.
            } else if sv.site_calls.contains_key(&site) || sv.site_native.contains_key(&site) {
                let o = local
                    .callee_origin
                    .get(&site.pc)
                    .copied()
                    .unwrap_or_default();
                sum.saturate(format!("empty@{}({})", site.pc, origin_str(&sv.names, o)));
            } else {
                let o = local
                    .callee_origin
                    .get(&site.pc)
                    .copied()
                    .unwrap_or_default();
                sum.saturate(format!(
                    "uncensused@{}({})",
                    site.pc,
                    origin_str(&sv.names, o)
                ));
            }
            if elem_sites.contains(&site) {
                sum.elems_write = true;
            }
        }
        for &site in &local.accessor_reads {
            if sum.top {
                break;
            }
            match facts.call_sites.get(&site) {
                Some(CallResolution::Scripted(targets)) if !targets.is_empty() => {
                    for &t in targets {
                        if !dep_list.contains(&t) {
                            dep_list.push(t);
                        }
                    }
                }
                _ => sum.saturate("accessor"),
            }
        }
        local.sum = sum;
        deps.insert(sid, dep_list);
    }

    // Phase C: transitive fixpoint. Monotone joins over a capped lattice.
    let mut rev: HashMap<ScriptId, Vec<ScriptId>> = HashMap::default();
    for &sid in &sids {
        for &d in &deps[&sid] {
            rev.entry(d).or_default().push(sid);
        }
    }
    let mut summaries: HashMap<ScriptId, EffectSummary> = sids
        .iter()
        .map(|&sid| (sid, locals[&sid].sum.clone()))
        .collect();
    let mut work: Vec<ScriptId> = sids.clone();
    let mut queued: HashSet<ScriptId> = sids.iter().copied().collect();
    while let Some(sid) = work.pop() {
        queued.remove(&sid);
        let mut joined = locals[&sid].sum.clone();
        for &d in &deps[&sid] {
            if joined.top {
                break;
            }
            let Some(ds) = summaries.get(&d) else {
                // A dep outside the walked source (should not happen):
                // nothing is known about it.
                joined.saturate("dep-missing");
                break;
            };
            join_into(&mut joined, ds);
        }
        if summaries[&sid] != joined {
            summaries.insert(sid, joined);
            if let Some(callers) = rev.get(&sid) {
                for &c in callers {
                    if queued.insert(c) {
                        work.push(c);
                    }
                }
            }
        }
    }
    facts.script_effects = summaries;
}

fn join_into(dst: &mut EffectSummary, src: &EffectSummary) {
    if src.top {
        dst.saturate(format!("dep:{}", src.top_why.as_deref().unwrap_or("?")));
        return;
    }
    for fw in &src.field_writes {
        if !dst.field_writes.contains(fw) {
            if dst.field_writes.len() >= FIELD_CAP {
                dst.saturate("field-cap");
                return;
            }
            dst.field_writes.push(*fw);
        }
    }
    for g in &src.gname_writes {
        if !dst.gname_writes.contains(g) {
            if dst.gname_writes.len() >= GNAME_CAP {
                dst.saturate("gname-cap");
                return;
            }
            dst.gname_writes.push(*g);
        }
    }
    dst.elems_write |= src.elems_write;
    dst.env_write |= src.env_write;
}
