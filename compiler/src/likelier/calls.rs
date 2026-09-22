/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Call binding, contexts, construct semantics, apply delegation, escape.
//!
//! A context is one interned id (a bounded call string), not a graph copy --
//! nothing is cloned. Binding a call reads the argument cells (subscribing,
//! so growth re-binds) and raises the callee's per-ctx Arg/This rows; the
//! callee's constraints are instantiated lazily the first time a ctx
//! reaches it. Degradations are explicit and censused, never silent:
//! depth cap, callee cap, recursion collapse, global budget -- all bind
//! into the callee's generic context instead.

use super::engine::{CellKey, ConId, Constraint, SEED};
use super::stats::Stats;
use super::types::{BoundedFnSet, CtxId, FnId, ObjType, TypeSet, CTX0};
use super::Solver;
use crate::constants::{
    CALLEE_CAP, CTX_BUDGET, CTX_DEPTH_CAP, MAX_TRACKED_FORMALS, TABLE_MEMBER_CAP,
};
use crate::facts::CallForm;
use crate::ids::{FormalIndex, Pc, ScriptId, Site};
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;

/// One frame of an interned call string. The chain of `parent` links from
/// a `CtxId` back to `CTX0` spells out the calls that reached it.
struct CtxFrame {
    parent: CtxId,
    /// The callee script this frame entered. Not "the callee" of anything
    /// -- a script calls many others, and each such call gets its own
    /// frame; this is the one call this frame stands for. Recursion
    /// collapse walks the parent chain looking for a frame that already
    /// entered the same script. `None` in frame 0, the generic context.
    callee: Option<ScriptId>,
    depth: u8,
}

pub struct Ctxs {
    frames: Vec<CtxFrame>,
    ids: HashMap<(CtxId, Site, ScriptId), CtxId>,
    pub depth_cap: u8,
    pub callee_cap: usize,
    pub budget: u64,
}

impl Default for Ctxs {
    fn default() -> Self {
        Self::new()
    }
}

impl Ctxs {
    pub fn new() -> Ctxs {
        Ctxs {
            // Frame 0 is the generic context.
            frames: vec![CtxFrame {
                parent: CTX0,
                callee: None,
                depth: 0,
            }],
            ids: HashMap::default(),
            depth_cap: CTX_DEPTH_CAP,
            callee_cap: CALLEE_CAP,
            budget: CTX_BUDGET,
        }
    }

    /// Mint (or reuse) the context for entering `callee` from `site` at
    /// `ctx`. Returns CTX0 (with a census tick) on any degradation.
    fn push(&mut self, ctx: CtxId, site: Site, callee: ScriptId, stats: &mut Stats) -> CtxId {
        // Recursion collapse: if the callee already appears in the chain,
        // reuse the context it was entered at (SCCs context-insensitive
        // internally).
        let mut cur = ctx;
        while cur != CTX0 {
            let f = &self.frames[cur.0 as usize];
            if f.callee == Some(callee) {
                stats.call_ctx_degraded_recursion += 1;
                return cur;
            }
            cur = f.parent;
        }
        let depth = self.frames[ctx.0 as usize].depth;
        if depth >= self.depth_cap {
            stats.call_ctx_degraded_depth += 1;
            return CTX0;
        }
        if stats.ctxs_spent >= self.budget {
            stats.call_ctx_degraded_budget += 1;
            return CTX0;
        }
        if let Some(&c) = self.ids.get(&(ctx, site, callee)) {
            return c;
        }
        let c = CtxId(u32::try_from(self.frames.len()).unwrap());
        self.frames.push(CtxFrame {
            parent: ctx,
            callee: Some(callee),
            depth: depth + 1,
        });
        self.ids.insert((ctx, site, callee), c);
        c
    }

    /// Every (caller ctx, site) edge that mints a context, by context.
    pub fn enter_sites(&self) -> HashMap<CtxId, Vec<Site>> {
        let mut out: HashMap<CtxId, Vec<Site>> = HashMap::default();
        for (&(_, site, _), &c) in &self.ids {
            out.entry(c).or_default().push(site);
        }
        out
    }

    /// Human-readable provenance of a context, for the site tracer: its
    /// depth, parent, and every (caller-ctx, site) edge that mints it.
    pub fn describe(&self, ctx: CtxId) -> String {
        if ctx == CTX0 {
            return "generic".to_string();
        }
        let f = &self.frames[ctx.0 as usize];
        let mut vias: Vec<String> = self
            .ids
            .iter()
            .filter(|&(_, &v)| v == ctx)
            .map(|(&(p, site, _), _)| format!("ctx {} at {site}", p.0))
            .collect();
        vias.sort();
        format!(
            "depth {} parent {} via [{}]",
            f.depth,
            f.parent.0,
            vias.join("; ")
        )
    }
}

/// One call constraint being evaluated: who is calling, at which context,
/// on behalf of which firing, and where the result goes. Every binding step
/// below needs all four, and threading them as one value is what lets the
/// three call shapes (ordinary call, `new`, `.call`/`.apply`) share their
/// binding code instead of restating it.
#[derive(Clone, Copy)]
struct CallAt {
    /// The calling script and the context it is being evaluated at.
    script: ScriptId,
    ctx: CtxId,
    /// The firing doing the reading, so reads subscribe to it.
    user: (ConId, CtxId),
    /// Where the call's result goes, in the caller's frame.
    ret: super::engine::CKey,
}

impl Solver<'_> {
    /// Bind the caller's arguments into `f`'s formal rows at `cx`, dropping
    /// the first `skip` (a `.call` site's leading receiver, which is the
    /// forwarded `this` rather than a formal).
    fn bind_args(
        &mut self,
        at: CallAt,
        f: ScriptId,
        cx: CtxId,
        args: &[super::engine::CKey],
        skip: usize,
    ) {
        for (i, a) in args.iter().skip(skip).enumerate() {
            let src = self.engine.resolve(at.script, at.ctx, *a);
            let v = self.engine.read(src, at.user);
            let arg = FormalIndex::new(u32::try_from(i).unwrap());
            self.note_arg_fn(f, arg, &v);
            let dst = self.engine.cell(CellKey::Arg {
                script: f,
                arg,
                ctx: cx,
            });
            self.engine.raise(dst, &v, at.user);
        }
    }

    /// Bind `tk` into `f`'s receiver row at `cx`, unless the this-assertion
    /// refuses it. A caller handing over its own `this` also records the
    /// delegation edge, so `f`'s this-writes attribute to the caller's home
    /// classes.
    ///
    /// `method_recv`: `tk` is a method call's receiver (`x.m()`), so a
    /// nullish value never reaches the callee -- the property access
    /// throws first, in both modes. Stripping null/undefined here is what
    /// keeps a null-seeded field (`this.root_ = null`) from widening the
    /// callee's This cell past the object claim its every actual
    /// invocation satisfies. An explicit `.call/.apply` this is NOT this
    /// shape: a strict callee really can observe null there, so those
    /// sites pass false.
    fn bind_this(
        &mut self,
        at: CallAt,
        f: ScriptId,
        cx: CtxId,
        tk: super::engine::CKey,
        method_recv: bool,
    ) {
        if tk == super::engine::CKey::This {
            self.this_deleg_add(at.script, f);
        }
        let src = self.engine.resolve(at.script, at.ctx, tk);
        let mut v = self.engine.read(src, at.user);
        if method_recv {
            v.prims = v.prims - (crate::opsem::PRIM_NULL | crate::opsem::PRIM_UNDEFINED);
            if v.is_empty() {
                // A provably-nullish receiver: the call never happens.
                return;
            }
        }
        // A worse-than-asserted receiver (AnyObject/AnyOf into a pinned
        // method) must not leave the context's This EMPTY -- an empty This
        // reads as "never invoked" and every this-dependent value in the
        // body computes nothing at this context (the callee's return dies
        // with it). The per-site context's cells are separate from CTX0's,
        // so binding here cannot destroy the assertion the refusal
        // protects: a single-owner pin binds its asserted class (strictly
        // better evidence than the lost receiver), a conflicted pin (a
        // genuinely shared method) binds the receiver itself.
        let bound = if self.bind_this_ok(f, &v) {
            v
        } else if let Some(&owner) = self.this_pin.get(&f).and_then(super::types::Agreed::get) {
            TypeSet {
                obj: ObjType::ClassAny(owner),
                ..TypeSet::default()
            }
        } else {
            v
        };
        let dst = self.engine.cell(CellKey::This { script: f, ctx: cx });
        self.engine.raise(dst, &bound, at.user);
    }

    /// Propagate `f`'s return at `cx` into the call's result.
    fn bind_ret(&mut self, at: CallAt, f: ScriptId, cx: CtxId) {
        let ret_src = self.engine.cell(CellKey::Ret { script: f, ctx: cx });
        let v = self.engine.read(ret_src, at.user);
        let ret_dst = self.engine.resolve(at.script, at.ctx, at.ret);
        self.engine.raise(ret_dst, &v, at.user);
    }

    /// Raise the result of calling a callee that is not a script: a modeled
    /// native's spec mask, or unknown evidence for anything unmodeled.
    fn raise_builtin_ret(&mut self, at: CallAt, f: FnId, args: &[super::engine::CKey]) {
        let v = if f.native_index().is_some() {
            let ai = self.args_integral(at.script, at.ctx, args, at.user);
            self.native_ret(f, ai)
        } else {
            TypeSet::unknown_evidence()
        };
        let ret_dst = self.engine.resolve(at.script, at.ctx, at.ret);
        self.engine.raise(ret_dst, &v, at.user);
    }
}

impl Solver<'_> {
    /// Every argument at the site is integrally ranged (numeric prims
    /// only, range at or below I53) -- the integral-preserving native
    /// condition. Reads subscribe, so a later widening re-evals the call.
    fn args_integral(
        &mut self,
        script: ScriptId,
        ctx: CtxId,
        args: &[super::engine::CKey],
        user: (ConId, CtxId),
    ) -> bool {
        args.iter().all(|&a| {
            let cell = self.engine.resolve(script, ctx, a);
            let ts = self.engine.read(cell, user);
            ts.prims
                .subset_of(crate::opsem::PRIM_INT32 | crate::opsem::PRIM_DOUBLE)
                && ts.fns.is_empty()
                && ts.obj == ObjType::Empty
                && ts.range <= super::types::Range::I53
        })
    }

    pub(super) fn eval_call(&mut self, con: ConId, ctx: CtxId) -> bool {
        let script = self.engine.con_script[con.0 as usize];
        let user = (con, ctx);
        match self.engine.cons[con.0 as usize].clone() {
            Constraint::Call {
                callee,
                this_,
                args,
                ret,
                pc,
                construct,
            } => {
                let at = CallAt {
                    script,
                    ctx,
                    user,
                    ret,
                };
                let c = self.engine.resolve(script, ctx, callee);
                let cts = self.engine.read(c, user);
                self.note_site_calls(script, pc, &cts);
                if construct {
                    self.note_site_ctor_native(script, pc, &cts.fns);
                } else {
                    self.note_site_native(script, pc, &cts.fns);
                }
                let region_fed = matches!(callee, super::engine::CKey::Var(v)
                    if self.region_calls.contains(&(script, v)));
                if region_fed {
                    // Region-resolved dispatch: the callee set here came
                    // from a region's method tables (`region_methods`)
                    // rather than from a resolved function value, so it is
                    // a guess at which of several sibling classes' methods
                    // this site reaches. The set itself is already recorded
                    // as the site's guard chain above; what is left is
                    // whether to bind arguments into those callees, and at
                    // which context.
                    //
                    // Binding is worth doing -- the facts it produces inside
                    // the guessed bodies are what makes the spliced arms
                    // worth emitting -- but neither obvious context works:
                    //
                    //   - The generic context (CTX0) is shared by every
                    //     caller of the callee, so a guessed argument
                    //     joined there is visible to every other call of
                    //     that function, forever. One wrong guess widens
                    //     the callee's formals for the whole program.
                    //   - Chaining off the caller's own context is precise,
                    //     but a region dispatch fans out to every member
                    //     class, and each of those may itself dispatch
                    //     through a region. The product exhausts the
                    //     context budget, and once the budget is gone
                    //     `Ctxs::push` degrades *everything* after it to
                    //     CTX0 -- so the precise choice ends up causing the
                    //     same whole-program widening the shared row would
                    //     have, just later and less predictably.
                    //
                    // So: a depth-1 context parented at the generic one,
                    // minted per (site, target). The guess stays contained
                    // in a row nothing else reads, and the budget sees a
                    // flat cost rather than a multiplied one. A target the
                    // budget refuses simply does not bind.
                    //
                    // Every resolved target binds -- the fn-set bound and
                    // the region cap are the population gates, and the ctx
                    // budget is the cost gate; a second, tighter cap here
                    // would starve any closed dispatch wider than it,
                    // since none of its callees' arguments would flow.
                    if !cts.fns.is_multi() {
                        for f in cts.fns.ids().to_vec() {
                            let Some(f) = f.as_script() else {
                                self.raise_builtin_ret(at, f, &args);
                                continue;
                            };
                            let cx =
                                self.ctxs
                                    .push(CTX0, Site::new(script, pc), f, &mut self.stats);
                            if cx == CTX0 {
                                self.raise_unknown_ret(script, ctx, ret, user);
                                continue;
                            }
                            if self.engine.instantiate(f, cx) {
                                self.stats.ctxs_spent += 1;
                            }
                            self.bind_args(at, f, cx, &args, 0);
                            if !construct {
                                if let Some(tk) = this_ {
                                    self.bind_this(at, f, cx, tk, true);
                                }
                            }
                            self.bind_ret(at, f, cx);
                        }
                    } else {
                        // Megamorphic or over-cap region dispatch: the
                        // call still executes.
                        self.raise_unknown_ret(script, ctx, ret, user);
                    }
                    return true;
                }
                // A resolved fn set binds even when the obj part is
                // AnyObject (method-union callees ride Any-valued reads);
                // only a truly unusable callee escapes the arguments.
                // An executed-but-unresolved call raises the unknown
                // evidence bit into its result, never nothing: an Empty
                // result reads as "no value ever arrived here", so a
                // consumer would claim whatever its other, numeric-only
                // writers said and miss on every call result.
                if cts.fns.is_multi() || (cts.fns.is_empty() && cts.obj == ObjType::AnyObject) {
                    // Fn-table dispatch: a multi callee read
                    // off a snapshot fn-table's elems still binds the join
                    // of the site's arg profiles into every member's Arg
                    // row at the generic context. Dispatch stays opaque
                    // (unknown ret, args escape as before) -- only the
                    // members' formals learn.
                    if cts.fns.is_multi() {
                        if let super::engine::CKey::Var(v) = callee {
                            if let Some(&rk) = self.elems_callee_vars.get(&(script, v)) {
                                let rcell = self.engine.resolve(script, ctx, rk);
                                let rts = self.engine.read(rcell, user);
                                if let ObjType::One(a) = rts.obj {
                                    if self.table_members.contains_key(&a) {
                                        self.bind_table_args(a, script, ctx, &args, user);
                                    }
                                }
                            }
                        }
                    }
                    self.raise_unknown_ret(script, ctx, ret, user);
                    for a in args.iter() {
                        let ac = self.engine.resolve(script, ctx, *a);
                        let v = self.engine.read(ac, user);
                        self.do_escape(&v, user);
                    }
                    return true;
                }
                if cts.fns.is_empty() && matches!(cts.obj, ObjType::AnyOf(_)) {
                    self.raise_unknown_ret(script, ctx, ret, user);
                    return true;
                }
                let targets = cts.fns.ids().to_vec();
                let poly =
                    targets.iter().filter(|f| !f.is_builtin()).count() > self.ctxs.callee_cap;
                for f in targets {
                    if f.native_index().is_some() {
                        // A named native: the call result is spec-modeled
                        // (or unknown); constructing one yields an object
                        // we do not model. `Object.defineProperty` is the
                        // one native with modeled heap semantics: it feeds
                        // the class accessor table.
                        let v = if construct {
                            TypeSet::unknown_evidence()
                        } else if self.is_define_property(f) {
                            self.eval_define_property(script, ctx, pc, &args, user)
                        } else {
                            let ai = self.args_integral(script, ctx, &args, user);
                            self.native_ret(f, ai)
                        };
                        let ret_dst = self.engine.resolve(script, ctx, ret);
                        self.engine.raise(ret_dst, &v, user);
                        continue;
                    }
                    let Some(f) = f.as_script() else {
                        // A builtin constructor value (`var Vector = Array`):
                        // allocation semantics at this site, call == construct.
                        let (is_array, ta) = if f == FnId::ARRAY_CTOR {
                            (true, None)
                        } else {
                            (false, f.typed_array_kind())
                        };
                        let abs = self.intern_alloc(script, pc, ctx, None, is_array, ta);
                        let ret_dst = self.engine.resolve(script, ctx, ret);
                        self.engine.raise(ret_dst, &TypeSet::obj_one(abs), user);
                        continue;
                    };
                    let cx = self.enter(ctx, script, pc, f, poly);
                    self.bind_args(at, f, cx, &args, 0);
                    if construct {
                        let this_cell = self.engine.cell(CellKey::This { script: f, ctx: cx });
                        let ret_dst = self.engine.resolve(script, ctx, ret);
                        self.constructed.insert(f);
                        // Shared-generated ctors: the site's snapshot-
                        // resolved per-prototype class, else the script-
                        // keyed identity.
                        let class = match self.site_ctor_class.get(&Site::new(script, pc)) {
                            Some(&c) => c,
                            None => self.class_for_fn(f),
                        };
                        let abs = self.intern_alloc(script, pc, ctx, Some(class), false, None);
                        let t = TypeSet::obj_one(abs);
                        self.engine.raise(this_cell, &t, user);
                        let ret_src = self.engine.cell(CellKey::Ret { script: f, ctx: cx });
                        let rv = self.engine.read(ret_src, user);
                        if self.tables.explicit_ret.contains(&f) {
                            // Object-returning constructor: `new F()` yields
                            // F's return when it is an object (NVector); the
                            // `this` allocation only where an observed
                            // primitive return path exists (the unknown bit
                            // is not one -- construct semantics box it to an
                            // object either way). Both activations are
                            // monotone.
                            let mut objpart = TypeSet {
                                fns: rv.fns.clone(),
                                obj: rv.obj,
                                ..TypeSet::default()
                            };
                            if !rv.prims.is_empty() {
                                objpart.join_from(
                                    &t,
                                    &self.engine.abs_labels,
                                    &mut self.engine.sink,
                                );
                            }
                            self.engine.raise(ret_dst, &objpart, user);
                        } else {
                            self.engine.raise(ret_dst, &t, user);
                        }
                    } else {
                        if let Some(tk) = this_ {
                            self.bind_this(at, f, cx, tk, true);
                        }
                        self.bind_ret(at, f, cx);
                    }
                }
                true
            }
            Constraint::Apply {
                target,
                args,
                arg1_is_arguments,
                ret,
                pc,
                form,
            } => {
                let at = CallAt {
                    script,
                    ctx,
                    user,
                    ret,
                };
                let t = self.engine.resolve(script, ctx, target);
                let tts = self.engine.read(t, user);
                self.note_site_apply(script, ctx, pc, &tts.fns, form);
                if tts.fns.is_multi()
                    || (tts.fns.is_empty()
                        && matches!(tts.obj, ObjType::AnyObject | ObjType::AnyOf(_)))
                {
                    // Fn-table dispatch through an apply form
                    // (`action[0].call(scope, data)`): a multi target read
                    // off a known table's elems still binds the site's arg
                    // profile and thisArg into every member's rows, so the
                    // handler bodies stop reading Empty formals. Dispatch
                    // stays opaque (unknown ret), and each member binds in
                    // a depth-1 context parented at the generic one -- the
                    // region-dispatch containment rule (a shared CTX0 row
                    // would widen every caller of the member forever, and
                    // caller-chained contexts fan out past the budget).
                    if tts.fns.is_multi() && form == CallForm::Call {
                        if let super::engine::CKey::Var(v) = target {
                            if let Some(&rk) = self.elems_callee_vars.get(&(script, v)) {
                                let rcell = self.engine.resolve(script, ctx, rk);
                                let rts = self.engine.read(rcell, user);
                                let members: Vec<FnId> = match rts.obj {
                                    ObjType::One(a) => self
                                        .table_members
                                        .get(&a)
                                        .map_or_else(Vec::new, |m| m.iter().copied().collect()),
                                    ObjType::ClassAny(c) => self
                                        .class_table_members
                                        .get(&c)
                                        .map_or_else(Vec::new, |m| m.iter().copied().collect()),
                                    _ => Vec::new(),
                                };
                                let mut members = members;
                                members.sort_unstable();
                                for f in members {
                                    let Some(f) = f.as_script() else {
                                        continue;
                                    };
                                    let cx = self.ctxs.push(
                                        CTX0,
                                        Site::new(script, pc),
                                        f,
                                        &mut self.stats,
                                    );
                                    if cx == CTX0 {
                                        continue;
                                    }
                                    if self.engine.instantiate(f, cx) {
                                        self.stats.ctxs_spent += 1;
                                    }
                                    if let Some(&recv) = args.first() {
                                        self.bind_this(at, f, cx, recv, false);
                                    }
                                    self.bind_args(at, f, cx, &args, 1);
                                }
                            }
                        }
                    }
                    self.raise_unknown_ret(script, ctx, ret, user);
                    return true;
                }
                let targets = tts.fns.ids().to_vec();
                let poly = targets.len() > self.ctxs.callee_cap;
                for f in targets {
                    let Some(f) = f.as_script() else {
                        self.raise_builtin_ret(at, f, &args);
                        continue;
                    };
                    let cx = self.enter(ctx, script, pc, f, poly);
                    if let Some(&recv) = args.first() {
                        self.bind_this(at, f, cx, recv, false);
                    }
                    if form == CallForm::Call {
                        self.bind_args(at, f, cx, &args, 1);
                    } else if arg1_is_arguments {
                        // `T.apply(this, arguments)`: forward the caller's
                        // own argument rows.
                        for i in 0..MAX_TRACKED_FORMALS {
                            let arg = FormalIndex::new(i);
                            let src = self.engine.cell(CellKey::Arg { script, arg, ctx });
                            let v = self.engine.read(src, user);
                            let dst = self.engine.cell(CellKey::Arg {
                                script: f,
                                arg,
                                ctx: cx,
                            });
                            self.engine.raise(dst, &v, user);
                        }
                    }
                    self.bind_ret(at, f, cx);
                }
                true
            }
            _ => false,
        }
    }

    /// Fn-table arg-binding: raise the dispatch site's arg
    /// reads into the table's per-index join rows; standing links fan
    /// each row into every member's Arg cell at the generic context.
    /// Reads subscribe, so arg growth re-binds; `link` propagates the
    /// current row into late-arriving members, so member growth is
    /// monotone too.
    fn bind_table_args(
        &mut self,
        a: super::types::AbsId,
        script: ScriptId,
        ctx: CtxId,
        args: &[super::engine::CKey],
        user: (ConId, CtxId),
    ) {
        self.table_bound.entry(a).or_insert(0);
        self.install_table_links(a);
        for (i, k) in args.iter().enumerate().take(MAX_TRACKED_FORMALS as usize) {
            let src = self.engine.resolve(script, ctx, *k);
            let v = self.engine.read(src, user);
            let j = self.engine.cell(CellKey::TableArgJoin {
                abs: a,
                arg: FormalIndex::new(u32::try_from(i).unwrap()),
            });
            self.engine.raise(j, &v, user);
        }
    }

    /// Whether native id `f` is the modeled `Object.defineProperty`.
    fn is_define_property(&self, f: FnId) -> bool {
        self.natives.get(f).is_some_and(|i| {
            i.kind == super::builtins::NativeKind::Bare && i.name == self.names_of.define_property
        })
    }

    /// Model `Object.defineProperty(target, "name", {get, set})`: register
    /// the accessor pair on the target's class (the target is a prototype
    /// abstraction or a class-owned concrete prototype), bind the bodies'
    /// `this`, and re-fire same-name heap constraints so evaluations that
    /// ran before registration route through the accessor. Returns the
    /// call result (the target).
    fn eval_define_property(
        &mut self,
        script: ScriptId,
        ctx: CtxId,
        pc: Pc,
        args: &[super::engine::CKey],
        user: (ConId, CtxId),
    ) -> TypeSet {
        let tts = if let Some(&t) = args.first() {
            let c = self.engine.resolve(script, ctx, t);
            self.engine.read(c, user)
        } else {
            TypeSet::default()
        };
        let ret = if tts.is_empty() {
            TypeSet::unknown_evidence()
        } else {
            tts.clone()
        };
        if args.len() != 3 {
            return ret;
        }
        let Some(&name) = self.tables.call_str_arg1.get(&Site::new(script, pc)) else {
            return ret;
        };
        let ObjType::One(t) = tts.obj else {
            return ret;
        };
        let info = &self.heap[t];
        let Some(class) = info.proto_of.or(info.owner_class) else {
            return ret;
        };
        let dcell = self.engine.resolve(script, ctx, args[2]);
        let dts = self.engine.read(dcell, user);
        let ObjType::One(d) = dts.obj else {
            return ret;
        };
        self.ensure_seeded(d);
        let n_get = self.names_of.get;
        let n_set = self.names_of.set;
        let gcell = self.field_cell(d, n_get);
        let g = self.engine.read(gcell, user);
        let scell = self.field_cell(d, n_set);
        let s = self.engine.read(scell, user);
        let pick = |ts: &TypeSet| -> Option<ScriptId> {
            match ts.fns.ids() {
                [f] if !ts.fns.is_multi() => f.as_script(),
                _ => None,
            }
        };
        self.accessor_add(class, name, pick(&g), pick(&s));
        ret
    }

    /// Monotone accessor-table install. A conflicting re-install poisons
    /// the entry (removed; never re-registered). New information re-fires
    /// every same-name Read/Write constraint at its live contexts --
    /// registrations are rare (a handful per corpus), so the cons scan is
    /// cheap.
    fn accessor_add(
        &mut self,
        c: super::types::ClassId,
        name: super::types::NameId,
        getter: Option<ScriptId>,
        setter: Option<ScriptId>,
    ) {
        if getter.is_none() && setter.is_none() {
            return;
        }
        if self.accessor_poisoned.contains(&(c, name)) {
            return;
        }
        let cur = self
            .accessors
            .get(&(c, name))
            .copied()
            .unwrap_or((None, None));
        fn merge(
            old: Option<ScriptId>,
            new: Option<ScriptId>,
        ) -> Result<(Option<ScriptId>, bool), ()> {
            match (old, new) {
                (None, Some(n)) => Ok((Some(n), true)),
                (Some(o), Some(n)) if o != n => Err(()),
                (o, _) => Ok((o, false)),
            }
        }
        let (Ok((g2, cg)), Ok((s2, cs))) = (merge(cur.0, getter), merge(cur.1, setter)) else {
            self.accessors.remove(&(c, name));
            self.accessor_poisoned.insert((c, name));
            return;
        };
        if !cg && !cs {
            return;
        }
        self.accessors.insert((c, name), (g2, s2));
        for m in [getter, setter].into_iter().flatten() {
            let this_cell = self.engine.cell(CellKey::This {
                script: m,
                ctx: CTX0,
            });
            let ts = TypeSet {
                obj: ObjType::ClassAny(c),
                ..TypeSet::default()
            };
            self.engine.raise(this_cell, &ts, (SEED, CTX0));
        }
        for ci in 0..self.engine.cons.len() {
            let hit = match &self.engine.cons[ci] {
                Constraint::Read { name: n, .. } | Constraint::Write { name: n, .. } => *n == name,
                _ => false,
            };
            if hit {
                let csid = self.engine.con_script[ci];
                for cx in self
                    .engine
                    .live_ctxs
                    .get(&csid)
                    .cloned()
                    .unwrap_or_default()
                {
                    self.engine
                        .enqueue(super::engine::ConId(u32::try_from(ci).unwrap()), cx);
                }
            }
        }
    }

    /// Record scripted fn ids arriving at a callee's arg row (from the
    /// Site's value, before the row join saturates), and forward them to
    /// any tables this row is known to feed.
    pub(super) fn note_arg_fn(&mut self, callee: ScriptId, arg: FormalIndex, v: &TypeSet) {
        if v.fns.is_multi() || v.fns.ids().is_empty() {
            return;
        }
        let mut fresh = false;
        for &id in v.fns.ids() {
            if !id.is_builtin() {
                fresh |= self
                    .arg_fn_members
                    .entry((callee, arg))
                    .or_default()
                    .insert(id);
            }
        }
        if !fresh {
            return;
        }
        for a in self
            .arg_row_tables
            .get(&(callee, arg))
            .cloned()
            .unwrap_or_default()
        {
            let ids: Vec<FnId> = v
                .fns
                .ids()
                .iter()
                .copied()
                .filter(|&f| !f.is_builtin())
                .collect();
            self.add_table_members(a, &ids);
        }
    }

    /// Insert members into a table's list (capped, censused) and extend
    /// the standing links if the table already has dispatch sites.
    pub(super) fn add_table_members(&mut self, a: super::types::AbsId, ids: &[FnId]) {
        let e = self.table_members.entry(a).or_default();
        for &f in ids {
            if e.len() >= TABLE_MEMBER_CAP {
                if !e.contains(&f) {
                    self.stats.table_members_capped += 1;
                }
                continue;
            }
            e.insert(f);
        }
        if let Some(c) = self.heap[a].class {
            let ce = self.class_table_members.entry(c).or_default();
            for &f in ids {
                if ce.len() >= TABLE_MEMBER_CAP {
                    break;
                }
                ce.insert(f);
            }
        }
        self.install_table_links(a);
    }

    /// Install join-row -> member-Arg links for members not yet linked
    /// (no-op unless the table has dispatch sites and members grew).
    pub(super) fn install_table_links(&mut self, a: super::types::AbsId) {
        let Some(linked) = self.table_bound.get(&a).copied() else {
            return;
        };
        let members: Vec<FnId> = self.table_members.get(&a).map_or_else(Vec::new, |m| {
            let mut v: Vec<FnId> = m.iter().copied().collect();
            v.sort_unstable();
            v
        });
        if members.len() <= linked {
            return;
        }
        for &f in &members {
            let Some(f) = f.as_script() else {
                continue;
            };
            for i in 0..MAX_TRACKED_FORMALS {
                let arg = FormalIndex::new(i);
                let j = self.engine.cell(CellKey::TableArgJoin { abs: a, arg });
                let dst = self.engine.cell(CellKey::Arg {
                    script: f,
                    arg,
                    ctx: CTX0,
                });
                self.engine.link(j, dst);
            }
        }
        self.table_bound.insert(a, members.len());
    }

    /// An executed-but-unresolved call result: raise the unknown evidence
    /// bit into the return destination (see `TypeSet::unknown`).
    fn raise_unknown_ret(
        &mut self,
        script: ScriptId,
        ctx: CtxId,
        ret: super::engine::CKey,
        user: (ConId, CtxId),
    ) {
        let ret_dst = self.engine.resolve(script, ctx, ret);
        self.engine
            .raise(ret_dst, &TypeSet::unknown_evidence(), user);
    }

    /// Enter callee `f` from `(script, pc)` at `ctx`: mint/reuse the context,
    /// count the budget, instantiate the callee's rows there.
    fn enter(&mut self, ctx: CtxId, script: ScriptId, pc: Pc, f: ScriptId, poly: bool) -> CtxId {
        let cx = if poly {
            self.stats.call_ctx_degraded_polymorphic += 1;
            CTX0
        } else {
            self.ctxs
                .push(ctx, Site::new(script, pc), f, &mut self.stats)
        };
        if self.engine.instantiate(f, cx) && cx != CTX0 {
            self.stats.ctxs_spent += 1;
        }
        cx
    }

    /// The this-assertion filter: never bind a worse-than-asserted receiver
    /// (AnyObject) into a homed method -- the polymorphic-dispatch site's
    /// lost receiver must not destroy the body's asserted precision.
    /// Precise receivers bind normally.
    fn bind_this_ok(&self, f: ScriptId, v: &TypeSet) -> bool {
        !(self.this_pin.contains_key(&f) && matches!(v.obj, ObjType::AnyObject | ObjType::AnyOf(_)))
    }

    /// Escape: function values reaching an untracked sink get Any joined
    /// into their generic-context args and this, once.
    pub(super) fn do_escape(&mut self, v: &TypeSet, user: (ConId, CtxId)) {
        for &f in v.fns.ids().to_vec().iter() {
            let Some(script) = f.as_script() else {
                continue;
            };
            if !self.escaped.insert(f) {
                continue;
            }
            if self.escape_log.len() < 20 {
                self.escape_log.push((f, user.0));
            }
            // Escaped bindings are executed-but-unresolved, not "every value
            // was seen": fabricated definite prim bits (TypeSet::any())
            // poisoned every field cell an escaped method writes through
            // `this`, indistinguishable from real string/bool evidence.
            let any = TypeSet::unresolved();
            for i in 0..MAX_TRACKED_FORMALS {
                let c = self.engine.cell(CellKey::Arg {
                    script,
                    arg: FormalIndex::new(i),
                    ctx: CTX0,
                });
                self.engine.raise(c, &any, (SEED, CTX0));
            }
            let c = self.engine.cell(CellKey::This { script, ctx: CTX0 });
            self.engine.raise(c, &any, (SEED, CTX0));
        }
    }

    fn note_site_calls(&mut self, script: ScriptId, pc: Pc, cts: &TypeSet) {
        // Output-table join: sink drops are diagnostics-only anyway.
        let mut scratch = Vec::new();
        let scripted = cts.fns.scripted_only(&mut scratch);
        let site = Site::new(script, pc);
        let e = self.site_calls.entry(site).or_default();
        e.join_from(&scripted, &mut scratch);
        if !(cts.fns.is_multi() && cts.unknown) {
            let e = self.site_likely_calls.entry(site).or_default();
            e.join_from(&scripted, &mut scratch);
        }
    }

    fn note_site_native(&mut self, script: ScriptId, pc: Pc, fns: &BoundedFnSet) {
        if fns.is_empty() && !fns.is_multi() {
            return;
        }
        let verdict = match fns.ids() {
            [f] if !fns.is_multi() && f.native_index().is_some() => Some(*f),
            _ => None,
        };
        let e = self.site_native.entry(Site::new(script, pc)).or_default();
        match verdict {
            Some(f) => e.observe(f),
            None => *e = super::types::Agreed::Conflict,
        }
    }

    fn note_site_ctor_native(&mut self, script: ScriptId, pc: Pc, fns: &BoundedFnSet) {
        if fns.is_empty() && !fns.is_multi() {
            return;
        }
        let verdict = match fns.ids() {
            [f] if !fns.is_multi() && f.native_index().is_some() => Some(*f),
            _ => None,
        };
        let e = self
            .site_ctor_native
            .entry(Site::new(script, pc))
            .or_default();
        match verdict {
            Some(f) => e.observe(f),
            None => *e = super::types::Agreed::Conflict,
        }
    }

    fn note_site_apply(
        &mut self,
        script: ScriptId,
        ctx: CtxId,
        pc: Pc,
        fns: &BoundedFnSet,
        form: CallForm,
    ) {
        // Output-table join: sink drops are diagnostics-only anyway.
        let mut scratch = Vec::new();
        let scripted = fns.scripted_only(&mut scratch);
        if ctx != CTX0 {
            self.site_apply_ctx
                .entry((ctx, Site::new(script, pc)))
                .or_default()
                .join_from(&scripted, &mut scratch);
        }
        let e = self
            .site_apply
            .entry(Site::new(script, pc))
            .or_insert((BoundedFnSet::default(), form));
        e.0.join_from(&scripted, &mut scratch);
        if fns.is_empty() && !fns.is_multi() {
            return;
        }
        let native = match fns.ids() {
            [f] if !fns.is_multi() && f.native_index().is_some() => Some(*f),
            _ => None,
        };
        let e = self
            .site_apply_native
            .entry(Site::new(script, pc))
            .or_default();
        match native {
            Some(f) => e.observe(f),
            None => *e = super::types::Agreed::Conflict,
        }
    }
}

pub type Escaped = HashSet<FnId>;
