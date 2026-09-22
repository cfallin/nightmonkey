/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Typeset-based (inclusion/dataflow) likely-facts analysis: a single
//! incremental fixpoint over constraints generated once per function; context
//! is part of edge identity, not constraint identity. The likely-facts
//! source (`facts::LikelyFacts`), consumed by the translator.

use crate::facts::CallForm;
use crate::ids::{FormalIndex, ScriptId, Site, VarId};
pub mod builtins;
pub mod calls;
pub mod dump;
pub mod effects;
pub mod emit;
pub mod engine;
pub mod heap;
pub mod scan;
pub mod stats;
pub mod types;
pub mod viz;

use crate::facts::LikelyFacts;
use crate::options::Options;
use crate::source::Source;
use engine::Engine;
use rustc_hash::FxHashMap as HashMap;
use types::{BoundedFnSet, NameId, Names, TypeSet, CTX0};

/// A hash map's keys in sorted order.
///
/// Iteration order of the analysis's maps is not something the output may
/// depend on: emission order fixes the layout keys, and a layout key is in
/// the artifact. Every place that iterates a map to *produce* something
/// goes through this, so the requirement is stated by the call rather than
/// left to a bare `sort_unstable` that reads like any other sort.
pub(super) fn sorted_keys<K: Copy + Ord, V>(m: &HashMap<K, V>) -> Vec<K> {
    let mut v: Vec<K> = m.keys().copied().collect();
    v.sort_unstable();
    v
}

/// The three solver tracers, latched from the first compilation's
/// [`crate::options::Diagnostics`]. They are diagnostics -- they produce
/// stderr lines and change nothing else -- and they sit behind the solver's
/// innermost loops, which is why they are read from a latch rather than
/// threaded down through `Engine` and `Heap`.
#[derive(Default)]
pub(super) struct Tracers {
    pub(super) cell: Option<String>,
    pub(super) field: Option<String>,
    pub(super) site: Option<Site>,
    pub(super) propgap: bool,
}

static TRACERS: std::sync::OnceLock<Tracers> = std::sync::OnceLock::new();

pub(super) fn tracers() -> &'static Tracers {
    TRACERS.get_or_init(Tracers::default)
}

/// Latch the tracers from this compilation's options. Idempotent: the first
/// compilation in a process wins, which is all a debugging aid needs.
pub(super) fn set_tracers(d: &crate::options::Diagnostics) {
    let _ = TRACERS.set(Tracers {
        cell: d.trace_cell.clone(),
        field: d.trace_field.clone(),
        site: d.trace_site.as_ref().and_then(|v| {
            let (s, p) = v.split_once(':')?;
            Some(Site::from_raw(s.parse().ok()?, p.parse().ok()?))
        }),
        propgap: d.propgap,
    });
}

/// The one read site under per-ctx eval tracing (diagnostics-only).
pub(super) fn trace_site_want() -> Option<Site> {
    tracers().site
}

/// How well a property site's receiver was resolved, ordered from most to
/// least precise. The AnyObject rate is this model's failure mode, so it
/// is measured per site rather than assumed.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum RecvKind {
    /// No receiver value ever arrived.
    Empty,
    /// One abstraction: the most precise answer there is.
    One,
    /// Some instance of one class.
    ClassAny,
    /// Some instance of one region of classes.
    AnyOf,
    /// Any object at all.
    AnyObject,
}

impl RecvKind {
    const ALL: [RecvKind; 5] = [
        RecvKind::Empty,
        RecvKind::One,
        RecvKind::ClassAny,
        RecvKind::AnyOf,
        RecvKind::AnyObject,
    ];
}

/// One construct site whose constructor script is shared by many classes
/// (the `Class.create()` idiom), resolved concretely from the snapshot.
pub struct SharedCtorSite {
    pub ctor: ScriptId,
    pub proto: crate::source::SourceObjectId,
    /// The init delegate the ctor's `this.<init>.apply` dispatch reaches.
    pub init: ScriptId,
}

pub struct Solver<'a> {
    pub source: &'a Source,
    pub gname_fns: &'a HashMap<NameId, ScriptId>,
    pub opts: &'a Options,
    pub engine: Engine,
    pub names: Names,
    pub tables: scan::ScanTables,
    pub heap: heap::Heap,
    pub ctxs: calls::Ctxs,
    /// Diagnostic counters for this run (see [`stats::Stats`]).
    pub stats: stats::Stats,
    pub escaped: calls::Escaped,
    /// Receiver-kind census per property-read site: the least precise
    /// receiver the site was ever evaluated with.
    pub site_recv: HashMap<Site, RecvKind>,
    /// Per-call-site resolved callee sets, joined over live contexts. Sound
    /// (an unresolved callee collapses it to multi): the effect summary's
    /// source.
    pub site_calls: HashMap<Site, BoundedFnSet>,
    /// `site_calls` without the evaluations whose callee was only the
    /// unresolved bit (multi with `unknown`): the guard chain's source, a
    /// prediction the runtime identity guards enforce.
    pub site_likely_calls: HashMap<Site, BoundedFnSet>,
    /// Per-apply-site resolved target set + kind.
    pub site_apply: HashMap<Site, (BoundedFnSet, CallForm)>,
    /// `site_apply` per non-generic context: the target set an apply site
    /// resolves to when its body was entered from one call site (a shared
    /// `initialize.apply(this, arguments)` wrapper resolves mono per `new`
    /// site and multi in the join).
    pub site_apply_ctx: HashMap<(types::CtxId, Site), BoundedFnSet>,
    /// Per apply-site mono NATIVE target, while every evaluation agrees
    /// (`hasOwnProperty.call(o, k)`): the native forward arms' source.
    pub site_apply_native: HashMap<Site, types::Agreed<types::FnId>>,
    /// First escapes, with the triggering constraint (root-cause census).
    pub escape_log: Vec<(types::FnId, engine::ConId)>,
    /// Per-read-site result typeset, joined over evaluations (the source of
    /// the numeric field/elem masks: "this read yields numeric", guarded).
    pub site_read_ts: HashMap<Site, TypeSet>,
    /// Per-property-site receiver class, while every resolved receiver
    /// agrees (a receiver that went AnyObject counts as a disagreement).
    pub site_recv_class: HashMap<Site, types::Agreed<types::ClassId>>,
    /// Sites one evaluation reached with the `TypeSet::unresolved` receiver:
    /// their agreement is re-derived from the final per-context states after
    /// the fixpoint (`settle_unresolved_recv_sites`), where that row is
    /// weighed as no evidence.
    pub site_recv_unresolved: rustc_hash::FxHashSet<Site>,
    /// Per-read-site VALUE class, while every derived result agrees --
    /// the read's obj half through the same mapper as the receiver rows
    /// (regions accepted: an AnyOf value keeps its root's label). Feeds
    /// `field_cls_sites`, the advisory likely-class the loaded value
    /// carries until a use guards it.
    pub site_value_class: HashMap<Site, types::Agreed<types::ClassId>>,
    /// Per-property-site raw receiver class labels (One classes, ClassAny,
    /// AnyOf region labels), find-at-emission so later unions never poison
    /// early evidence. Conflict once an AnyObject receiver shows up or the
    /// label cap overflows; the region-range rung consumes sites whose
    /// labels all resolve to one region root.
    pub site_recv_labels: HashMap<Site, types::AgreedSet<types::ClassId>>,
    /// Per-elem-site receiver typed-array kind, while the site's receivers
    /// agree on one.
    pub site_recv_ta: HashMap<Site, types::Agreed<crate::opsem::TaKind>>,
    /// Constructor scripts that were actually constructed.
    pub constructed: rustc_hash::FxHashSet<ScriptId>,
    /// The this-assertion, authoritative: a method homed to exactly one
    /// class has This(m, ctx) pinned to ClassAny(C) in every context;
    /// caller receivers are ignored (a polymorphic dispatch site's
    /// AnyObject must not destroy the body's precision). A second
    /// differing install conflicts the entry, and shared methods then bind
    /// normally.
    pub this_pin: HashMap<ScriptId, types::Agreed<types::ClassId>>,
    /// this-write attribution (cell side): script -> home classes whose
    /// ClassField cells its ThisField cells feed (capped; links installed
    /// pairwise with `this_field_names`).
    pub this_homes: HashMap<ScriptId, Vec<types::ClassId>>,
    /// Names a script has this-written (ThisField cells minted), for
    /// late-home link installs.
    pub this_field_names: HashMap<ScriptId, Vec<NameId>>,
    /// this-forwarding call edges caller -> callees: home classes
    /// propagate through them (the Deleg channel, cell side).
    pub this_delegs: HashMap<ScriptId, Vec<ScriptId>>,
    /// Shared-generated-ctor construct sites, resolved concretely from
    /// the snapshot pre-solve (`resolve_shared_ctor_sites`): (site) ->
    /// the per-prototype ClassId the site constructs. Consumed at
    /// construct evaluation in place of the (collapsing) script-keyed
    /// `class_for_fn`.
    pub site_ctor_class: HashMap<Site, types::ClassId>,
    /// The same sites' raw resolution: (site) -> (ctor script, proto
    /// object id, init-delegate script). The emit-phase layout minting
    /// consumes this.
    pub shared_ctor_sites: HashMap<Site, SharedCtorSite>,
    /// Callee vars resolved through an AnyOf region's method tables: they
    /// bind at the generic context only (no ctx minting off a guessed
    /// dispatch) but are emitted -- the set is flow-scoped, not a name
    /// guess.
    pub region_calls: rustc_hash::FxHashSet<(ScriptId, VarId)>,
    /// Per-call-site named-native resolution, while every evaluation
    /// agrees on one native callee. Anything else -- scripted, multi, a
    /// different native -- conflicts it. Source of the native call fact.
    pub site_native: HashMap<Site, types::Agreed<types::FnId>>,
    /// The construct-site mirror of `site_native` (`new Date()`): kept
    /// separate so emission's native-call lowering is untouched; consumed
    /// by the effect-summary fold only.
    pub site_ctor_native: HashMap<Site, types::Agreed<types::FnId>>,
    /// Fn-table member lists, per table abstraction. The
    /// elems cell saturates to fn-multi at the BoundedFnSet cap, so identities
    /// are collected where they are still singular: snapshot elements
    /// (the wizer image is live), per-ctx elems writes, and -- for
    /// registrations degraded to the generic context -- the per-site arg
    /// values recorded in `arg_fn_members`. Unbounded up to
    /// `TABLE_MEMBER_CAP`.
    pub table_members: HashMap<types::AbsId, rustc_hash::FxHashSet<types::FnId>>,
    /// `table_members` aggregated by the table abstraction's class: a
    /// dispatch whose table read merged to `ClassAny` (every
    /// `[handler, scope]` pair sharing one literal-site class) still
    /// finds the member population.
    pub class_table_members: HashMap<types::ClassId, rustc_hash::FxHashSet<types::FnId>>,
    /// Scripted fn ids observed flowing into a callee's arg row, keyed
    /// (callee sid, arg index), recorded at call binding from the site's
    /// value before the row join can saturate.
    pub arg_fn_members: HashMap<(ScriptId, FormalIndex), rustc_hash::FxHashSet<types::FnId>>,
    /// Reverse feed: arg rows observed writing (saturated) into a table's
    /// elems -- later single-fn arrivals on the row append to the table
    /// directly (the multi cell no longer grows, so the write con never
    /// re-fires).
    pub arg_row_tables: HashMap<(ScriptId, FormalIndex), Vec<types::AbsId>>,
    /// Callee-position elems reads: (sid, dst var) -> receiver key, so an
    /// fn-multi callee at a call site can be traced back to the table
    /// abstraction it was read from.
    pub elems_callee_vars: HashMap<(ScriptId, VarId), engine::CKey>,
    /// Tables whose dispatch-site join rows exist; the value is how many
    /// members have standing links installed (re-linked on growth).
    pub table_bound: HashMap<types::AbsId, usize>,
    /// Class accessor table (`Object.defineProperty(P, name, {get, set})`
    /// modeled): (class, name) -> (getter sid, setter sid). A conflicting
    /// second install poisons the entry (removed + remembered, never
    /// re-registered).
    pub accessors: HashMap<(types::ClassId, NameId), (Option<ScriptId>, Option<ScriptId>)>,
    pub accessor_poisoned: rustc_hash::FxHashSet<(types::ClassId, NameId)>,
    /// The reserved function ids minted for named natives, filled lazily.
    /// Those ids never leave the solver -- the fact tables filter builtins.
    pub natives: builtins::Natives,
    /// The property names the analysis itself has to recognise.
    names_of: WellKnown,
}

/// The property names the analysis reasons about by identity rather than
/// by evidence: the reserved element name, `prototype` (a class bridge,
/// never value flow), and the `Object.defineProperty` trio.
pub struct WellKnown {
    pub elems: NameId,
    pub prototype: NameId,
    pub get: NameId,
    pub set: NameId,
    pub define_property: NameId,
}

impl<'a> Solver<'a> {
    fn new(
        source: &'a Source,
        gname_fns: &'a HashMap<NameId, ScriptId>,
        opts: &'a Options,
        mut names: Names,
    ) -> Solver<'a> {
        let names_of = WellKnown {
            elems: names.intern(scan::ELEMS),
            prototype: names.intern_str("prototype"),
            get: names.intern_str("get"),
            set: names.intern_str("set"),
            define_property: names.intern_str("defineProperty"),
        };
        let mut engine = Engine::default();
        engine.elems_name = Some(names_of.elems);
        Solver {
            source,
            gname_fns,
            opts,
            engine,
            names,
            tables: scan::ScanTables::default(),
            heap: heap::Heap::default(),
            ctxs: calls::Ctxs::new(),
            stats: stats::Stats::default(),
            escaped: calls::Escaped::default(),
            site_recv: HashMap::default(),
            site_calls: HashMap::default(),
            site_likely_calls: HashMap::default(),
            site_apply: HashMap::default(),
            site_apply_ctx: HashMap::default(),
            site_apply_native: HashMap::default(),
            escape_log: Vec::new(),
            site_read_ts: HashMap::default(),
            site_recv_class: HashMap::default(),
            site_recv_unresolved: rustc_hash::FxHashSet::default(),
            site_value_class: HashMap::default(),
            site_recv_labels: HashMap::default(),
            site_recv_ta: HashMap::default(),
            constructed: rustc_hash::FxHashSet::default(),
            this_pin: HashMap::default(),
            this_homes: HashMap::default(),
            this_field_names: HashMap::default(),
            this_delegs: HashMap::default(),
            site_ctor_class: HashMap::default(),
            shared_ctor_sites: HashMap::default(),
            site_native: HashMap::default(),
            site_ctor_native: HashMap::default(),
            region_calls: rustc_hash::FxHashSet::default(),
            table_members: HashMap::default(),
            class_table_members: HashMap::default(),
            arg_fn_members: HashMap::default(),
            arg_row_tables: HashMap::default(),
            elems_callee_vars: HashMap::default(),
            table_bound: HashMap::default(),
            accessors: HashMap::default(),
            accessor_poisoned: rustc_hash::FxHashSet::default(),
            natives: builtins::Natives::default(),
            names_of,
        }
    }

    /// Post-fixpoint half of the `NIGHT_TRACE_SITE` tracer: for the traced
    /// site's script, every live ctx with its provenance and its Arg/This/
    /// recv cell contents -- "which ctxs hold the values" against the eval
    /// tracer's "which ctxs the read evaluates in".
    fn trace_site_dump(&mut self) {
        use engine::{CellKey, Constraint};
        let Some(site) = trace_site_want() else {
            return;
        };
        let sid = site.script;
        let recv = self.engine.script_cons.get(&sid).and_then(|cons| {
            cons.iter()
                .find_map(|&c| match &self.engine.cons[c.0 as usize] {
                    Constraint::Read { recv, pc, .. } if *pc == site.pc => Some(*recv),
                    _ => None,
                })
        });
        let ctxs = self.engine.live_ctxs.get(&sid).cloned().unwrap_or_default();
        crate::diag_line!(
            "night: tracesite dump {site} live-ctxs {} recv {:?}",
            ctxs.len(),
            recv
        );
        fn show(eng: &Engine, key: CellKey) -> String {
            match eng.lookup(key) {
                None => "-".to_string(),
                Some(id) => {
                    let ts = eng.ts(id);
                    format!("{:?}/{:?}/u{}", ts.obj, ts.prims, u8::from(ts.unknown))
                }
            }
        }
        for ctx in ctxs {
            let mut args = Vec::new();
            for i in 0..crate::constants::MAX_TRACKED_FORMALS {
                let k = CellKey::Arg {
                    script: sid,
                    arg: FormalIndex::new(i),
                    ctx,
                };
                args.push(format!("a{i}[{}]", show(&self.engine, k)));
            }
            let this = show(&self.engine, CellKey::This { script: sid, ctx });
            let rv = match recv {
                None => "-".to_string(),
                Some(r) => {
                    let id = self.engine.resolve(sid, ctx, r);
                    let ts = self.engine.ts(id).clone();
                    format!("{:?}/{:?}/u{}", ts.obj, ts.prims, u8::from(ts.unknown))
                }
            };
            crate::diag_line!(
                "night: tracesite ctx {} ({}) this[{this}] recv[{rv}] {}",
                ctx.0,
                self.ctxs.describe(ctx),
                args.join(" ")
            );
        }
        if let Some(r) = recv {
            let needle = format!("{r:?}");
            if let Some(cons) = self.engine.script_cons.get(&sid) {
                for &c in cons {
                    let con = &self.engine.cons[c.0 as usize];
                    let d = format!("{con:?}");
                    if d.contains(&needle) {
                        crate::diag_line!("night: tracesite con {} {d}", c.0);
                    }
                }
            }
        }
        // The class identity table, so a traced site's predicted ClassId
        // resolves to its minting key and ctor attribution without a
        // second run.
        for (i, ci) in self.heap.classes.iter().enumerate() {
            crate::diag_line!(
                "night: tracesite class {} key {:?} ctor {:?}",
                i,
                ci.key,
                ci.ctor,
            );
        }
    }

    fn solve(&mut self) {
        // Instantiate every script at the generic context; precise contexts
        // arrive with call binding.
        for sid in sorted_keys(&self.engine.script_cons) {
            self.engine.instantiate(sid, CTX0);
        }
        while let Some((c, ctx)) = self.engine.pop() {
            if self.engine.eval_core(c, ctx) {
                continue;
            }
            if self.eval_heap(c, ctx) {
                continue;
            }
            let handled = self.eval_call(c, ctx);
            debug_assert!(handled, "unhandled constraint kind");
        }
    }

    /// Phase counts and timings, plus the escape / AnyObject-transition
    /// attribution. Emitted only when statistics are requested.
    fn census(&mut self, t0: std::time::Instant) {
        let kinds: Vec<String> = engine::ConstraintKind::ALL
            .iter()
            .map(|&k| {
                let n = self.engine.cons.iter().filter(|c| c.kind() == k).count();
                format!("{} {n}", k.name())
            })
            .collect();
        crate::diag_line!(
            "likelier: {} scripts, {} cons ({}), {} cells, {} evals, {} raises, {}ms",
            self.tables.n_scripts,
            self.engine.cons.len(),
            kinds.join(" "),
            self.engine.cells.len(),
            self.engine.n_evals,
            self.engine.n_raises,
            t0.elapsed().as_millis()
        );
        let mut recv = [0usize; 5];
        for &r in self.site_recv.values() {
            recv[RecvKind::ALL.iter().position(|&k| k == r).unwrap()] += 1;
        }
        crate::diag_line!(
            "likelier: ctxs {} (degraded poly {} depth {} rec {} budget {}), \
             {} abstractions, {} classes, escaped {}, dropped-writes {} (this {}), \
             read-recv empty {} one {} classany {} anyof {} anyobj {}, \
             aliased resolved {} unresolved {}",
            self.stats.ctxs_spent,
            self.stats.call_ctx_degraded_polymorphic,
            self.stats.call_ctx_degraded_depth,
            self.stats.call_ctx_degraded_recursion,
            self.stats.call_ctx_degraded_budget,
            self.heap.abs.len(),
            self.heap.classes.len(),
            self.escaped.len(),
            self.stats.dropped_writes,
            self.stats.dropped_this_writes,
            recv[0],
            recv[1],
            recv[2],
            recv[3],
            recv[4],
            self.tables.aliased_resolved,
            self.tables.aliased_unresolved
        );
        let caps = &self.stats.caps;
        crate::diag_line!(
            "likelier: cap drops: fn-set {} snap-absorb {} this-homes {} proto-chain {} \
             recv-labels {} call-targets {} layout-fields {} layout-rows {} \
             deleg-depth {} layout-keys {} this-events {} table-members {}",
            caps.fn_set,
            caps.snap_absorb,
            caps.this_homes,
            caps.proto_chain,
            caps.recv_labels,
            caps.call_targets,
            caps.layout_fields,
            caps.layout_rows,
            caps.deleg_depth,
            caps.layout_keys,
            caps.this_events,
            self.stats.table_members_capped
        );
        // The giant-region watchdog: region count + biggest.
        let mut biggest = 0usize;
        let n_regions = self.engine.region_members.len();
        for m in self.engine.region_members.values() {
            biggest = biggest.max(m.len());
        }
        if n_regions > 0 {
            crate::diag_line!(
                "likelier: {} class regions, biggest {} members",
                n_regions,
                biggest
            );
        }
        for &(f, c) in &self.escape_log {
            if c == engine::SEED {
                crate::diag_line!("likelier: escape fn#{f} via SEED");
            } else {
                let sid = self.engine.con_script[c.0 as usize];
                crate::diag_line!(
                    "likelier: escape fn#{f} via #{sid} {:?}",
                    self.engine.cons[c.0 as usize]
                );
            }
        }
        let mut rows: Vec<(engine::ConId, u32)> = self
            .engine
            .anyobj_why
            .iter()
            .map(|(&c, &n)| (c, n))
            .collect();
        for (key, c) in self.engine.anyobj_first.clone() {
            let what = if c == engine::SEED {
                "SEED/link".to_string()
            } else {
                format!(
                    "#{} {:?}",
                    self.engine.con_script[c.0 as usize], self.engine.cons[c.0 as usize]
                )
            };
            crate::diag_line!("likelier: anyobj-first {key:?} via {what}");
        }
        rows.sort_by(|a, b| b.1.cmp(&a.1).then(a.0 .0.cmp(&b.0 .0)));
        for (c, n) in rows.into_iter().take(12) {
            if c == engine::SEED {
                crate::diag_line!("likelier: anyobj {n} via SEED/link");
                continue;
            }
            let sid = self.engine.con_script[c.0 as usize];
            crate::diag_line!(
                "likelier: anyobj {n} via #{sid} {:?}",
                self.engine.cons[c.0 as usize]
            );
        }
    }
}

pub fn analyze(
    source: &Source,
    gname_fns: &HashMap<NameId, ScriptId>,
    opts: &Options,
    names: Names,
) -> LikelyFacts {
    let t0 = std::time::Instant::now();
    set_tracers(&opts.diagnostics);
    let mut sv = Solver::new(source, gname_fns, opts, names);
    scan::scan_all(
        &mut sv.engine,
        &mut sv.names,
        &mut sv.tables,
        source,
        gname_fns,
    );
    sv.seed();
    sv.resolve_shared_ctor_sites();
    sv.solve();
    sv.settle_unresolved_recv_sites();
    sv.trace_site_dump();
    // The census runs last so it can report what the emission phase
    // refused at its caps, not just what the fixpoint did.
    let mut facts = sv.emit();
    if opts.diagnostics.stats {
        sv.census(t0);
    }
    // The string table travels on with the facts: every `NameId` in them
    // resolves through it, and the translator takes it over from here.
    facts.names = std::mem::take(&mut sv.names);
    facts
}
