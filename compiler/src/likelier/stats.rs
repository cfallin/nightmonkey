/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Analysis counters.
//!
//! Every number the analysis reports about its own run lives here, with a
//! name rather than an index. They are diagnostics only: nothing reads
//! them back, and `Diagnostics::stats` decides whether they are printed.
//!
//! Most of them count a *degradation* -- a place where the analysis gave
//! up precision it would rather have kept. Those are the numbers worth
//! watching, so each one names its cause: a bind that lost its context
//! should say why it lost it, not increment `degraded[1]`.

/// Counters for one run of the analysis.
#[derive(Default)]
pub struct Stats {
    /// Contexts actually instantiated: `(script, ctx)` pairs charged
    /// against the context budget.
    pub ctxs_spent: u64,
    /// Calls bound at the generic context because the site had more
    /// callees than the callee cap -- a genuinely polymorphic site.
    pub call_ctx_degraded_polymorphic: u64,
    /// ...because the call string already reached the depth cap.
    pub call_ctx_degraded_depth: u64,
    /// ...because the callee was already on the call string, so the
    /// context it was first entered at is reused (an SCC is
    /// context-insensitive internally).
    pub call_ctx_degraded_recursion: u64,
    /// ...because the whole-analysis context budget was exhausted.
    pub call_ctx_degraded_budget: u64,
    /// Property writes that landed nowhere: the receiver was AnyObject or
    /// a region, so there is no field cell to raise into. This is the
    /// model's failure mode, so it is measured rather than assumed.
    pub dropped_writes: u64,
    /// Of those, the ones whose receiver was the writing script's own
    /// `this` (see `Heap`'s this-attribution).
    pub dropped_this_writes: u64,
    /// Function-table member inserts refused at `TABLE_MEMBER_CAP`.
    pub table_members_capped: u64,
    /// Everything the analysis dropped at one of its fixed caps.
    pub caps: CapDrops,
}

/// Drops at the analysis's fixed caps.
///
/// Every cap here is deliberate -- each one is a place the analysis stops
/// rather than growing without bound, and the thing dropped is something it
/// decided was not worth the work. But "deliberate" and "invisible" are
/// different: a cap that fires far more often than expected is how a
/// corpus tells you the bound is wrong, and it cannot say so if the drop
/// leaves no trace. So each cap counts what it refused.
#[derive(Default)]
pub struct CapDrops {
    /// Function ids discarded when a `BoundedFnSet` saturated to multi.
    /// Those scripts may run through the saturated set with unbound
    /// arguments. (Recorded by `JoinSink::dropped_fns`; joins that pass a
    /// throwaway sink are not counted here.)
    pub fn_set: u64,
    /// One+One snapshot absorptions: the survivor's population silently
    /// includes the loser (`JoinSink::snap_absorbs`).
    pub snap_absorb: u64,
    /// Home classes refused at `MAX_HOMES`: a script homed everywhere is a
    /// shared helper, and linking it into every class merges their field
    /// cells into one useless claim.
    pub this_homes: u64,
    /// Prototype-chain walks that reached `CHAIN_DEPTH` without hitting a
    /// dead end, so the levels above it were never joined.
    pub proto_chain: u64,
    /// Per-site receiver label sets collapsed by the 8-label overflow: the
    /// site keeps no region evidence at all past that.
    pub recv_labels: u64,
    /// Call sites whose resolved callee set exceeded `MAX_SITE_TARGETS`,
    /// so no dispatch fact is emitted for them.
    pub call_targets: u64,
    /// Field names refused by a layout row at `LAY_CAP`.
    pub layout_fields: u64,
    /// Whole layout rows refused for exceeding `LAY_CAP`.
    pub layout_rows: u64,
    /// Constructor-delegation walks that reached `MAX_DELEG_DEPTH`.
    pub deleg_depth: u64,
    /// Construction events refused at the per-script event budget, so the
    /// layout row they would have extended stops short.
    pub this_events: u64,
    /// Predictor groups and shared-ctor classes that got no layout key
    /// because the 15-bit key space was exhausted.
    pub layout_keys: u64,
}

impl CapDrops {
    /// Fold another tally in (the emission phase accumulates its own and
    /// hands them up when it finishes).
    pub fn add(&mut self, o: &CapDrops) {
        self.fn_set += o.fn_set;
        self.snap_absorb += o.snap_absorb;
        self.this_homes += o.this_homes;
        self.proto_chain += o.proto_chain;
        self.recv_labels += o.recv_labels;
        self.call_targets += o.call_targets;
        self.layout_fields += o.layout_fields;
        self.layout_rows += o.layout_rows;
        self.deleg_depth += o.deleg_depth;
        self.this_events += o.this_events;
        self.layout_keys += o.layout_keys;
    }
}
