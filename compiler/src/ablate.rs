//! EXPERIMENT ONLY (evaluation ablations; not for upstream).
//!
//! `NIGHT_ABLATE=a,b,c` turns off named mechanisms for one compilation.
//! Two kinds of names:
//!
//! - a pass/arm switch, the lowercase name of a `knob!` (e.g. `pea`,
//!   `licm`, `hoist_guards`, `inlining`): the `const NAME: bool = true`
//!   it replaced reads false;
//! - a fact group (`facts_*`, see [`facts`]): tables of the analysis's
//!   output cleared before the translator sees them. Every fact is a
//!   guarded prediction (`facts.rs`), so clearing any table is
//!   semantics-preserving; it only removes fast paths.

use crate::facts::{CallResolution, Claim, LikelyFacts};
use std::collections::HashSet;
use std::sync::OnceLock;

fn set() -> &'static HashSet<String> {
    static S: OnceLock<HashSet<String>> = OnceLock::new();
    S.get_or_init(|| {
        let s: HashSet<String> = std::env::var("NIGHT_ABLATE")
            .unwrap_or_default()
            .split([',', ' '])
            .filter(|w| !w.is_empty())
            .map(str::to_string)
            .collect();
        if !s.is_empty() {
            crate::diag_line!("night: ablate {:?}", s);
        }
        s
    })
}

/// Whether `name` is ablated.
pub fn off(name: &str) -> bool {
    set().contains(name)
}

/// A former `const NAME: bool = true`, now `NAME()`: true unless the
/// lowercase name is in `NIGHT_ABLATE` (or the group `$group` is).
#[macro_export]
macro_rules! knob {
    ($vis:vis $name:ident, $key:literal, $group:literal) => {
        #[allow(non_snake_case)]
        #[inline]
        $vis fn $name() -> bool {
            static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *V.get_or_init(|| !($crate::ablate::off($key) || $crate::ablate::off($group)))
        }
    };
}

/// Clear the fact groups `NIGHT_ABLATE` names.
pub fn facts(f: &mut LikelyFacts) {
    if off("facts_all") {
        // The empty prediction: nothing but the string table.
        let names = std::mem::take(&mut f.names);
        *f = LikelyFacts { names, ..LikelyFacts::default() };
        return;
    }
    if off("facts_slots") {
        // No slot prediction: every property access through the IC (no
        // site rows, no class hints that would synthesize one).
        f.prop_sites.clear();
        f.this_layouts.clear();
        f.arg_cls.clear();
        f.field_cls_sites.clear();
    }
    if off("facts_heap") {
        // No value types for anything loaded from the heap: fields,
        // elements, environment slots, globals.
        for c in f.classes.values_mut() {
            for fl in &mut c.fields {
                fl.prims = Default::default();
                fl.range = None;
                fl.types = Claim::NONE;
                fl.typed_prims = Default::default();
            }
        }
        for v in f.prop_sites.values_mut() {
            v.3 = Claim::NONE;
        }
        for (_, masks) in f.group_tables.values_mut() {
            for m in masks.iter_mut() {
                *m = Default::default();
            }
        }
        f.array_elem_claims.clear();
        f.elem_sites.clear();
        f.elem_write_sites.clear();
        f.field_sites.clear();
        f.typed_sites.clear();
        f.aliased_sites.clear();
        f.gname_types.clear();
        f.field_cls_sites.clear();
    }
    if off("facts_calls") {
        // No scripted call targets (direct calls, guard chains, inlining
        // of non-local callees, predicted methods and global functions).
        f.call_sites.retain(|_, r| matches!(r, CallResolution::Native));
        f.apply_targets.clear();
        f.apply_targets_in.clear();
        f.apply_target_sets.clear();
        f.gname_fns.clear();
        f.method_sites.clear();
    }
    if off("facts_args") {
        // No interprocedural argument / return types.
        f.arg_types.clear();
        f.arg_cls.clear();
        f.call_types.clear();
    }
}
