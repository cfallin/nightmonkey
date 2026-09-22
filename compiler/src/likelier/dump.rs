/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Canonical `LikelyFacts` dump (`Diagnostics::facts`), written at the
//! `layout_env` seam so both analyses produce the identical format. The
//! parity diff script (`tools/diff-facts.py`) compares two dumps per table
//! per site.

use crate::facts::LikelyFacts;
use crate::ids::{JsString, NameId, Names};
use std::fmt::Write as _;

/// Property names are UTF-16; escape anything outside the identifier-ish
/// range so lines stay unambiguous and single-line.
fn esc(name: &JsString) -> String {
    let mut s = String::new();
    for &u in name.chars() {
        match char::from_u32(u32::from(u)) {
            Some(c) if c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '.' => s.push(c),
            _ => {
                let _ = write!(s, "%{u:04x}");
            }
        }
    }
    if s.is_empty() {
        s.push_str("%empty");
    }
    s
}

fn names(tbl: &Names, list: &[NameId]) -> String {
    list.iter()
        .map(|&n| esc(tbl.get(n)))
        .collect::<Vec<_>>()
        .join(",")
}

pub fn dump_facts(facts: &LikelyFacts, path: &str) {
    let mut out = String::new();
    let _ = writeln!(out, "# night-facts-dump v1");
    let _ = writeln!(out, "meta n_classes = {}", facts.n_classes);
    let _ = writeln!(out, "meta n_cons = {}", facts.n_cons);

    let mut lines: Vec<String> = Vec::new();
    for (site, targets) in facts.scripted_call_sites() {
        let mut t = targets.to_vec();
        t.sort_unstable();
        let t: Vec<String> = t.iter().map(|x| x.to_string()).collect();
        lines.push(format!("calls {site} = {}", t.join(",")));
    }
    for (&site, &(target, kind)) in &facts.accessor_sites {
        lines.push(format!("accessor_sites {site} = {target} {kind}"));
    }
    for (&site, &kind) in &facts.apply_sites {
        lines.push(format!("apply_sites {site} = {kind:?}"));
    }
    for (&site, &target) in &facts.apply_targets {
        lines.push(format!("apply_targets {site} = {target}"));
    }
    for (&(entry, site), &target) in &facts.apply_targets_in {
        lines.push(format!("apply_targets_in {entry} {site} = {target}"));
    }
    for (&site, targets) in &facts.apply_target_sets {
        let t: Vec<String> = targets.iter().map(|t| t.to_string()).collect();
        lines.push(format!("apply_target_sets {site} = [{}]", t.join(" ")));
    }
    for name in &facts.accessor_names {
        lines.push(format!(
            "accessor_names {} = 1",
            esc(facts.names.get(*name))
        ));
    }
    for (&(script, i), &claim) in &facts.arg_types {
        lines.push(format!("arg_types {script}:{i} = {:#x}", claim.bits()));
    }
    for (&name, &claim) in &facts.gname_types {
        lines.push(format!(
            "gname_types {} = {:#x}",
            esc(facts.names.get(name)),
            claim.bits()
        ));
    }
    for (&site, &claim) in &facts.call_types {
        lines.push(format!("call_types {site} = {:#x}", claim.bits()));
    }
    for (&site, &claim) in &facts.aliased_sites {
        lines.push(format!("aliased_sites {site} = {:#x}", claim.bits()));
    }
    for &site in &facts.fractional_arith_sites {
        lines.push(format!("fractional_arith_sites {site}"));
    }
    for &site in &facts.string_arith_sites {
        lines.push(format!("string_arith_sites {site}"));
    }
    for (&site, key) in &facts.lit_stamps {
        lines.push(format!("lit_stamps {site} = {}", key.get()));
    }
    for (&root, &(prims, range)) in &facts.array_elem_claims {
        lines.push(format!(
            "array_elem_claims {root} = {:#x} {} {}",
            prims.bits(),
            range.lo,
            range.hi
        ));
    }
    for (&site, &root) in &facts.array_alloc_sites {
        lines.push(format!("array_alloc_sites {site} = {root}"));
    }
    for (&site, &root) in &facts.array_elem_recv {
        lines.push(format!("array_elem_recv {site} = {root}"));
    }
    for (&site, &key) in &facts.construct_site_keys {
        lines.push(format!("construct_site_keys {site} = {key}"));
    }
    for (&site, r) in &facts.call_sites {
        if matches!(r, crate::facts::CallResolution::Native) {
            lines.push(format!("native_calls {site} = 1"));
        }
    }
    for (&s, &(lo, hi)) in &facts.this_layouts {
        lines.push(format!("this_layouts {s} = {lo} {hi}"));
    }
    for (&ctor, class) in &facts.classes {
        let row: Vec<NameId> = class.fields.iter().map(|f| f.name).collect();
        lines.push(format!(
            "class_layouts {ctor} = {}",
            names(&facts.names, &row)
        ));
        let m: Vec<String> = class
            .fields
            .iter()
            .map(|f| format!("{:#x}", f.prims.bits()))
            .collect();
        lines.push(format!("class_layout_masks {ctor} = {}", m.join(",")));
        if class.fields.iter().any(|f| f.typed_prims != f.prims) {
            let m: Vec<String> = class
                .fields
                .iter()
                .map(|f| format!("{:#x}", f.typed_prims.bits()))
                .collect();
            lines.push(format!("class_layout_typed_masks {ctor} = {}", m.join(",")));
        }
    }
    for (&site, &(lo, hi, slot, mask)) in &facts.prop_sites {
        lines.push(format!(
            "prop_sites {site} = {lo} {hi} {slot} {:#x}",
            mask.bits()
        ));
    }
    for (&site, &mask) in &facts.elem_sites {
        lines.push(format!("elem_sites {site} = {:#x}", mask.bits()));
    }
    for (&site, &mask) in &facts.elem_write_sites {
        lines.push(format!("elem_write_sites {site} = {:#x}", mask.bits()));
    }
    for (&site, &kind) in &facts.ta_elem_sites {
        lines.push(format!("ta_elem_sites {site} = {}", kind.code()));
    }
    for &site in &facts.elem_poly_sites {
        lines.push(format!("elem_poly_sites {site} = 1"));
    }
    for (&site, &(lo, hi)) in &facts.field_cls_sites {
        lines.push(format!("field_cls_sites {site} = {lo} {hi}"));
    }
    for (&(sid, i), &(lo, hi)) in &facts.arg_cls {
        lines.push(format!("arg_cls {sid}:{} = {lo} {hi}", i.get()));
    }
    for (&site, &mask) in &facts.field_sites {
        lines.push(format!("field_sites {site} = {:#x}", mask.bits()));
    }
    for (&site, &(lo, hi, mask)) in &facts.typed_sites {
        lines.push(format!("typed_sites {site} = {lo} {hi} {:#x}", mask.bits()));
    }
    for &s in &facts.deleg_inits {
        lines.push(format!("deleg_inits {s} = 1"));
    }
    for (&s, &key) in &facts.deleg_restamps {
        lines.push(format!("deleg_restamps {s} = {key}"));
        if let Some(class) = facts.classes.get(&key) {
            let row: Vec<NameId> = class.fields.iter().map(|f| f.name).collect();
            lines.push(format!(
                "deleg_restamp_layouts {s} = {}",
                names(&facts.names, &row)
            ));
        }
    }
    for (&s, &key) in &facts.ctor_stamps {
        lines.push(format!("ctor_stamps {s} = {key}"));
    }
    for (&s, &n) in &facts.ctor_nslots {
        lines.push(format!("ctor_nslots {s} = {n}"));
    }
    for (&lo, (fields, masks)) in &facts.group_tables {
        let m: Vec<String> = masks.iter().map(|x| format!("{:#x}", x.bits())).collect();
        lines.push(format!(
            "group_tables {lo} = {} / {}",
            names(&facts.names, fields),
            m.join(",")
        ));
    }
    // Derived, stably-keyed views for cross-analysis comparison: the dense
    // layout keys above are a per-analysis numbering artifact.
    for (&f, &key) in &facts.ctor_stamps {
        if let Some(class) = facts.classes.get(&key) {
            let row: Vec<NameId> = class.fields.iter().map(|f| f.name).collect();
            lines.push(format!("ctor_layouts {f} = {}", names(&facts.names, &row)));
            let m: Vec<String> = class
                .fields
                .iter()
                .map(|f| format!("{:#x}", f.prims.bits()))
                .collect();
            lines.push(format!("ctor_layout_masks {f} = {}", m.join(",")));
        }
    }
    for (&m, &(lo, hi)) in &facts.this_layouts {
        let row: Option<Vec<NameId>> = if lo == hi {
            facts
                .classes
                .get(&lo)
                .map(|c| c.fields.iter().map(|f| f.name).collect())
        } else {
            facts.group_tables.get(&lo).map(|(t, _)| t.clone())
        };
        if let Some(row) = row {
            let kind = if lo == hi { "exact" } else { "range" };
            lines.push(format!(
                "this_slots {m} = {kind} {}",
                names(&facts.names, &row)
            ));
        }
    }
    for (&site, native) in &facts.apply_natives {
        lines.push(format!("apply_natives {site} = {native:?}"));
    }
    for (&site, &(local, key)) in &facts.local_restamps {
        lines.push(format!("local_restamp {site} = l{local} -> {key}"));
    }
    for (&sid, &(formal, key)) in &facts.arg_restamps {
        lines.push(format!(
            "arg_restamp {} = a{} -> {}",
            sid.get(),
            formal,
            key.get()
        ));
    }
    for (&site, &(lo, hi, slot, mask)) in &facts.prop_sites {
        let kind = if lo == hi { "exact" } else { "range" };
        lines.push(format!(
            "prop_slots {site} = {kind} {}..{} {slot} {:#x}",
            lo.get(),
            hi.get(),
            mask.bits()
        ));
    }
    for (&sid, e) in &facts.script_effects {
        let mut fields = String::new();
        for &(range, name) in &e.field_writes {
            let cls = match range {
                Some((lo, hi)) => format!("{}..{}", lo.get(), hi.get()),
                None => "?".to_string(),
            };
            let _ = write!(fields, " {}:{}", cls, esc(facts.names.get(name)));
        }
        lines.push(format!(
            "effect sid#{} = {}{fields}{}",
            sid.get(),
            e.label(),
            if e.gname_writes.is_empty() {
                String::new()
            } else {
                format!(" gnames={}", names(&facts.names, &e.gname_writes))
            },
        ));
    }
    lines.sort();
    for l in lines {
        let _ = writeln!(out, "{l}");
    }
    match std::fs::write(path, &out) {
        Ok(()) => crate::diag_line!("likelier: facts dump written to {path}"),
        Err(e) => log::error!("likelier: facts dump to {path} failed: {e}"),
    }
}
