/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The analysis half of the speculation trace `tools/viz.py` renders.
//!
//! The translator writes the other half (which versions it minted, which
//! guards it emitted); this module writes what the analysis predicted about
//! each script's receiver and formals, so the page can show the prediction
//! next to what the lowering did with it.
//!
//! The stream goes wherever the caller points it. With `--viz-facts <path>`
//! it is a file, which is what `viz.py` asks for; otherwise `--viz` sends
//! it to stderr interleaved with the translator's records, as it always
//! has. Either way the line format is the same anchored `night: viz ...`
//! grammar the parser expects.

use super::engine::CellKey;
use super::types::{CtxId, Range, TypeSet};
use super::Solver;
use crate::ids::FormalIndex;
use crate::opsem::PRIM_DOUBLE;
use std::io::Write;

/// Open the trace stream for this run, or `None` when no viz output was
/// asked for.
pub(super) fn stream(opts: &crate::options::Options) -> Option<Box<dyn Write>> {
    if let Some(path) = &opts.diagnostics.viz_facts {
        return match std::fs::File::create(path) {
            Ok(f) => Some(Box::new(std::io::BufWriter::new(f))),
            Err(e) => {
                log::warn!("could not write viz facts to {path}: {e}");
                None
            }
        };
    }
    opts.diagnostics
        .viz
        .then(|| Box::new(std::io::stderr()) as Box<dyn Write>)
}

/// Every class-view (field) cell: which values a field of a class holds.
pub(super) fn write_field_cells(sv: &Solver<'_>, names: &crate::ids::Names, out: &mut dyn Write) {
    for (class, name, cid) in sv.engine.field_cells() {
        let ts = sv.engine.ts(cid);
        if ts.is_empty() {
            continue;
        }
        let n: String = String::from_utf16_lossy(names.get(name).chars());
        let _ = writeln!(
            out,
            "night: viz fieldty cls{} {n} ty {}",
            class.0,
            describe(ts)
        );
    }
}

/// Per arith-constraint destination: the joined evidence the numeric-
/// category gate (`fractional_arith_sites`) reads, with the dimensions
/// `describe` omits.
pub(super) fn write_arith_dsts(sv: &Solver<'_>, out: &mut dyn Write) {
    use super::engine::{CKey, CellKey, Constraint};
    let mut rows: Vec<(crate::ids::Site, String)> = Vec::new();
    for ci in 0..sv.engine.cons.len() {
        let Constraint::Arith { dst, pc, .. } = &sv.engine.cons[ci] else {
            continue;
        };
        let CKey::Var(def) = *dst else { continue };
        let pc = *pc;
        let sid = sv.engine.con_script[ci];
        let Some(ctxs) = sv.engine.live_ctxs.get(&sid) else {
            continue;
        };
        let Some(j) = sv.engine.join_over_ctxs(ctxs, |ctx| CellKey::Var {
            script: sid,
            var: def,
            ctx,
        }) else {
            continue;
        };
        rows.push((
            crate::ids::Site::new(sid, pc),
            format!("ty {} rng {:?} unk {}", describe(&j), j.range, j.unknown),
        ));
    }
    rows.sort();
    for (site, d) in rows {
        let _ = writeln!(out, "night: viz arithdst {site} {d}");
    }
}

/// Every class region with more than one member: the classes the engine
/// has merged into one receiver population.
pub(super) fn write_regions(sv: &Solver<'_>, out: &mut dyn Write) {
    let mut roots: Vec<_> = sv.engine.region_members.iter().collect();
    roots.sort_by_key(|(r, _)| r.0);
    for (root, members) in roots {
        if members.len() < 2 {
            continue;
        }
        let ms: Vec<String> = members.iter().map(|c| format!("cls{}", c.0)).collect();
        let _ = writeln!(
            out,
            "night: viz region root cls{} members {}",
            root.0,
            ms.join(",")
        );
    }
}

pub(super) fn write_gname_cells(sv: &Solver<'_>, names: &crate::ids::Names, out: &mut dyn Write) {
    for (name, cid) in sv.engine.gname_cells() {
        let ts = sv.engine.ts(cid);
        if ts.is_empty() {
            continue;
        }
        let n: String = String::from_utf16_lossy(names.get(name).chars());
        let _ = writeln!(out, "night: viz gnamety {n} ty {}", describe(ts));
    }
}

/// The predicted type of each script's receiver and formals: the `This` and
/// `Arg` cells joined over the contexts the script was live at. Index 0 is
/// `this`, index `1 + n` is formal `n` -- the fact tables' own numbering.
pub(super) fn write_arg_types(sv: &Solver<'_>, out: &mut dyn Write) {
    for sid in super::sorted_keys(&sv.engine.live_ctxs) {
        let ctxs = sv.engine.live_ctxs[&sid].clone();
        let mut emit_cell = |i: usize, mk: &dyn Fn(CtxId) -> CellKey| {
            let Some(joined) = sv.engine.join_over_ctxs(&ctxs, mk) else {
                return;
            };
            if joined.is_empty() {
                return;
            }
            let _ = writeln!(
                out,
                "night: viz argty sid#{sid} i {i} ty {}",
                describe(&joined)
            );
        };
        emit_cell(0, &|ctx| CellKey::This { script: sid, ctx });
        for n in 0..crate::constants::MAX_TRACKED_FORMALS {
            emit_cell(1 + n as usize, &|ctx| CellKey::Arg {
                script: sid,
                arg: FormalIndex::new(n),
                ctx,
            });
        }
    }
}

/// One typeset as the trace's compact `|`-separated form.
fn describe(ts: &TypeSet) -> String {
    use super::types::ObjType;
    let mut parts: Vec<String> = ts.prims.viz_parts().into_iter().map(String::from).collect();
    if ts.unknown {
        parts.push("unk".to_string());
    }
    if !ts.fns.is_empty() {
        parts.push("fn".to_string());
    }
    match ts.obj {
        ObjType::Empty => {}
        ObjType::One(_) => parts.push("obj:one".to_string()),
        ObjType::ClassAny(c) => parts.push(format!("obj:cls{}", c.0)),
        ObjType::AnyOf(r) => parts.push(format!("obj:anyof{}", r.0)),
        ObjType::AnyObject => parts.push("obj:any".to_string()),
    }
    let mut out = if parts.is_empty() {
        "none".to_string()
    } else {
        parts.join("|")
    };
    if ts.prims.intersects(PRIM_DOUBLE) && ts.range == Range::I53 {
        out.push_str(":i53");
    }
    out
}
