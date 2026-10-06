//! `--viz`: what the analysis knows, in words, for `tools/viz.py`'s
//! bytecode column. Per op: the type of each value it pushed (its cell
//! joined over the script's live contexts) and every `LikelyFacts` row at
//! its site; per script: its formals', receiver's and return's cells and
//! the per-script rows; and the predicted layouts the rows name (`L<key>`).
//! Scripts are written `s<sid>`, which the page links. Diagnostics only:
//! nothing here feeds the compilation.

use super::engine::{CKey, CellKey};
use super::heap::{AbsKey, ClassKey};
use super::types::{ClassId, CtxId, FnId, Interval, ObjType, StrConsts, TypeSet};
use super::Solver;
use crate::facts::{CallResolution, Claim, LikelyFacts, RESTAMP_FORMAL};
use crate::ids::{FormalIndex, LayoutKey, NameId, ScriptId, Site};
use crate::opsem::{Prims, Range, PRIM_DOUBLE, PRIM_INT32};
use crate::source::SourceObject;
use std::collections::BTreeMap;

/// One script's analysis view.
#[derive(Default)]
pub struct ScriptView {
    /// Script-wide lines (formals, receiver, return, per-script rows).
    pub script: Vec<String>,
    /// Per pc: the pushed values' types, then the site's rows.
    pub sites: BTreeMap<u32, (Vec<String>, Vec<String>)>,
}

#[derive(Default)]
pub struct View {
    pub scripts: BTreeMap<u32, ScriptView>,
    /// `L<key>` -> its predicted fields.
    pub layouts: BTreeMap<u32, String>,
}

/// Filled by [`collect`] when `--viz` is on; taken by the record writer.
pub static VIEW: std::sync::Mutex<Option<View>> = std::sync::Mutex::new(None);

fn s(sid: ScriptId) -> String {
    format!("s{}", sid.get())
}

fn prims(p: Prims) -> String {
    format!("{p:?}")
}

/// A fact-table claim.
pub fn claim(c: Claim) -> String {
    let mut t = if c.is_none() {
        "none".to_string()
    } else if c.is_object() {
        match c.ta_kind() {
            Some(k) => format!("object ({k:?} array)"),
            None => "object".to_string(),
        }
    } else if c.bits() & Claim::OBJECT.bits() != 0 {
        // Primitives beside the object bit (`null | object`).
        format!("{} | object", prims(c.prims()))
    } else {
        prims(c.prims())
    };
    if c.double_first() {
        t.push_str(" double-first");
    }
    t
}

fn layout(lo: LayoutKey, hi: LayoutKey) -> String {
    if lo == hi {
        format!("L{}", lo.get())
    } else {
        format!("L{}..L{}", lo.get(), hi.get())
    }
}

struct Ctx<'s, 'a> {
    sv: &'s Solver<'a>,
    facts: &'s LikelyFacts,
}

impl Ctx<'_, '_> {
    fn name(&self, n: NameId) -> String {
        String::from_utf16_lossy(self.sv.names.get(n).chars())
    }

    fn fn_id(&self, f: FnId) -> String {
        if let Some(sid) = f.as_script() {
            return s(sid);
        }
        if let Some(info) = self.sv.natives.get(f) {
            return format!("native {}", self.name(info.name));
        }
        if let Some(k) = f.typed_array_kind() {
            return format!("{k:?}Array ctor");
        }
        if f == FnId::ARRAY_CTOR {
            return "Array ctor".into();
        }
        format!("builtin#{}", f.get())
    }

    /// A class, with the layout it stamps when it has one.
    fn class(&self, c: ClassId) -> String {
        let Some(info) = self.sv.heap.classes.get(c.0 as usize) else {
            return format!("class#{}", c.0);
        };
        let (what, key) = match info.key {
            ClassKey::Script(sid) => (format!("new {}", s(sid)), self.facts.ctor_stamps.get(&sid).copied()),
            ClassKey::Site(site) => {
                let kind = if let Some(k) = info.ta_kind {
                    format!("{k:?} array")
                } else if info.is_array {
                    "array".into()
                } else {
                    "literal".into()
                };
                (format!("{kind} @{}:{}", s(site.script), site.pc), self.facts.lit_stamps.get(&site).copied())
            }
            // A class named by its prototype object: by its constructor
            // where it has one (`new F` instances of `F.prototype`).
            ClassKey::Proto(o) => match info.ctor {
                Some(sid) => (format!("new {}", s(sid)), self.facts.ctor_stamps.get(&sid).copied()),
                None => (format!("proto obj#{}", o.id()), None),
            },
        };
        match key {
            Some(k) => format!("{what} L{}", k.get()),
            None => what,
        }
    }

    fn obj(&self, o: &ObjType) -> Option<String> {
        Some(match *o {
            ObjType::Empty => return None,
            ObjType::AnyObject => "any object".into(),
            ObjType::ClassAny(c) => format!("instance of {}", self.class(c)),
            ObjType::AnyOf(c) => format!("instance of region {{{}}}", self.class(self.sv.engine.region_root(c))),
            ObjType::One(a) => {
                let Some(abs) = self.sv.heap.abs.get(a.0 as usize) else {
                    return Some(format!("abs#{}", a.0));
                };
                let what = match abs.key {
                    AbsKey::Snap(id) => format!("snapshot obj#{}", id.id()),
                    AbsKey::FnObj(sid) => format!("function {}", s(sid)),
                    AbsKey::ProtoOf(c) => format!("prototype of {}", self.class(c)),
                    // Per context; the site is what tells them apart here.
                    AbsKey::Alloc { script, pc, .. } => format!("allocation @{}:{}", s(script), pc),
                    AbsKey::NativeNs(i) => format!("native namespace #{i}"),
                };
                match abs.class {
                    Some(c) if !matches!(abs.key, AbsKey::ProtoOf(_)) => format!("{what} ({})", self.class(c)),
                    _ => what,
                }
            }
        })
    }

    /// A type set joined over contexts: each component unioned, the
    /// distinct object labels and string sets listed.
    fn types(&self, sets: &[TypeSet], nctx: usize) -> String {
        if sets.is_empty() {
            return "no value reached it".into();
        }
        let mut p = Prims::EMPTY;
        let mut unknown = false;
        let mut interval = Interval::Empty;
        let mut range = Range::I32;
        let mut fns: Vec<String> = vec![];
        let mut multi = false;
        let mut objs: Vec<String> = vec![];
        let mut strs: Vec<String> = vec![];
        let mut any_str = false;
        for ts in sets {
            p |= ts.prims;
            unknown |= ts.unknown;
            interval = Interval::join(interval, ts.interval);
            if ts.range > range {
                range = ts.range;
            }
            multi |= ts.fns.is_multi();
            for &f in ts.fns.ids() {
                let n = self.fn_id(f);
                if !fns.contains(&n) {
                    fns.push(n);
                }
            }
            if let Some(o) = self.obj(&ts.obj) {
                if !objs.contains(&o) {
                    objs.push(o);
                }
            }
            match ts.strs {
                StrConsts::Any => any_str = true,
                StrConsts::Atoms { n, atoms } => {
                    for &a in &atoms[..n as usize] {
                        let t = format!("{:?}", self.name(a));
                        if !strs.contains(&t) {
                            strs.push(t);
                        }
                    }
                }
            }
        }
        let mut parts = vec![];
        if !p.is_empty() {
            let mut t = prims(p);
            if p.intersects(PRIM_INT32.or(PRIM_DOUBLE)) {
                match interval {
                    Interval::In(r) => t.push_str(&format!(" in [{}, {}]", r.lo, r.hi)),
                    Interval::Num => t.push_str(" (any number)"),
                    _ => {}
                }
                if range != Range::I32 {
                    t.push_str(&format!(" range {range:?}"));
                }
            }
            if p.intersects(crate::opsem::PRIM_STRING) && !any_str && !strs.is_empty() {
                t.push_str(&format!(" strings {{{}}}", strs.join(", ")));
            }
            parts.push(t);
        }
        if multi {
            parts.push("functions: megamorphic".into());
        } else if !fns.is_empty() {
            parts.push(format!("functions {{{}}}", fns.join(", ")));
        }
        parts.extend(objs);
        if unknown {
            parts.push("unresolved".into());
        }
        if parts.is_empty() {
            parts.push("empty (no value flowed here)".into());
        }
        let mut t = parts.join("; ");
        if nctx > 1 {
            t.push_str(&format!("  [{nctx} ctxs]"));
        }
        t
    }

    /// A scan key in `sid`, over its live contexts.
    fn key(&self, sid: ScriptId, k: CKey) -> String {
        let ctxs: Vec<CtxId> = self.sv.engine.live_ctxs.get(&sid).cloned().unwrap_or_default();
        let one = |key: CellKey| self.sv.engine.lookup(key).map(|c| self.sv.engine.ts(c).clone());
        let sets: Vec<TypeSet> = match k {
            CKey::GName(n) => one(CellKey::GName(n)).into_iter().collect(),
            CKey::Aliased { scope, slot } => one(CellKey::Aliased { scope, slot }).into_iter().collect(),
            _ => ctxs
                .iter()
                .filter_map(|&ctx| {
                    one(match k {
                        CKey::Var(var) => CellKey::Var { script: sid, var, ctx },
                        CKey::Arg(arg) => CellKey::Arg { script: sid, arg, ctx },
                        CKey::This => CellKey::This { script: sid, ctx },
                        _ => CellKey::Ret { script: sid, ctx },
                    })
                })
                .collect(),
        };
        let n = sets.len();
        self.types(&sets, n)
    }

    fn pushed(&self, site: Site, p: &super::scan::Pushed) -> String {
        let src = match p.key {
            Some(CKey::GName(n)) => format!("  (global {})", self.name(n)),
            Some(CKey::Arg(a)) => format!("  (formal {})", a.get()),
            Some(CKey::This) => "  (this)".into(),
            Some(CKey::Aliased { slot, .. }) => format!("  (closure slot {})", slot.get()),
            _ => String::new(),
        };
        match p.key {
            Some(k) => format!("{}{src}", self.key(site.script, k)),
            None if p.prims.is_empty() && p.str_const.is_none() => "(no type: not modeled here)".into(),
            None => {
                let mut t = prims(p.prims);
                if let Some(r) = p.num {
                    if r.lo == r.hi {
                        t.push_str(&format!(" = {}", r.lo));
                    } else {
                        t.push_str(&format!(" in [{}, {}]", r.lo, r.hi));
                    }
                }
                if let Some(a) = p.str_const {
                    t.push_str(&format!(" = {:?}", self.name(a)));
                }
                t.push_str("  (constant)");
                t
            }
        }
    }

    /// Every `LikelyFacts` row keyed by a site, in words.
    fn site_rows(&self) -> BTreeMap<Site, Vec<String>> {
        let f = self.facts;
        let mut m: BTreeMap<Site, Vec<String>> = BTreeMap::new();
        let mut add = |site: Site, t: String| m.entry(site).or_default().push(t);
        for (&site, r) in &f.call_sites {
            add(
                site,
                match r {
                    CallResolution::Native => "call: one modeled native".into(),
                    CallResolution::Scripted(t) => {
                        format!("call targets: {}", t.iter().map(|&x| s(x)).collect::<Vec<_>>().join(", "))
                    }
                },
            );
        }
        for (&site, &c) in &f.call_types {
            add(site, format!("call result claim: {}", claim(c)));
        }
        for (&site, &(target, kind)) in &f.accessor_sites {
            add(site, format!("accessor: {} kind {kind}", s(target)));
        }
        for (&site, &form) in &f.apply_sites {
            add(site, format!("apply form: {form:?}"));
        }
        for (&site, &t) in &f.apply_targets {
            add(site, format!("apply target: {}", s(t)));
        }
        for (&(entry, site), &t) in &f.apply_targets_in {
            add(site, format!("apply target from {}:{}: {}", s(entry.script), entry.pc, s(t)));
        }
        for (&site, ts) in &f.apply_target_sets {
            add(site, format!("apply targets: {}", ts.iter().map(|&x| s(x)).collect::<Vec<_>>().join(", ")));
        }
        for (&site, n) in &f.apply_natives {
            add(site, format!("apply native: {n:?}"));
        }
        for (&site, &(lo, hi, slot, c)) in &f.prop_sites {
            add(site, format!("property: {} slot {} value {}", layout(lo, hi), slot.get(), claim(c)));
        }
        for (&site, &(lo, hi, name, t)) in &f.method_sites {
            add(site, format!("method: {} .{} = {}", layout(lo, hi), self.name(name), s(t)));
        }
        for (&site, &c) in &f.field_sites {
            add(site, format!("field value claim: {}", claim(c)));
        }
        for (&site, &(lo, hi)) in &f.field_cls_sites {
            add(site, format!("field value class: {}", layout(lo, hi)));
        }
        for (&site, &(lo, hi, c)) in &f.typed_sites {
            add(site, format!("typed field: {} value {}", layout(lo, hi), claim(c)));
        }
        for (&site, &c) in &f.elem_sites {
            add(site, format!("element read claim: {}", claim(c)));
        }
        for (&site, &c) in &f.elem_write_sites {
            add(site, format!("element write claim: {}", claim(c)));
        }
        for (&site, k) in &f.ta_elem_sites {
            add(site, format!("typed-array element: {k:?}"));
        }
        for &site in &f.elem_poly_sites {
            add(site, "element site: polymorphic receiver".into());
        }
        for (&site, &c) in &f.aliased_sites {
            add(site, format!("closure variable claim: {}", claim(c)));
        }
        for (&site, root) in &f.array_alloc_sites {
            add(site, format!("array allocation: region {root}{}", self.elem_claim(*root)));
        }
        for (&site, root) in &f.array_elem_recv {
            add(site, format!("array element receiver: region {root}{}", self.elem_claim(*root)));
        }
        for (&site, &k) in &f.lit_stamps {
            add(site, format!("literal stamps L{}", k.get()));
        }
        for (&site, &k) in &f.construct_site_keys {
            add(site, format!("construct stamps L{}", k.get()));
        }
        for (&site, &(slot, k)) in &f.local_restamps {
            let what = if slot & RESTAMP_FORMAL != 0 {
                format!("formal {}", slot & !RESTAMP_FORMAL)
            } else {
                format!("local {slot}")
            };
            add(site, format!("restamps {what} to L{}", k.get()));
        }
        // The analysis's own per-site views, beyond the emitted rows.
        for (&site, fs) in &self.sv.site_calls {
            let t = if fs.is_multi() {
                "megamorphic".to_string()
            } else {
                fs.ids().iter().map(|&x| self.fn_id(x)).collect::<Vec<_>>().join(", ")
            };
            add(site, format!("analysis callees (all contexts): {t}"));
        }
        for (&site, k) in &self.sv.site_recv {
            add(site, format!("analysis receiver: {k:?}"));
        }
        m
    }

    fn elem_claim(&self, root: crate::ids::RegionRoot) -> String {
        match self.facts.array_elem_claims.get(&root) {
            Some(&(p, r)) => format!(", elements {} in [{}, {}]", prims(p), r.lo, r.hi),
            None => String::new(),
        }
    }

    /// Every `LikelyFacts` row keyed by a script, and its formals',
    /// receiver's and return's cells.
    fn script_rows(&self, sid: ScriptId, nargs: u32) -> Vec<String> {
        let f = self.facts;
        let mut v = vec![];
        let nctx = self.sv.engine.live_ctxs.get(&sid).map_or(0, Vec::len);
        v.push(format!("analyzed in {nctx} context(s)"));
        if nctx > 0 {
            v.push(format!("this: {}", self.key(sid, CKey::This)));
            for i in 0..nargs {
                v.push(format!("formal {i}: {}", self.key(sid, CKey::Arg(FormalIndex::new(i)))));
            }
            v.push(format!("returns: {}", self.key(sid, CKey::Ret)));
        }
        for (&(x, i), &c) in &f.arg_types {
            if x == sid {
                v.push(format!("formal {} claim: {}", i.get(), claim(c)));
            }
        }
        for (&(x, i), &(lo, hi)) in &f.arg_cls {
            if x == sid {
                v.push(format!("formal {} class: {}", i.get(), layout(lo, hi)));
            }
        }
        for &(x, i) in &f.omitted_formals {
            if x == sid {
                v.push(format!("formal {i}: some call omits it"));
            }
        }
        if let Some(&(lo, hi)) = f.this_layouts.get(&sid) {
            v.push(format!("this layout: {}", layout(lo, hi)));
        }
        if let Some(&k) = f.ctor_stamps.get(&sid) {
            v.push(format!("constructor stamps L{}", k.get()));
        }
        if let Some(&n) = f.ctor_nslots.get(&sid) {
            v.push(format!("constructor slots: {n}"));
        }
        if let Some(cs) = f.ctor_publish.get(&sid) {
            v.push(format!("publishes for: {}", cs.iter().map(|&c| s(c)).collect::<Vec<_>>().join(", ")));
        }
        if f.deleg_inits.contains(&sid) {
            v.push("delegated initializer".into());
        }
        if let Some(&k) = f.deleg_restamps.get(&sid) {
            v.push(format!("delegation restamps L{}", k.get()));
        }
        if let Some(&(formal, k)) = f.arg_restamps.get(&sid) {
            v.push(format!("restamps formal {formal} to L{}", k.get()));
        }
        v
    }

    fn layouts(&self) -> BTreeMap<u32, String> {
        let mut m = BTreeMap::new();
        for (&k, c) in &self.facts.classes {
            let fields: Vec<String> = c
                .fields
                .iter()
                .map(|fl| {
                    let mut t = format!("{}: {}", self.name(fl.name), claim(fl.types));
                    if let Some(r) = fl.range {
                        t.push_str(&format!(" in [{}, {}]", r.lo, r.hi));
                    }
                    t
                })
                .collect();
            m.insert(k.get(), format!("{{{}}}", fields.join(", ")));
        }
        for (&lo, (names, _)) in &self.facts.group_tables {
            m.entry(lo.get()).or_insert_with(|| {
                format!("group {{{}}}", names.iter().map(|&n| self.name(n)).collect::<Vec<_>>().join(", "))
            });
        }
        m
    }
}

/// Build the view (after the solve and the emission, while the solver's
/// tables are still whole) and leave it in [`VIEW`].
pub fn collect(sv: &Solver<'_>, facts: &LikelyFacts) {
    let cx = Ctx { sv, facts };
    let mut view = View { layouts: cx.layouts(), ..View::default() };
    for (id, obj) in sv.source.objects() {
        if let SourceObject::Script(script) = obj {
            let sid = ScriptId::new(id.id());
            view.scripts.entry(sid.get()).or_default().script = cx.script_rows(sid, u32::from(script.nargs));
        }
    }
    for (site, vals) in &sv.tables.pushed {
        let t: Vec<String> = vals.iter().map(|p| cx.pushed(*site, p)).collect();
        view.scripts.entry(site.script.get()).or_default().sites.entry(site.pc.get()).or_default().0 = t;
    }
    for (site, rows) in cx.site_rows() {
        let e = view.scripts.entry(site.script.get()).or_default().sites.entry(site.pc.get()).or_default();
        e.1 = rows;
        e.1.sort();
    }
    *VIEW.lock().unwrap() = Some(view);
}
