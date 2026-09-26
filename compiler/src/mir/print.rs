//! The MIR text format: a printer whose output `parse` reads back to an
//! equal module. Meant for hand-written tests and dumps, so it prints the
//! compact spelling of every type (components the tags already imply are
//! left out) and names atoms by their strings rather than their ids.
//!
//! ```text
//! module {
//!   atom "x"
//!   layout L3 = { x: val{int32} range[0,99], next: val{object} obj{Plain} }
//! }
//!
//! func @s12 (formals=1, locals=0, depths={0:0}) {
//!   root entry b0
//!
//! b0(v0: obj{Function(s12)}, v1: val, v2: val):
//!   guard.unbox.i32 v2 -> ok b1(v3: i32), fail b9
//! b1(v3: i32):
//!   v4 = box v3
//!   return v4
//! b9:
//!   v5 = const.val undefined
//!   exit pc=0 this=v1 args=[v2] locals=[] rval=v5 stack=[]
//! }
//! ```
//!
//! Output is deterministic: blocks print in layout order, module tables
//! in id order.

use std::fmt::Write as _;

use crate::ids::JsString;
use crate::mir::entity::AtomId;
use crate::mir::func::{EdgeArg, Func, RootKind};
use crate::mir::module::{Module, Region};
use crate::mir::ops::*;
use crate::mir::types::*;

/// Anything that can name an atom: the module when there is one (strings),
/// nothing in error messages that have no module at hand (ids).
fn atom(m: Option<&Module>, a: AtomId) -> String {
    match m.and_then(|m| m.atoms.get(a)) {
        Some(s) => atom_str(s),
        None => a.to_string(),
    }
}

/// An atom as a bare identifier when it is one, else a quoted string.
pub fn atom_str(s: &JsString) -> String {
    let chars: Vec<u16> = s.chars().to_vec();
    let is_ident = !chars.is_empty()
        && chars.iter().enumerate().all(|(i, &c)| {
            c < 0x80 && {
                let c = c as u8 as char;
                c == '_' || c == '$' || c.is_ascii_alphabetic() || (i > 0 && c.is_ascii_digit())
            }
        })
        && !is_reserved_word(&s.to_string());
    if is_ident {
        return s.to_string();
    }
    let mut out = String::from("\"");
    for &c in &chars {
        match c {
            0x22 => out.push_str("\\\""),
            0x5c => out.push_str("\\\\"),
            0x20..=0x7e => out.push(c as u8 as char),
            _ => write!(out, "\\u{{{c:x}}}").unwrap(),
        }
    }
    out.push('"');
    out
}

/// Words the parser gives meaning in an atom's position.
fn is_reserved_word(s: &str) -> bool {
    matches!(s, "types")
}

pub fn tags_str(t: TagSet) -> String {
    let names: Vec<_> = TagSet::NAMES
        .iter()
        .filter(|(_, bit)| !bit.intersect(t).is_empty())
        .map(|(n, _)| *n)
        .collect();
    format!("{{{}}}", names.join(","))
}

fn num_quals(n: &NumInfo, implied: &NumInfo, out: &mut String) {
    if n.range != implied.range {
        if let Some(r) = n.range {
            write!(out, " range[{},{}]", r.lo, r.hi).unwrap();
        }
    }
    if n.integral && !implied.integral {
        out.push_str(" integral");
    }
    if !n.may_neg_zero && implied.may_neg_zero {
        out.push_str(" nonegz");
    }
    if !n.may_nan && implied.may_nan {
        out.push_str(" nonan");
    }
}

pub fn kind_str(k: ObjKind) -> String {
    match k {
        ObjKind::Any => "Any".into(),
        ObjKind::Native => "Native".into(),
        ObjKind::Plain => "Plain".into(),
        ObjKind::Array => "Array".into(),
        ObjKind::Function(None) => "Function".into(),
        ObjKind::Function(Some(s)) => format!("Function(s{s})"),
        ObjKind::TypedArray(t) => format!("TypedArray({t:?})"),
        ObjKind::Arguments => "Arguments".into(),
        ObjKind::Env => "Env".into(),
    }
}

pub fn keys_str(k: &KeyRange) -> String {
    if k.lo == k.hi {
        format!("L{}", k.lo)
    } else {
        format!("L{}..L{}", k.lo, k.hi)
    }
}

fn claim_str(c: &LayoutClaim) -> String {
    let mut s = keys_str(&c.keys);
    if c.types {
        s.push_str(" types");
    }
    match c.state {
        LayoutState::Published => {}
        LayoutState::Prefix(n) => write!(s, " prefix({n})").unwrap(),
        LayoutState::Constructing(n) => write!(s, " constructing({n})").unwrap(),
    }
    s
}

fn obj_str(o: &ObjInfo) -> String {
    let mut items = vec![];
    if o.kind != ObjKind::Any {
        items.push(kind_str(o.kind));
    }
    if let Some(s) = o.singleton {
        items.push(s.to_string());
    }
    if let Some(c) = &o.layout {
        items.push(claim_str(c));
    }
    if items.is_empty() {
        "obj".into()
    } else {
        format!("obj{{{}}}", items.join(", "))
    }
}

fn str_str(m: Option<&Module>, s: &StrInfo) -> String {
    match s.atom {
        Some(a) => format!("str{{{}}}", atom(m, a)),
        None => "str".into(),
    }
}

pub fn type_str(t: &Type) -> String {
    type_str_in(None, t)
}

pub fn type_str_in(m: Option<&Module>, t: &Type) -> String {
    let mut s = String::new();
    match t {
        Type::Val(v) => {
            s.push_str("val");
            if v.tags != TagSet::ALL {
                s.push_str(&tags_str(v.tags));
            }
            if v.tags.has_number() {
                num_quals(&v.num, &VSet::implied_num(v.tags), &mut s);
            }
            if v.tags.object && v.obj != ObjInfo::TOP {
                write!(s, " {}", obj_str(&v.obj)).unwrap();
            }
            if v.tags.has_string() && v.str != StrInfo::TOP {
                write!(s, " {}", str_str(m, &v.str)).unwrap();
            }
        }
        Type::I32(r) | Type::Int(r) => {
            let (name, full) = match t {
                Type::I32(_) => ("i32", IRange::I32),
                _ => ("int", IRange::INT),
            };
            s.push_str(name);
            if *r != full {
                write!(s, "[{},{}]", r.lo, r.hi).unwrap();
            }
        }
        Type::F64(n) => {
            s.push_str("f64");
            num_quals(n, &NumInfo::TOP, &mut s);
        }
        Type::Bool => s.push_str("bool"),
        Type::Obj(o) => s.push_str(&obj_str(o)),
        Type::Str(x) => s.push_str(&str_str(m, x)),
        Type::Raw(RawKind::Elements) => s.push_str("raw.elements"),
        Type::Raw(RawKind::Slots) => s.push_str("raw.slots"),
        Type::Raw(RawKind::TaData) => s.push_str("raw.tadata"),
        Type::W32 => s.push_str("w32"),
        Type::W64 => s.push_str("w64"),
        Type::Fact(FactKind::Fuse(f)) => write!(s, "fact.fuse({f})").unwrap(),
        Type::Fact(FactKind::Binding(b)) => write!(s, "fact.binding({b})").unwrap(),
        Type::Fact(FactKind::NativeIntact(n)) => write!(s, "fact.native({n})").unwrap(),
    }
    s
}

pub fn kill_str(p: &KillPattern) -> String {
    let names: Vec<_> = KillSet::NAMES
        .iter()
        .filter(|(_, k)| p.set.contains(*k))
        .map(|(n, _)| *n)
        .collect();
    let mut s = names.join(",");
    if let Some(k) = &p.keys {
        write!(s, " in {}", keys_str(k)).unwrap();
    }
    s
}

fn f64_str(bits: u64) -> String {
    format!("{:?}", f64::from_bits(bits))
}

fn arith_name(a: ArithOp) -> &'static str {
    match a {
        ArithOp::Add => "add",
        ArithOp::Sub => "sub",
        ArithOp::Mul => "mul",
    }
}

pub fn cc_name(c: Cc) -> &'static str {
    match c {
        Cc::Eq => "eq",
        Cc::Ne => "ne",
        Cc::Lt => "lt",
        Cc::Le => "le",
        Cc::Gt => "gt",
        Cc::Ge => "ge",
    }
}

pub fn f64op_name(o: F64Op) -> &'static str {
    match o {
        F64Op::Add => "add",
        F64Op::Sub => "sub",
        F64Op::Mul => "mul",
        F64Op::Div => "div",
        F64Op::Mod => "mod",
    }
}

pub fn bitop_name(o: BitOp) -> &'static str {
    match o {
        BitOp::And => "and",
        BitOp::Or => "or",
        BitOp::Xor => "xor",
        BitOp::Shl => "shl",
        BitOp::Shr => "shr",
    }
}

pub fn math_name(f: MathFn) -> String {
    format!("{f:?}").to_ascii_lowercase()
}

pub fn js_binop_name(b: JsBinop) -> String {
    format!("{b:?}").to_ascii_lowercase()
}

pub fn js_unop_name(u: JsUnop) -> String {
    format!("{u:?}").to_ascii_lowercase()
}

pub fn js_cc_name(c: JsCc) -> String {
    format!("{c:?}").to_ascii_lowercase()
}

/// The mnemonic, including any immediates folded into it.
pub fn mnemonic(op: &Opcode) -> String {
    use Opcode::*;
    match op {
        ConstVal(_) => "const.val".into(),
        ConstI32(_) => "const.i32".into(),
        ConstF64(_) => "const.f64".into(),
        ConstBool(_) => "const.bool".into(),
        ConstObj(_) => "const.obj".into(),
        ConstStr(_) => "const.str".into(),
        Box => "box".into(),
        Unbox(k) => format!("unbox.{}", k.name()),
        I32ToInt => "i32.to_int".into(),
        I32ToF64 => "i32.to_f64".into(),
        IntToF64 => "int.to_f64".into(),
        Weaken => "weaken".into(),
        GuardUnbox(k) => format!("guard.unbox.{}", k.name()),
        GuardTags(_) => "guard.tags".into(),
        GuardKind(_) => "guard.kind".into(),
        GuardLayout { .. } => "guard.layout".into(),
        GuardSingleton(_) => "guard.singleton".into(),
        GuardScript(_) => "guard.script".into(),
        F64ToIntExact => "f64.to_int_exact".into(),
        CheckFuse(_) => "check.fuse".into(),
        CheckBinding(_) => "check.binding".into(),
        CheckNative(_) => "check.native".into(),
        Jump => "jump".into(),
        Br => "br".into(),
        Switch(_) => "switch".into(),
        Return => "return".into(),
        Exit { .. } => "exit".into(),
        ExitThrow { .. } => "exit.throw".into(),
        Unreachable => "unreachable".into(),
        I32Ovf(a) => format!("i32.{}.ovf", arith_name(*a)),
        I32Wrap(a) => format!("i32.{}.wrap", arith_name(*a)),
        IntArith(a) => format!("int.{}", arith_name(*a)),
        F64Arith(o) => format!("f64.{}", f64op_name(*o)),
        F64Neg => "f64.neg".into(),
        I32Bit(b) => format!("i32.{}", bitop_name(*b)),
        I32Ushr => "i32.ushr".into(),
        ToInt32 => "to_int32".into(),
        Cmp(r, c) => format!(
            "{}.cmp.{}",
            match r {
                NumRepr::I32 => "i32",
                NumRepr::Int => "int",
                NumRepr::F64 => "f64",
            },
            cc_name(*c)
        ),
        Math(f) => format!("math.{}", math_name(*f)),
        JsAdd => "js.add".into(),
        JsBinop(b) => format!("js.binop.{}", js_binop_name(*b)),
        JsUnop(u) => format!("js.unop.{}", js_unop_name(*u)),
        JsCompare(c) => format!("js.compare.{}", js_cc_name(*c)),
        JsTypeof => "js.typeof".into(),
        JsToBool => "js.tobool".into(),
        JsToNumeric => "js.tonumeric".into(),
        JsGetProp(_) => "js.getprop".into(),
        JsSetProp(_) => "js.setprop".into(),
        JsGetElem => "js.getelem".into(),
        JsSetElem => "js.setelem".into(),
        JsGetName(_) => "js.getname".into(),
        LoadField(_) => "load_field".into(),
        StoreField(_) => "store_field".into(),
        InitField(_) => "init_field".into(),
        PublishLayout => "publish_layout".into(),
        NewObject(_) => "new_object".into(),
        NewArray => "new_array".into(),
        LoadElem => "load_elem".into(),
        StoreElem => "store_elem".into(),
        LoadTa => "load_ta".into(),
        StoreTa => "store_ta".into(),
        LengthArray => "length.array".into(),
        LengthString => "length.string".into(),
        LengthTa => "length.ta".into(),
        ElementsPtr => "elements_ptr".into(),
        StrCharCodeAt => "str.char_code_at".into(),
        LoadGName(_) => "load_gname".into(),
        StoreGName(_) => "store_gname".into(),
        EnvCurrent => "env.current".into(),
        EnvParent => "env.parent".into(),
        EnvLoad(_) => "env.load".into(),
        EnvStore(_) => "env.store".into(),
        Call => "call".into(),
        CallDirect => "call_direct".into(),
        Construct => "construct".into(),
        CallNative(_) => "call_native".into(),
    }
}

/// The immediates printed after the operands (not the ones folded into
/// the mnemonic).
fn immediates(m: &Module, op: &Opcode) -> Option<String> {
    use Opcode::*;
    Some(match op {
        ConstVal(c) => match c {
            crate::mir::ops::ConstVal::Undefined => "undefined".into(),
            crate::mir::ops::ConstVal::Null => "null".into(),
            crate::mir::ops::ConstVal::Bool(b) => b.to_string(),
            crate::mir::ops::ConstVal::Int32(n) => format!("int32 {n}"),
            crate::mir::ops::ConstVal::Double(bits) => format!("double {}", f64_str(*bits)),
        },
        ConstI32(n) => n.to_string(),
        ConstF64(bits) => f64_str(*bits),
        ConstBool(b) => b.to_string(),
        ConstObj(s) | GuardSingleton(s) => s.to_string(),
        ConstStr(a) | JsGetProp(a) | JsSetProp(a) | JsGetName(a) | LoadField(a) | StoreField(a)
        | InitField(a) => atom(Some(m), *a),
        GuardTags(t) => tags_str(*t),
        GuardKind(k) => kind_str(*k),
        GuardLayout { keys, types } => {
            let mut s = keys_str(keys);
            if *types {
                s.push_str(" types");
            }
            s
        }
        GuardScript(s) => format!("s{s}"),
        CheckFuse(f) => f.to_string(),
        CheckBinding(b) | LoadGName(b) | StoreGName(b) => b.to_string(),
        CheckNative(n) | CallNative(n) => n.to_string(),
        NewObject(k) => format!("L{k}"),
        EnvLoad(s) | EnvStore(s) => s.to_string(),
        _ => return None,
    })
}

fn region_str(m: &Module, r: &Region) -> String {
    match r {
        Region::Field { name, keys } => format!(
            "field({}, {})",
            keys.as_ref().map_or("*".to_string(), keys_str),
            atom(Some(m), *name)
        ),
        Region::Elements(root) => {
            format!("elements({})", root.map_or("*".into(), |r| format!("r{r}")))
        }
        Region::ArrayLength(root) => format!(
            "arraylength({})",
            root.map_or("*".into(), |r| format!("r{r}"))
        ),
        Region::TypedArrayData(k) => format!("tadata({k:?})"),
        Region::TypedArrayLength => "talength".into(),
        Region::Global(b) => format!("global({b})"),
        Region::Env(s) => format!("env({s})"),
        Region::Unknown => "unknown".into(),
    }
}

fn vlist(vs: &[crate::mir::entity::Value]) -> String {
    let parts: Vec<_> = vs.iter().map(|v| v.to_string()).collect();
    format!("[{}]", parts.join(", "))
}

pub fn print_module(m: &Module) -> String {
    let mut out = String::new();
    let has_tables = !m.atoms.is_empty()
        || !m.layouts.is_empty()
        || !m.snap_objs.is_empty()
        || !m.fuses.is_empty()
        || !m.bindings.is_empty()
        || !m.natives.is_empty()
        || !m.regions.is_empty();
    if has_tables {
        out.push_str("module {\n");
        for (_, a) in m.atoms.iter() {
            writeln!(out, "  atom {}", atom_str(a)).unwrap();
        }
        for (k, l) in &m.layouts {
            let fields: Vec<_> = l
                .fields
                .iter()
                .map(|f| {
                    format!(
                        "{}: {}",
                        atom(Some(m), f.name),
                        type_str_in(Some(m), &f.claim)
                    )
                })
                .collect();
            if fields.is_empty() {
                write!(out, "  layout L{k} = {{}}").unwrap();
            } else {
                write!(out, "  layout L{k} = {{ {} }}", fields.join(", ")).unwrap();
            }
            if let Some(r) = l.elements {
                write!(out, " elements r{r}").unwrap();
            }
            out.push('\n');
        }
        for (s, d) in m.snap_objs.iter() {
            writeln!(out, "  snap {s} = {}", kind_str(d.kind)).unwrap();
        }
        for (f, d) in m.fuses.iter() {
            writeln!(
                out,
                "  fuse {f} = {}",
                atom_str(&JsString::from(d.name.as_str()))
            )
            .unwrap();
        }
        for (b, d) in m.bindings.iter() {
            writeln!(
                out,
                "  binding {b} = {} : {}",
                atom(Some(m), d.name),
                type_str_in(Some(m), &d.claim)
            )
            .unwrap();
        }
        for (n, d) in m.natives.iter() {
            writeln!(
                out,
                "  native {n} = {}",
                atom_str(&JsString::from(d.name.as_str()))
            )
            .unwrap();
        }
        for (r, d) in m.regions.iter() {
            writeln!(out, "  region {r} = {}", region_str(m, d)).unwrap();
        }
        out.push_str("}\n");
    }
    for f in &m.funcs {
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(&print_func(m, f));
    }
    out
}

pub fn print_func(m: &Module, f: &Func) -> String {
    let ty = |t: &Type| type_str_in(Some(m), t);
    let mut out = String::new();
    let depths: Vec<_> = f
        .frame
        .depths
        .iter()
        .map(|(pc, d)| format!("{pc}:{d}"))
        .collect();
    writeln!(
        out,
        "func @s{} (formals={}, locals={}, depths={{{}}}) {{",
        f.script,
        f.frame.formals,
        f.frame.locals,
        depths.join(", ")
    )
    .unwrap();
    for r in &f.roots {
        match r.kind {
            RootKind::Entry => writeln!(out, "  root entry {}", r.block).unwrap(),
            RootKind::Onramp(pc) => writeln!(out, "  root onramp(pc={pc}) {}", r.block).unwrap(),
        }
    }
    for l in &f.loops {
        writeln!(out, "  loop {} preheader={}", l.header, l.preheader).unwrap();
    }
    for &b in &f.layout {
        out.push('\n');
        let params: Vec<_> = f.blocks[b]
            .params
            .iter()
            .map(|&v| format!("{v}: {}", ty(&f.values[v].ty)))
            .collect();
        if params.is_empty() {
            writeln!(out, "{b}:").unwrap();
        } else {
            writeln!(out, "{b}({}):", params.join(", ")).unwrap();
        }
        for &inst in &f.blocks[b].insts {
            let d = &f.insts[inst];
            out.push_str("  ");
            // Results: types only where the rule would not infer them.
            let arg_tys: Vec<Type> = d.args.iter().map(|&v| f.values[v].ty).collect();
            let inferred = signature(&d.op, &arg_tys, m).ok().map(|s| s.results);
            if !d.results.is_empty() {
                let rs: Vec<_> = d
                    .results
                    .iter()
                    .enumerate()
                    .map(|(i, &v)| {
                        let t = f.values[v].ty;
                        if inferred.as_ref().and_then(|r| r.get(i)) == Some(&t) {
                            v.to_string()
                        } else {
                            format!("{v}: {}", ty(&t))
                        }
                    })
                    .collect();
                write!(out, "{} = ", rs.join(", ")).unwrap();
            }
            out.push_str(&mnemonic(&d.op));
            if let Some((pc, nargs, nlocals)) = d.op.exit_shape() {
                match crate::mir::ops::frame_parts(&d.args, nargs, nlocals) {
                    Some(fp) => write!(
                        out,
                        " pc={pc} this={} args={} locals={} rval={} stack={}",
                        fp.this,
                        vlist(fp.args),
                        vlist(fp.locals),
                        fp.rval,
                        vlist(fp.stack)
                    )
                    .unwrap(),
                    // Malformed (too few operands): print them raw, so the
                    // validator's complaint can be read against the text.
                    None => write!(out, " pc={pc} raw={}", vlist(&d.args)).unwrap(),
                }
            } else {
                let args: Vec<_> = d.args.iter().map(|v| v.to_string()).collect();
                if !args.is_empty() {
                    write!(out, " {}", args.join(", ")).unwrap();
                }
                if let Some(imm) = immediates(m, &d.op) {
                    write!(out, " {imm}").unwrap();
                }
            }
            if !d.succs.is_empty() {
                let roles = d.op.roles();
                let edges: Vec<_> = d
                    .succs
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        let mut next_out = 0;
                        let args: Vec<_> = e
                            .args
                            .iter()
                            .enumerate()
                            .map(|(j, a)| match a {
                                EdgeArg::Value(v) => v.to_string(),
                                EdgeArg::Out(k) => {
                                    let p = f
                                        .blocks
                                        .get(e.block)
                                        .and_then(|bd| bd.params.get(j))
                                        .copied();
                                    let mut s = match p {
                                        Some(p) => format!("{p}: {}", ty(&f.values[p].ty)),
                                        None => "?".into(),
                                    };
                                    if *k != next_out {
                                        write!(s, " = %{k}").unwrap();
                                    }
                                    next_out = k + 1;
                                    s
                                }
                            })
                            .collect();
                        let target = if args.is_empty() {
                            e.block.to_string()
                        } else {
                            format!("{}({})", e.block, args.join(", "))
                        };
                        match (&d.op, roles.get(i)) {
                            (Opcode::Jump, _) => target,
                            (_, Some(r)) => format!("{} {target}", r.name()),
                            (_, None) => format!("extra {target}"),
                        }
                    })
                    .collect();
                if d.op == Opcode::Jump {
                    write!(out, " {}", edges.join(", ")).unwrap();
                } else {
                    write!(out, " -> {}", edges.join(", ")).unwrap();
                }
            }
            if let Some(a) = d.attach {
                let at = &f.attachments[a];
                let mut items = vec![];
                if let Some(s) = at.site {
                    items.push(format!("site={}:{}", s.script, s.pc));
                }
                if let Some(c) = at.ic_cell {
                    items.push(format!("ic={c:#x}"));
                }
                if let Some(c) = at.call_cell {
                    items.push(format!("call={c:#x}"));
                }
                if let Some(s) = at.slot {
                    items.push(format!("slot={s}"));
                }
                if let Some(k) = at.field_mask {
                    items.push(format!("mask={k:#x}"));
                }
                if !at.targets.is_empty() {
                    let ts: Vec<_> = at.targets.iter().map(|s| format!("s{s}")).collect();
                    items.push(format!("targets=[{}]", ts.join(", ")));
                }
                write!(out, " @{{{}}}", items.join(", ")).unwrap();
            }
            if let Some(w) = f.witness(inst) {
                write!(out, " !pred{{{}}}", kill_str(&w.may_kill)).unwrap();
            }
            out.push('\n');
        }
    }
    out.push_str("}\n");
    out
}
