/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! AOT Wasm codegen: the emitter submodule.
//!
//! `layout_env` runs the analysis prepass and computes the reserved
//! linear-memory region layout; `translate_all` compiles every compilable
//! script (and regex program) into a Wasm function body (see `translate`);
//! the rest run interpreted. Consumed by the in-process batch builder
//! (`inprocess`, via the `night_inproc_build` FFI) and by the external
//! snapshot compiler (`js/src/night/nightmonkey`).

use crate::facts::{Claim, LikelyFacts};
use crate::ids::{JsString, LayoutKey, NameId, Names, Pc, RegionRoot, ScriptId, Site, StampKey};
use crate::opsem::ValueRange;
use waffle::{ExportKind, Func, FuncDecl, Module, Operator, SignatureData, Table, Type, ValueDef};

use crate::options::Options;
use crate::region_shape as shape;
use crate::source::{ObjectData, ObjectKind, Source, SourceObject, SourceObjectId};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

pub(crate) mod bbv;
pub use bbv::EARLY_KEY_MAX;

/// The image-patch constants for snapshot-object stamping (nightmonkey's
/// main patches the class word straight into the snapshot bytes): the
/// likely-class word's byte offset in a JSObject, and the SLOTS validity
/// bit. Values mirror `bbv::abi` (OBJ_CLASS_IDX_OFFSET, CLASS_WORD_SLOTS).
pub mod stamp {
    pub const WORD_OFFSET: u32 = 4;
    pub const SLOTS: u32 = 0x0002_0000;
    pub const SHAPE_OFFSET: u32 = super::bbv::abi::SHAPE_OFFSET;
    pub const SHAPE_IMMUTABLE_FLAGS_OFFSET: u32 = super::bbv::abi::SHAPE_IMMUTABLE_FLAGS_OFFSET;
    pub const SHAPE_FIXED_SLOTS_SHIFT: u32 = super::bbv::abi::SHAPE_FIXED_SLOTS_SHIFT;
    pub const SHAPE_FIXED_SLOTS_MASK_BITS: u32 = super::bbv::abi::SHAPE_FIXED_SLOTS_MASK_BITS;
}
pub use bbv::{
    build_call_classify_helper, build_elem_append_helper, build_elem_mega_helpers,
    build_ic_set_cold_helper,
};
pub(crate) mod effects;
pub mod inprocess;
pub mod regex;
pub mod translate;

pub fn find_export_func(m: &Module, name: &str) -> Result<Func, String> {
    m.exports
        .iter()
        .find_map(|e| match &e.kind {
            ExportKind::Func(f) if e.name == name => Some(*f),
            _ => None,
        })
        .ok_or_else(|| format!("runtime export `{name}` not found"))
}

/// The shared C-function-pointer table (`__indirect_function_table`). Prefer
/// the export of that name; fall back to the single defined table.
pub fn find_indirect_table(m: &Module) -> Result<Table, String> {
    for e in &m.exports {
        if let ExportKind::Table(t) = &e.kind {
            if e.name == "__indirect_function_table" {
                return Ok(*t);
            }
        }
    }
    m.tables
        .iter()
        .next()
        .ok_or_else(|| "runtime module has no table".to_string())
}

/// Place `func` in `__indirect_function_table` at the next free index and
/// return that index (the C-function-pointer value). The backend emits one
/// active elem segment per entry at its index; bump `initial` to cover it.
pub fn place_in_table(m: &mut Module, func: Func) -> Result<u32, String> {
    let table = find_indirect_table(m)?;
    let elems = m.tables[table]
        .func_elements
        .as_mut()
        .ok_or_else(|| "indirect table has no func_elements".to_string())?;
    let index = elems.len() as u32;
    elems.push(func);
    if (m.tables[table].initial as u32) < index + 1 {
        m.tables[table].initial = u64::from(index + 1);
    }
    Ok(index)
}

/// A `night_abi_sig` adapter for a widened-ABI body: forwards the params,
/// calls the body, drops the `eff` result, returns `err`. This is what
/// sits in the C-visible funcref table (and behind `nightFuncIndex`), so
/// the runtime's `NightFn` pointer type and every `call_indirect` keep the
/// single-result signature; only patched direct calls see multivalue.
fn abi_adapter(m: &mut Module, sig1: waffle::Signature, body_fn: Func, sid: u32) -> Func {
    let mut b = waffle::FunctionBody::new(m, sig1);
    let entry = b.entry;
    let params: Vec<waffle::Value> = b.blocks[entry].params.iter().map(|&(_, v)| v).collect();
    let arg_list = b.arg_pool.from_iter(params.into_iter());
    let tys = b.type_pool.from_iter([Type::I32, Type::I32].into_iter());
    let call = b.add_value(ValueDef::Operator(
        Operator::Call {
            function_index: body_fn,
        },
        arg_list,
        tys,
    ));
    b.append_to_block(entry, call);
    let err = b.add_value(ValueDef::PickOutput(call, 0, Type::I32));
    b.append_to_block(entry, err);
    b.set_terminator(entry, waffle::Terminator::Return { values: vec![err] });
    m.funcs
        .push(FuncDecl::Body(sig1, format!("night_adapter_{sid}"), b))
}

/// Patch each `(func, value, row)` site's reserved `I32Const` placeholder to
/// `base + stride * row`. Shared by the cell-region and string-literal patch
/// passes, which differ only in `base` and `stride`.
pub fn patch_const(
    m: &mut Module,
    patches: Vec<(Func, waffle::Value, u32)>,
    base: u32,
    stride: u32,
) {
    for (f, addr, row) in patches {
        if let FuncDecl::Body(_, _, body) = &mut m.funcs[f] {
            if let ValueDef::Operator(Operator::I32Const { value }, _, _) = &mut body.values[addr] {
                *value = base + stride * row;
            }
        }
    }
}

/// Serialize the regex matcher descriptor table: `u32 count`, then per entry
/// `u32 flags, u32 latin1_tableidx, u32 twobyte_tableidx (0 = no matcher),
/// u32 num_registers, u32 pair_count, u32 pattern_len, pattern_len x u16`.
/// Parsed by `night_runtime_install_env`; matched against live `RegExpShared`s by
/// (pattern chars, flags). Little-endian throughout.
pub fn serialize_regex_table(entries: &[(JsString, u32, u32, u32, u32, u32)]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    for (pattern, flags, l1, tb, nregs, pairs) in entries {
        out.extend_from_slice(&flags.to_le_bytes());
        out.extend_from_slice(&l1.to_le_bytes());
        out.extend_from_slice(&tb.to_le_bytes());
        out.extend_from_slice(&nregs.to_le_bytes());
        out.extend_from_slice(&pairs.to_le_bytes());
        out.extend_from_slice(&(pattern.len() as u32).to_le_bytes());
        for &u in pattern.chars() {
            out.extend_from_slice(&u.to_le_bytes());
        }
    }
    out
}

/// Likely this-layout table: `u32 flags`, `u32 count`, then per layout (in
/// layout_id order) `u32 nfields` + nfields x `u32 atomId` (field index
/// order == predicted slot) + `u32` add-check bound. Interned before the
/// atom table serializes (the ids must be in it).
///
/// The compiled code does not read this table -- it bakes each site's slot
/// as an immediate, exactly as the review expects. The table exists for the
/// *other* side of the stamp: the engine's property-add chokepoint
/// (`js::night::NightAddPropCheck`, called whenever an interpreted body or
/// a generic helper adds a property to an object) has to decide what an add
/// does to the receiver's SLOTS stamp bit, and it only has the receiver's
/// class-idx word to go on. The table is how that word becomes a field
/// list.
///
/// Unconditionally clearing the bit there would be sound and much simpler,
/// and it is the wrong trade: the adds that build an object are exactly the
/// ones that would clear it. A two-phase constructor's init delegate adds
/// the tail of the row after the prefix stamp lands, and every one of those
/// adds is a name the layout predicts at the slot it is landing in. With
/// the table the hook keeps the bit through them (and through a clump
/// extension adding past a prefix); without it the stamp would be dead by
/// the time the object escaped its constructor. The per-layout add-check
/// bound serialized alongside is the same idea one step cheaper -- an add
/// past the clump's longest prefix cannot be inside any guarded prefix, so
/// the hook returns before the name search.
pub fn serialize_layout_table(env: &EnvLayout, atoms: &mut translate::AtomTable) -> Vec<u8> {
    let mut out = Vec::new();
    let flags: u32 = env.layout_mode;
    out.extend_from_slice(&flags.to_le_bytes());
    out.extend_from_slice(&(env.layout_ctors.len() as u32).to_le_bytes());
    for &ctor in &env.layout_ctors {
        let fields = &env.likely_class_layouts[&ctor];
        out.extend_from_slice(&(fields.len() as u32).to_le_bytes());
        for &name in fields {
            out.extend_from_slice(&atoms.intern(name).to_le_bytes());
        }
        // The add-check bound (see StampCtorIn::ext_bound): the runtime
        // fills the static bound table (the retired guard cells' region)
        // from this at install.
        let max_len = env
            .layout_ctors
            .iter()
            .filter(|&&e| {
                let ef = &env.likely_class_layouts[&e];
                ef.len() >= fields.len() && ef[..fields.len()] == fields[..]
            })
            .map(|&e| env.likely_class_layouts[&e].len())
            .max()
            .unwrap_or(fields.len());
        let bound = translate::FIXED_SLOTS_BASE + 8 * u32::try_from(max_len).unwrap();
        out.extend_from_slice(&bound.to_le_bytes());
    }
    out
}

/// Gname fuse table: u32 count, then per fused binding u32 atomId + u64
/// predicted literal bits (fuse cell index == position).
pub fn serialize_fuse_table(env: &EnvLayout, atoms: &mut translate::AtomTable) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(env.fused_list.len() as u32).to_le_bytes());
    for &(name, bits) in &env.fused_list {
        out.extend_from_slice(&atoms.intern(name).to_le_bytes());
        out.extend_from_slice(&bits.to_le_bytes());
    }
    out
}

/// Serialize the property-name atom table: `u32 count`, then `count` ×
/// (`u32 char_len`, `char_len` × `u16` UTF-16 code units). `atomId` is the
/// index. `night_runtime_install_env` interns each to a `JSAtom*`; the generic
/// property helpers index by `atomId`. Little-endian throughout.
pub fn serialize_atom_table(atoms: &translate::AtomTable) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(atoms.emitted_len() as u32).to_le_bytes());
    for name in atoms.emitted_names() {
        out.extend_from_slice(&(name.len() as u32).to_le_bytes());
        for &u in name.chars() {
            out.extend_from_slice(&u.to_le_bytes());
        }
    }
    out
}

/// Serialize the global-binding name table: `u32 count`, then `count` ×
/// (`u32 char_len`, `char_len` × `u16` UTF-16 code units), in `binding_id`
/// order. The reactor pre-interns each to a `PropertyKey` at startup (mirroring
/// `gAtomIds`) so the lazy `night_runtime_resolve_global_slot` `lookupPure` never
/// re-atomizes. Little-endian throughout.
// Per binding: the UTF-16 name, then a u32 expected-callee word (the
// funcref-table index + 1 of the predicted callee for fuse-guarded direct
// calls at this binding's gname-callee sites; 0 = no call prediction). The
// reactor's arm-time validation compares the armed value's AOT target
// against it.
pub fn serialize_global_binding_table(
    tbl: &Names,
    names: &[NameId],
    expected_index: &HashMap<u32, u32>,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(names.len() as u32).to_le_bytes());
    for (i, &nid) in names.iter().enumerate() {
        let name = tbl.get(nid);
        out.extend_from_slice(&(name.len() as u32).to_le_bytes());
        for &u in name.chars() {
            out.extend_from_slice(&u.to_le_bytes());
        }
        let exp = expected_index
            .get(&u32::try_from(i).unwrap())
            .map(|&idx| idx + 1)
            .unwrap_or(0);
        out.extend_from_slice(&exp.to_le_bytes());
    }
    out
}

/// Likely-callee facts: top-level `function
/// f(){}` declarations whose global binding is never syntactically reassigned
/// anywhere in the bundle. A call site whose callee operand provably came from
/// `GetGName f` gets a guarded direct-call arm (runtime `nightFuncIndex`
/// identity compare against the declaration's table index), so a wrong likely
/// costs one compare, never correctness -- eval/Function-constructor
/// reassignment is caught by the guard.
fn collect_likely_gname_fns(
    source: &Source,
    root_id: SourceObjectId,
    names: &mut Names,
) -> HashMap<NameId, ScriptId> {
    use crate::bytecode::OpcodeVisitor;
    let SourceObject::Script(root) = source.object(root_id) else {
        return HashMap::default();
    };
    // Candidates: the root script's named function gcthings (top-level
    // declarations and named top-level lambdas). A duplicated name is
    // dropped (re-declaration: last-wins semantics are not worth modeling).
    let mut cand: HashMap<NameId, Option<ScriptId>> = HashMap::default();
    for &g in &root.gcthings {
        if g.is_other() {
            continue;
        }
        if let SourceObject::Object(ObjectData {
            kind: ObjectKind::Function,
            script: Some(sid),
            name: Some(nid),
            ..
        }) = source.object(g)
        {
            if let SourceObject::String(n) = source.object(*nid) {
                cand.entry(names.intern(n))
                    .and_modify(|e| *e = None)
                    .or_insert(Some(ScriptId::new(sid.id())));
            }
        }
    }
    // Exclusions: any syntactic global-name write in any script (compiled or
    // interpreted) drops the name -- the guard would just always miss.
    struct Scan<'a> {
        source: &'a Source,
        script: &'a crate::bytecode::Script,
        written: &'a mut Vec<NameId>,
        names: &'a mut Names,
    }
    impl Scan<'_> {
        fn name(&mut self, idx: u32) {
            if let Some(&g) = self.script.gcthings.get(idx as usize) {
                if !g.is_other() {
                    if let SourceObject::String(sname) = self.source.object(g) {
                        let id = self.names.intern(sname);
                        self.written.push(id);
                    }
                }
            }
        }
    }
    impl OpcodeVisitor for Scan<'_> {
        fn set_g_name(&mut self, i: u32) {
            self.name(i);
        }
        fn strict_set_g_name(&mut self, i: u32) {
            self.name(i);
        }
        fn set_name(&mut self, i: u32) {
            self.name(i);
        }
        fn strict_set_name(&mut self, i: u32) {
            self.name(i);
        }
    }
    let mut written: Vec<NameId> = Vec::new();
    for (_id, obj) in source.objects() {
        if let SourceObject::Script(script) = obj {
            script.parser().visit(Scan {
                source,
                script,
                written: &mut written,
                names,
            });
        }
    }
    for w in &written {
        cand.remove(w);
    }
    cand.into_iter()
        .filter_map(|(k, v)| v.map(|sid| (k, sid)))
        .collect()
}

/// Whether the static program text can never produce a BigInt value: any
/// BigInt literal, any referenced name equal to a BigInt-family global, any
/// eval op, or any referenced `eval` name (an indirect-eval alias compiles
/// as a plain call, not an Eval op) makes it return false.
///
/// # Why this is answered statically rather than by a guard
///
/// The natural objection is that a guard should do this: test for an
/// Int32/Number tag on the path that needs one, or read a fuse word. Both
/// are already how the surrounding code works, and neither can produce the
/// thing this answer is used for.
///
/// The claim is not a *guard*, it is a *type*. Its consumer is
/// `bbv::emit::bigint_result`: the generic arithmetic arm's helper returns
/// a boxed value whose type, by the spec of `+`, is `Int32|Double|BigInt`.
/// The tag tests the reviewer would reach for already ran -- they are the
/// arms this value fell out of, and it is the residue they did not claim.
/// Testing its tag again would not remove a cost, it would add one, because
/// a type is what the *next* op consumes: the BigInt bit is what makes
/// `is_numeric` false, and `is_numeric` is what routes the next arithmetic
/// op onto the unboxed f64 track instead of the fully generic tag-guarded
/// ladder. So the price of not having this answer is not one test here, it
/// is the typed continuation of the whole downstream chain. And this tier
/// has no deopt landing, so the only recovery from a failed type claim is a
/// second version -- which is precisely what `bigint_result` emits. Doing
/// that per value instead of per module would mean a version split at every
/// arithmetic result in the program.
///
/// A fuse word is the right shape, and half of the answer already is one.
/// A fuse needs a chokepoint: one place the engine can blow it from, cheap
/// enough that every JS program pays for it. "Unscanned source text has been
/// compiled" has such a place -- `ScriptSource::assignSource` -- which is
/// why that half *is* a fuse (`Helpers::dyncode_fuse_word`, blown by
/// `js::night::NightBlowDynamicCodeFuse`), and why this function does not
/// try to answer for `new Function("...1n...")` or an indirect eval reached
/// without naming `eval`. "A BigInt exists somewhere reachable" has no such
/// place. A BigInt is an ordinary heap value: a literal, `BigInt(x)`, a
/// `BigInt64Array` read, `JS::NumberToBigInt` from an embedder. Blowing a
/// fuse at each would put a store on every BigInt creation in SpiderMonkey
/// -- a cost paid by all of JS to serve this tier -- and would still have to
/// cover values arriving across the embedder boundary. Reading the program
/// text costs nothing at runtime and answers the same question for the
/// bundles this tier compiles.
///
/// # What it assumes
///
/// That the registered scripts are the whole program. A BigInt already
/// sitting in the wizened heap, or one handed back by an embedder native
/// the text calls without naming any BigInt global, is covered by neither
/// this scan nor the dyncode fuse. That holds for the deployment this tier
/// targets -- a bundle registered at wizen time, with the shell as the only
/// embedder -- but it is an assumption about the embedding, not a proof
/// about the language, and an embedder that hands BigInts to unscanned code
/// would need a third mechanism.
fn module_is_bigint_free(source: &Source, script_ids: &[SourceObjectId]) -> bool {
    const NAMES: [&[u16]; 4] = [
        &[66, 105, 103, 73, 110, 116], // "BigInt"
        &[66, 105, 103, 73, 110, 116, 54, 52, 65, 114, 114, 97, 121], // "BigInt64Array"
        &[
            66, 105, 103, 85, 105, 110, 116, 54, 52, 65, 114, 114, 97, 121,
        ], // "BigUint64Array"
        &[101, 118, 97, 108],          // "eval"
    ];
    struct Scan {
        found: bool,
    }
    impl crate::bytecode::OpcodeVisitor for Scan {
        fn bigint(&mut self, _bigint_index: u32) {
            self.found = true;
        }
        fn before_op(&mut self, _pc: Pc, op: crate::bytecode::JSOp, _u: usize, _d: usize) {
            use crate::bytecode::JSOp;
            if matches!(
                op,
                JSOp::Eval | JSOp::StrictEval | JSOp::SpreadEval | JSOp::StrictSpreadEval
            ) {
                self.found = true;
            }
        }
    }
    for &id in script_ids {
        let SourceObject::Script(script) = source.object(id) else {
            continue;
        };
        // A referenced name (GetGName / GetProp / String literal for computed
        // access) appears as a String gcthing of the script.
        for &g in &script.gcthings {
            if g.is_other() {
                continue;
            }
            if let SourceObject::String(s) = source.object(g) {
                if NAMES.iter().any(|n| *n == s.chars()) {
                    return false;
                }
            }
        }
        let scan = script.parser().visit(Scan { found: false });
        if scan.found {
            return false;
        }
    }
    true
}

/// GetGName fuse: global names the root script assigns a compile-time
/// constant number/boolean/null/undefined, with the predicted boxed literal.
/// A tolerant linear constant-propagation walk of the root bytecode: literals
/// and folds over already-known globals produce constants; any control op
/// clears the abstract stack; unknown values are None. A wrong prediction is
/// Sound: the runtime helper arms a binding's fuse only when the actually
/// written value equals the prediction, and blows it on any other write.
///
/// # Why this is not just "every global name we use"
///
/// There are two global-read fast arms, and that other one already is
/// exactly that. Every syntactic `GetGName` name gets a binding id
/// (`collect_syntactic_gnames`) and, with it, a 16-byte value-fuse cell in
/// `gGlobalVals`; the runtime arms the cell with whatever value it finds,
/// and `emit_get_gname_inline_guarded`'s first arm returns those bits after
/// one fuse-word test. No compile-time prediction is involved.
///
/// This table buys the step past that: because the value is known *here*,
/// the arm pushes an IR constant rather than a load, so the read folds into
/// whatever consumes it. That is what turns a `if (VERBOSE)` or a
/// `for (i = 0; i < SIZE; i++)` over a top-level constant into no code at
/// all, and it is only available to a value the compiler holds.
///
/// # Why it is a separate walk
///
/// Because the fuse-cell address of each binding is baked into `GetGName`
/// sites as an immediate, in every script -- so the table's contents, and
/// hence its size and the base of everything laid out after it, have to be
/// final before any body is translated. Collecting it while compiling the
/// root script would need the answer before the walk that produces it, and
/// the root script is not translated first in any case: bodies come off the
/// BBV workqueue in reachability order.
fn collect_fused_gnames(
    source: &Source,
    root_id: SourceObjectId,
    names: &mut Names,
) -> Vec<(NameId, u64)> {
    use crate::bytecode::JSOp;
    let SourceObject::Script(root) = source.object(root_id) else {
        return Vec::new();
    };
    use translate::ConstValue as K;
    // JS ToInt32 for the bitop folds, restricted to already-integral values
    // in range (benchmark constants); anything else stays unknown.
    fn as_i32(k: Option<K>) -> Option<i32> {
        match k {
            Some(K::Number(f))
                if f.fract() == 0.0 && (-2147483648.0..=2147483647.0).contains(&f) =>
            {
                Some(f as i32)
            }
            _ => None,
        }
    }
    let name_of = |names: &mut Names, ni: u32| -> Option<NameId> {
        let &g = root.gcthings.get(ni as usize)?;
        if g.is_other() {
            return None;
        }
        if let SourceObject::String(s) = source.object(g) {
            Some(names.intern(s))
        } else {
            None
        }
    };
    let mut stack: Vec<Option<K>> = Vec::new();
    let mut known: HashMap<NameId, K> = HashMap::default();
    let mut out: Vec<(NameId, u64)> = Vec::new();
    let mut seen: HashSet<NameId> = HashSet::default();
    // A root-script rewrite the walk cannot prove equal to the fused
    // literal (a non-constant value, or a different constant) means the
    // fuse blows at that write and every later read runs the disarmed
    // arm forever -- the fuse table must only hold names that stay
    // armed. `written_elsewhere` below covers other scripts; this covers
    // the root's own `var X = 0; ... X++` shape (earley's counters).
    let mut poisoned: HashSet<NameId> = HashSet::default();
    let mut p = root.parser();
    loop {
        let before = p.remaining();
        let Some(op) = p.next_op() else { break };
        let len = op.len();
        use JSOp::*;
        match op {
            Zero => stack.push(Some(K::Number(0.0))),
            One => stack.push(Some(K::Number(1.0))),
            Int8 => stack.push(p.next_int8().map(|v| K::Number(f64::from(v)))),
            Uint16 => stack.push(p.next_uint16().map(|v| K::Number(f64::from(v)))),
            Uint24 => stack.push(p.next_uint24().map(|v| K::Number(v as f64))),
            Int32 => stack.push(p.next_int32().map(|v| K::Number(f64::from(v)))),
            Double => stack.push(p.next_uint64().map(|b| K::Number(f64::from_bits(b)))),
            True => stack.push(Some(K::Boolean(true))),
            False => stack.push(Some(K::Boolean(false))),
            Null => stack.push(Some(K::Null)),
            Undefined => stack.push(Some(K::Undefined)),
            GetGName => {
                let k = p
                    .next_uint32()
                    .and_then(|ni| name_of(names, ni))
                    .and_then(|n| known.get(&n).copied());
                stack.push(k);
            }
            SetGName | StrictSetGName => {
                let name = p.next_uint32().and_then(|ni| name_of(names, ni));
                let val = stack.pop().flatten();
                stack.pop();
                if let Some(n) = name {
                    match val {
                        Some(k) => {
                            if seen.insert(n) {
                                if !poisoned.contains(&n) {
                                    out.push((n, k.boxed_bits()));
                                }
                            } else if out
                                .iter()
                                .any(|&(m, bits)| m == n && bits != k.boxed_bits())
                            {
                                poisoned.insert(n);
                                out.retain(|&(m, _)| m != n);
                            }
                            known.insert(n, k);
                        }
                        None => {
                            known.remove(&n);
                            poisoned.insert(n);
                            out.retain(|&(m, _)| m != n);
                        }
                    }
                }
                stack.push(val);
            }
            BitOr | BitAnd | BitXor | Lsh | Rsh | Ursh => {
                let b = as_i32(stack.pop().flatten());
                let a = as_i32(stack.pop().flatten());
                let r = a.zip(b).map(|(a, b)| match op {
                    BitOr => a | b,
                    BitAnd => a & b,
                    BitXor => a ^ b,
                    Lsh => a.wrapping_shl(b as u32 & 31),
                    Rsh => a.wrapping_shr(b as u32 & 31),
                    _ => ((a as u32) >> (b as u32 & 31)) as i32,
                });
                // Ursh of a negative yields a >2^31 unsigned value; keep it
                // only when it stays in i32 range (as_i32 rejected it anyway).
                stack.push(r.map(|v| K::Number(f64::from(v))));
            }
            BitNot => {
                let a = as_i32(stack.pop().flatten());
                stack.push(a.map(|v| K::Number(f64::from(!v))));
            }
            Add | Sub | Mul | Div => {
                let b = stack.pop().flatten();
                let a = stack.pop().flatten();
                let r = match (a, b) {
                    (Some(K::Number(x)), Some(K::Number(y))) => Some(K::Number(match op {
                        Add => x + y,
                        Sub => x - y,
                        Mul => x * y,
                        _ => x / y,
                    })),
                    _ => None,
                };
                stack.push(r);
            }
            Neg => {
                let a = stack.pop().flatten();
                stack.push(match a {
                    Some(K::Number(x)) => Some(K::Number(-x)),
                    _ => None,
                });
            }
            Goto | JumpIfFalse | JumpIfTrue | And | Or | Coalesce | Case | Default
            | TableSwitch | JumpTarget | LoopHead | Return | RetRval | Throw | ThrowWithStack
            | ThrowMsg => stack.clear(),
            _ => {
                match op.nuses() {
                    Some(n) => {
                        for _ in 0..n {
                            stack.pop();
                        }
                    }
                    None => stack.clear(),
                }
                for _ in 0..op.ndefs() {
                    stack.push(None);
                }
            }
        }
        let consumed = before - p.remaining();
        let need = len as usize;
        if consumed < need && p.advance(need - consumed).is_none() {
            break;
        }
    }
    // A name any OTHER script writes is not a constant: its fuse blows on
    // the first such write, and every read from then on takes the
    // disarmed arm -- a Side-stepped continuation, i.e. Dirty for the rest
    // of the body (e.g. an asm.js-style module-level global reread in a
    // hot loop). Such a name reads through the guarded slot arm instead.
    let mut written_elsewhere: HashSet<NameId> = HashSet::default();
    for (id, obj) in source.objects() {
        let SourceObject::Script(script) = obj else {
            continue;
        };
        if id == root_id {
            continue;
        }
        let mut p = script.parser();
        loop {
            let before = p.remaining();
            let Some(op) = p.next_op() else { break };
            let len = op.len();
            if matches!(op, JSOp::SetGName | JSOp::StrictSetGName) {
                if let Some(n) = p.next_uint32().and_then(|ni| {
                    let &g = script.gcthings.get(ni as usize)?;
                    if g.is_other() {
                        return None;
                    }
                    match source.object(g) {
                        SourceObject::String(s) => Some(names.intern(s)),
                        _ => None,
                    }
                }) {
                    written_elsewhere.insert(n);
                }
            }
            let consumed = before - p.remaining();
            let need = len as usize;
            if consumed < need && p.advance(need - consumed).is_none() {
                break;
            }
        }
    }
    out.retain(|(n, _)| !written_elsewhere.contains(n));
    out
}

/// No-TI (global-slot guarded): every unique `GetGName` operand name across
/// the
/// compiled scripts, in first-appearance order -- the binding-id table for the
/// shape-guarded inline gname read. (Global writes keep the generic helper.)
fn collect_syntactic_gnames(source: &Source, names: &mut Names) -> Vec<NameId> {
    use crate::bytecode::OpcodeVisitor;
    struct Scan<'a> {
        source: &'a Source,
        script: &'a crate::bytecode::Script,
        out: &'a mut Vec<NameId>,
        seen: &'a mut HashSet<NameId>,
        names: &'a mut Names,
    }
    impl OpcodeVisitor for Scan<'_> {
        fn get_g_name(&mut self, name_index: u32) {
            let Some(&gc) = self.script.gcthings.get(name_index as usize) else {
                return;
            };
            let SourceObject::String(s) = self.source.object(gc) else {
                return;
            };
            let id = self.names.intern(s);
            if self.seen.insert(id) {
                self.out.push(id);
            }
        }
    }
    let mut out = Vec::new();
    let mut seen = HashSet::default();
    for (_, obj) in source.objects() {
        let SourceObject::Script(script) = obj else {
            continue;
        };
        script.parser().visit(Scan {
            source,
            script,
            out: &mut out,
            seen: &mut seen,
            names,
        });
    }
    out
}

/// The in-module pieces every Helpers needs regardless of environment.
pub struct HelperPrebuilt {
    pub mem: waffle::Memory,
    pub ta_get_poly: Func,
    pub ta_set_poly: Func,
    pub ic_get_poly: Func,
    pub ic_set_cold: Func,
    pub elem_mega_get: Func,
    pub elem_mega_set_probe: Func,
    pub call_classify: Func,
    pub elem_append_check: Func,
    pub night_abi_sig: waffle::Signature,
    pub indirect_table: Table,
    pub direct_call_stub: Func,
    pub night_abi_sig2: waffle::Signature,
    pub direct_call_stub2: Func,
}

/// The baked cell/region base addresses the translator embeds.
pub struct HelperBases {
    pub global_slots_base: u32,
    pub prop_ic_base: u32,
    pub mega_set_base: u32,
    pub accessor_cache_base: u32,
    pub prop_ic_gen_base: u32,
    pub this_cells_base: u32,
    pub this_slots_base: u32,
    pub mega_get_base: u32,
    pub night_stack_limit_base: u32,
    pub fn_class_slot: u32,
    pub static_strings_slot: u32,
    pub atom_table_slot: u32,
    pub nursery_pos_slot: u32,
    pub nursery_end_slot: u32,
    pub str_ccat_cell: u32,
    pub str_cat_cell: u32,
    pub str_fcc_cell: u32,
    pub str_fuse_addr_slot: u32,
    pub array_class_slot: u32,
    pub args_class_base: u32,
    pub strlit_slot: u32,
    pub builtin_cells_base: u32,
    pub math_natives_base: u32,
    pub append_cache_base: u32,
    pub ta_class_base: u32,
    pub global_vals_base: u32,
}

/// Build the translator Helpers, resolving each engine-helper reference
/// through `resolve` (production: an export lookup in the merged module;
/// in-process batches: a pushed function import).
pub fn resolve_helpers(
    m: &mut Module,
    resolve: &mut dyn FnMut(&mut Module, &str) -> Result<Func, String>,
    pre: HelperPrebuilt,
    bases: HelperBases,
    viz: bool,
) -> Result<translate::Helpers, String> {
    // The function-index -> helper-name table, so the lowering view can name
    // the calls an op emits instead of printing an index.
    let mut resolve = |m: &mut Module, n: &str| -> Result<Func, String> {
        let f = resolve(m, n)?;
        if viz {
            crate::diag_line!(
                "night: viz helper {} {n}",
                waffle::entity::EntityRef::index(f)
            );
        }
        Ok(f)
    };
    Ok(translate::Helpers {
        mem: pre.mem,
        ta_get_poly: pre.ta_get_poly,
        ta_set_poly: pre.ta_set_poly,
        ic_get_poly: pre.ic_get_poly,
        ic_set_cold: pre.ic_set_cold,
        elem_mega_get: pre.elem_mega_get,
        elem_mega_set_probe: pre.elem_mega_set_probe,
        call_classify: pre.call_classify,
        elem_append_check: pre.elem_append_check,
        night_abi_sig: pre.night_abi_sig,
        indirect_table: pre.indirect_table,
        direct_call_stub: pre.direct_call_stub,
        night_abi_sig2: pre.night_abi_sig2,
        direct_call_stub2: pre.direct_call_stub2,
        census: resolve(m, "night_runtime_census").ok(),
        callee_night_target: resolve(m, "night_runtime_callee_night_target")?,
        add: resolve(m, "night_runtime_add")?,
        concat: resolve(m, "night_runtime_concat")?,
        call: resolve(m, "night_runtime_call")?,
        call_iter: resolve(m, "night_runtime_call_iter")?,
        native_dispatch: resolve(m, "night_runtime_native_dispatch")?,
        apply_fwd: resolve(m, "night_runtime_apply_fwd")?,
        construct: resolve(m, "night_runtime_construct")?,
        get_property: resolve(m, "night_runtime_get_property")?,
        set_property: resolve(m, "night_runtime_set_property")?,
        get_prop_ic_miss: resolve(m, "night_runtime_get_prop_ic_miss")?,
        set_prop_ic_miss: resolve(m, "night_runtime_set_prop_ic_miss")?,
        get_gname: resolve(m, "night_runtime_get_gname")?,
        get_element: resolve(m, "night_runtime_get_element")?,
        set_element: resolve(m, "night_runtime_set_element")?,
        binop: resolve(m, "night_runtime_binop")?,
        compare: resolve(m, "night_runtime_compare")?,
        string: resolve(m, "night_runtime_string")?,
        get_intrinsic: resolve(m, "night_runtime_get_intrinsic")?,
        get_intrinsic_cell: resolve(m, "night_runtime_get_intrinsic_cell")?,
        strlit_verify: resolve(m, "night_runtime_strlit_verify")?,
        str_chars_eq: resolve(m, "night_runtime_str_chars_eq")?,
        tonumeric: resolve(m, "night_runtime_tonumeric")?,
        pos: resolve(m, "night_runtime_pos")?,
        neg: resolve(m, "night_runtime_neg")?,
        instanceof_: resolve(m, "night_runtime_instanceof")?,
        del_prop: resolve(m, "night_runtime_del_prop")?,
        arguments_: resolve(m, "night_runtime_arguments")?,
        arguments_env: resolve(m, "night_runtime_arguments_env")?,
        box_nonstrict_this: resolve(m, "night_runtime_box_nonstrict_this")?,
        get_mapped_arg: resolve(m, "night_runtime_get_mapped_arg")?,
        set_mapped_arg: resolve(m, "night_runtime_set_mapped_arg")?,
        validate_this_layout: resolve(m, "night_runtime_validate_this_layout")?,
        in_: resolve(m, "night_runtime_in")?,
        has_own: resolve(m, "night_runtime_has_own")?,
        to_property_key: resolve(m, "night_runtime_to_property_key")?,
        mutate_proto: resolve(m, "night_runtime_mutate_proto")?,
        init_home_object: resolve(m, "night_runtime_init_home_object")?,
        super_base: resolve(m, "night_runtime_super_base")?,
        super_fun: resolve(m, "night_runtime_super_fun")?,
        get_prop_super: resolve(m, "night_runtime_get_prop_super")?,
        get_elem_super: resolve(m, "night_runtime_get_elem_super")?,
        set_prop_super: resolve(m, "night_runtime_set_prop_super")?,
        set_elem_super: resolve(m, "night_runtime_set_elem_super")?,
        tostring: resolve(m, "night_runtime_tostring")?,
        pow: resolve(m, "night_runtime_pow")?,
        check_obj_coercible: resolve(m, "night_runtime_check_obj_coercible")?,
        check_class_heritage: resolve(m, "night_runtime_check_class_heritage")?,
        create_generator: resolve(m, "night_runtime_create_generator")?,
        gen_suspend: resolve(m, "night_runtime_gen_suspend")?,
        gen_restore: resolve(m, "night_runtime_gen_restore")?,
        gen_check_resume: resolve(m, "night_runtime_gen_check_resume")?,
        gen_closing: resolve(m, "night_runtime_gen_closing")?,
        gen_final: resolve(m, "night_runtime_gen_final")?,
        async_await: resolve(m, "night_runtime_async_await")?,
        async_resolve: resolve(m, "night_runtime_async_resolve")?,
        async_reject: resolve(m, "night_runtime_async_reject")?,
        can_skip_await: resolve(m, "night_runtime_can_skip_await")?,
        maybe_extract_await: resolve(m, "night_runtime_maybe_extract_await")?,
        check_is_obj: resolve(m, "night_runtime_check_is_obj")?,
        check_this: resolve(m, "night_runtime_check_this")?,
        check_lexical: resolve(m, "night_runtime_check_lexical")?,
        throw_set_const: resolve(m, "night_runtime_throw_set_const")?,
        push_lexical_env: resolve(m, "night_runtime_push_lexical_env")?,
        push_class_body_env: resolve(m, "night_runtime_push_class_body_env")?,
        freshen_lexical_env: resolve(m, "night_runtime_freshen_lexical_env")?,
        recreate_lexical_env: resolve(m, "night_runtime_recreate_lexical_env")?,
        init_glexical: resolve(m, "night_runtime_init_glexical")?,
        get_name: resolve(m, "night_runtime_get_name")?,
        bind_name: resolve(m, "night_runtime_bind_name")?,
        get_bound_name: resolve(m, "night_runtime_get_bound_name")?,
        bind_unqualified_name: resolve(m, "night_runtime_bind_unqualified_name")?,
        bind_var: resolve(m, "night_runtime_bind_var")?,
        del_name: resolve(m, "night_runtime_del_name")?,
        push_var_env: resolve(m, "night_runtime_push_var_env")?,
        enter_with: resolve(m, "night_runtime_enter_with")?,
        throw_msg: resolve(m, "night_runtime_throw_msg")?,
        builtin_object: resolve(m, "night_runtime_builtin_object")?,
        builtin_object_cell: resolve(m, "night_runtime_builtin_object_cell")?,
        del_elem: resolve(m, "night_runtime_del_elem")?,
        global_this: resolve(m, "night_runtime_global_this")?,
        regexp: resolve(m, "night_runtime_regexp")?,
        init_prop_getset: resolve(m, "night_runtime_init_prop_getset")?,
        to_boolean: resolve(m, "night_runtime_to_boolean")?,
        typeof_: resolve(m, "night_runtime_typeof")?,
        typeof_eq: resolve(m, "night_runtime_typeof_eq")?,
        constant_strict_eq: resolve(m, "night_runtime_constant_strict_eq")?,
        bind_unqualified_gname: resolve(m, "night_runtime_bind_unqualified_gname")?,
        set_name: resolve(m, "night_runtime_set_name")?,
        new_object: resolve(m, "night_runtime_new_object")?,
        new_array: resolve(m, "night_runtime_new_array")?,
        init_prop: resolve(m, "night_runtime_init_prop")?,
        init_elem: resolve(m, "night_runtime_init_elem")?,
        init_elem_getset: resolve(m, "night_runtime_init_elem_getset")?,
        check_private_field: resolve(m, "night_runtime_check_private_field")?,
        new_private_name: resolve(m, "night_runtime_new_private_name")?,
        env_setup: resolve(m, "night_runtime_env_setup")?,
        get_aliased: resolve(m, "night_runtime_get_aliased")?,
        set_aliased: resolve(m, "night_runtime_set_aliased")?,
        lambda: resolve(m, "night_runtime_lambda")?,
        exception: resolve(m, "night_runtime_exception")?,
        throw: resolve(m, "night_runtime_throw")?,
        throw_with_stack: resolve(m, "night_runtime_throw_with_stack")?,
        get_exception_for_finally: resolve(m, "night_runtime_get_exception_for_finally")?,
        global_decl_instantiation: resolve(m, "night_runtime_global_decl_instantiation")?,
        iter_: resolve(m, "night_runtime_iter")?,
        more_iter: resolve(m, "night_runtime_more_iter")?,
        end_iter: resolve(m, "night_runtime_end_iter")?,
        close_iter_for_exception: resolve(m, "night_runtime_close_iter_for_exception")?,
        symbol: resolve(m, "night_runtime_symbol")?,
        optimize_get_iterator: resolve(m, "night_runtime_optimize_get_iterator")?,
        close_iter: resolve(m, "night_runtime_close_iter")?,
        to_async_iter: resolve(m, "night_runtime_to_async_iter")?,
        spread_call: resolve(m, "night_runtime_spread_call")?,
        optimize_spread_call: resolve(m, "night_runtime_optimize_spread_call")?,
        object: resolve(m, "night_runtime_object")?,
        post_write_barrier: resolve(m, "night_runtime_post_write_barrier")?,
        post_write_barrier_elem: resolve(m, "night_runtime_post_write_barrier_elem")?,
        pre_write_barrier: resolve(m, "night_runtime_pre_write_barrier")?,
        resolve_global_slot: resolve(m, "night_runtime_resolve_global_slot")?,
        resolve_global_slot_guarded: resolve(m, "night_runtime_resolve_global_slot_guarded")?,
        set_global: resolve(m, "night_runtime_set_global")?,
        binding_written: resolve(m, "night_runtime_binding_written")?,
        binding_value: resolve(m, "night_runtime_binding_value")?,
        global_slots_base: bases.global_slots_base,
        prop_ic_base: bases.prop_ic_base,
        mega_set_base: bases.mega_set_base,
        prop_ic_gen_base: bases.prop_ic_gen_base,
        this_cells_base: bases.this_cells_base,
        this_slots_base: bases.this_slots_base,
        mega_get_base: bases.mega_get_base,
        night_stack_limit_base: bases.night_stack_limit_base,
        fn_class_slot: bases.fn_class_slot,
        static_strings_slot: bases.static_strings_slot,
        atom_table_slot: bases.atom_table_slot,
        nursery_pos_slot: bases.nursery_pos_slot,
        nursery_end_slot: bases.nursery_end_slot,
        str_ccat_cell: bases.str_ccat_cell,
        str_cat_cell: bases.str_cat_cell,
        str_fcc_cell: bases.str_fcc_cell,
        str_fuse_addr_slot: bases.str_fuse_addr_slot,
        // The TA-clasp table's 4-byte alignment pad (9*4 = 36, padded to 40)
        // holds the HasSeenObjectEmulateUndefinedFuse word address; NightRuntime
        // startup mirrors this offset.
        dda_fuse_addr_slot: bases.ta_class_base + shape::TA_CLASS_DDA_FUSE_OFF,
        // The args-metadata block's tail pad (+12) holds the night-owned
        // dynamic-code fuse word; NightRuntime startup mirrors this offset.
        // (This pad is the free word here, so using it costs no ABI change.)
        dyncode_fuse_word: bases.args_class_base + shape::ARGS_DYN_CODE_FUSE_OFF,
        array_class_slot: bases.array_class_slot,
        args_class_base: bases.args_class_base,
        strlit_slot: bases.strlit_slot,
        builtin_cells_base: bases.builtin_cells_base,
        math_natives_base: bases.math_natives_base,
        append_cache_base: bases.append_cache_base,
        accessor_cache_base: bases.accessor_cache_base,
        ta_class_base: bases.ta_class_base,
        math_unary: resolve(m, "night_runtime_math_unary")?,
        math_pow: resolve(m, "night_runtime_math_pow")?,
        fmod: resolve(m, "night_runtime_fmod")?,
        global_vals_base: bases.global_vals_base,
        create_this: resolve(m, "night_runtime_create_this")?,
        rest: resolve(m, "night_runtime_rest")?,
        implicit_this: resolve(m, "night_runtime_implicit_this")?,
        check_this_reinit: resolve(m, "night_runtime_check_this_reinit")?,
        check_return: resolve(m, "night_runtime_check_return")?,
        obj_with_proto: resolve(m, "night_runtime_obj_with_proto")?,
        fun_with_proto: resolve(m, "night_runtime_fun_with_proto")?,
        set_fun_name: resolve(m, "night_runtime_set_fun_name")?,
        no_extra_indexed: resolve(m, "night_runtime_no_extra_indexed")?,
        gen_is_closing: resolve(m, "night_runtime_gen_is_closing")?,
    })
}

/// Analysis-prepass outputs plus the derived pre-translation address blocks:
/// the likely-facts inputs and tx maps the translator consumes, and every
/// baked base address (`HelperBases` derives from these).
pub struct EnvLayout {
    pub syn_gname_names: Vec<NameId>,
    pub syn_gnames: HashMap<NameId, u32>,
    /// The bindings whose name is an own atom-keyed DATA property of the
    /// snapshot's global object (the heap oracle records no other kind):
    /// the population the per-binding value facts (`Ctx::gcells`) are
    /// minted for. A global lexical, an accessor or an undeclared name is
    /// never in it, so its reads keep the generic helper's Opt keep arm.
    pub gcell_bids: HashSet<u32>,
    pub likely_fns: HashMap<NameId, ScriptId>,
    /// The analysis output, carried whole: every table the translator reads
    /// unchanged lives here rather than as a renamed copy below.
    pub facts: LikelyFacts,
    /// Field-name rows per layout key: the view most layout consumers want.
    pub likely_class_layouts: HashMap<LayoutKey, Vec<NameId>>,
    /// `facts.elem_sites` and `facts.field_sites` merged (one op per pc);
    /// consumed identically by the loop-version planner and value guards.
    pub likely_elems: HashMap<Site, Claim>,
    pub fused_list: Vec<(NameId, u64)>,
    pub stamp_ctors_tx: HashMap<ScriptId, translate::StampCtorIn>,
    /// Object-literal stamp sites (site -> layout id), fixed-slot rows only.
    pub lit_stamps_tx: HashMap<Site, u32>,
    /// Per atom: prefix-closed (layout k+1, predicted byte offset) pairs
    /// for the unknown-receiver add arms' runtime key check.
    pub layout_addpred_tx: HashMap<NameId, Vec<translate::AddPred>>,
    pub ctor_nslots_tx: HashMap<ScriptId, u32>,
    pub deleg_restamps_tx: HashMap<ScriptId, translate::StampCtorIn>,
    pub arg_restamps_tx: HashMap<ScriptId, (u32, translate::StampCtorIn)>,
    pub local_restamps_tx: HashMap<Site, (u32, translate::StampCtorIn)>,
    pub construct_sites_tx: HashMap<Site, translate::StampCtorIn>,
    pub this_layouts_tx: HashMap<ScriptId, translate::ThisLayoutIn>,
    pub prop_sites_tx: HashMap<Site, translate::PropSiteIn>,
    /// Stamped class idx (`layout_id + 1`) -> field name -> value mask.
    pub layout_field_masks_tx: HashMap<StampKey, HashMap<NameId, Claim>>,
    /// Same keying, the range claims (absent name = no claim).
    pub layout_field_ranges_tx: HashMap<StampKey, HashMap<NameId, ValueRange>>,
    /// Array alloc site -> the stamp word to write at allocation.
    pub array_stamp_tx: HashMap<Site, u32>,
    /// Element site -> (stamp key, mask, lo, hi).
    pub array_elem_tx: HashMap<Site, translate::ArrayElemIn>,
    /// Intersection of every array claim: what an unclassified element
    /// store must prove. None = nothing claims, so stores owe nothing.
    pub array_any_claim: Option<ValueRange>,
    pub fused_gnames_tx: HashMap<NameId, translate::FusedGname>,
    pub ctor_layout_id: HashMap<LayoutKey, u32>,
    pub layout_ctors: Vec<LayoutKey>,
    pub layout_mode: u32,
    pub num_global_bindings: usize,
    pub global_slots_base: u32,
    pub global_vals_base: u32,
    pub prop_ic_gen_base: u32,
    pub night_stack_limit_base: u32,
    pub fn_class_slot: u32,
    pub static_strings_slot: u32,
    pub atom_table_slot: u32,
    pub nursery_pos_slot: u32,
    pub nursery_end_slot: u32,
    pub str_ccat_cell: u32,
    pub str_cat_cell: u32,
    pub str_fcc_cell: u32,
    pub str_fuse_addr_slot: u32,
    pub array_class_slot: u32,
    pub builtin_cells_base: u32,
    pub ta_class_base: u32,
    pub args_class_base: u32,
    pub strlit_slot: u32,
    pub this_cells_base: u32,
    pub this_slots_base: u32,
    pub gname_fuse_base: u32,
    pub mega_get_base: u32,
    pub mega_set_base: u32,
    pub math_natives_base: u32,
    pub append_cache_base: u32,
    pub accessor_cache_base: u32,
    pub prop_ic_base: u32,
}

impl EnvLayout {
    pub fn helper_bases(&self) -> HelperBases {
        HelperBases {
            global_slots_base: self.global_slots_base,
            prop_ic_base: self.prop_ic_base,
            mega_set_base: self.mega_set_base,
            prop_ic_gen_base: self.prop_ic_gen_base,
            this_cells_base: self.this_cells_base,
            this_slots_base: self.this_slots_base,
            mega_get_base: self.mega_get_base,
            night_stack_limit_base: self.night_stack_limit_base,
            fn_class_slot: self.fn_class_slot,
            static_strings_slot: self.static_strings_slot,
            atom_table_slot: self.atom_table_slot,
            nursery_pos_slot: self.nursery_pos_slot,
            nursery_end_slot: self.nursery_end_slot,
            str_ccat_cell: self.str_ccat_cell,
            str_cat_cell: self.str_cat_cell,
            str_fcc_cell: self.str_fcc_cell,
            str_fuse_addr_slot: self.str_fuse_addr_slot,
            array_class_slot: self.array_class_slot,
            args_class_base: self.args_class_base,
            strlit_slot: self.strlit_slot,
            builtin_cells_base: self.builtin_cells_base,
            math_natives_base: self.math_natives_base,
            append_cache_base: self.append_cache_base,
            accessor_cache_base: self.accessor_cache_base,
            ta_class_base: self.ta_class_base,
            global_vals_base: self.global_vals_base,
        }
    }
}

/// Run the analysis prepass and compute the derived address blocks starting
/// at `base` (production: the runtime module's initial memory end).
pub fn layout_env(
    source: &Source,
    root_id: SourceObjectId,
    base: u32,
    opts: &Options,
) -> Result<EnvLayout, String> {
    // Reserve the `gGlobalSlots` region (one 8-byte `[entry, shape]` row
    // per resolvable global binding; the guarded path checks `shape`) at the
    // Current memory end, before the blob/patch/atom/binding-name data segments
    // are appended below. It carries no data segment, so it stays
    // zero-initialized == all-unresolved; the reactor lazily fills it on first
    // access. The translator bakes `global_slots_base + 8*binding_id` as the
    // inline-read address, so the base must be known before translation. The
    // binding table is the syntactic gname set (pre-scanned here, so the count
    // -- and hence the property-IC base below -- is known before translation).
    // The compilation's one string table. Seeded by the syntactic scans
    // here, filled by the analysis, and finally owned by the `AtomTable`:
    // every name crosses the analysis/translator boundary as a `NameId`
    // rather than as a copy of its code units.
    let mut names = Names::default();
    let syn_gname_names: Vec<NameId> = collect_syntactic_gnames(source, &mut names);
    let syn_gnames: HashMap<NameId, u32> = syn_gname_names
        .iter()
        .enumerate()
        .map(|(i, &n)| (n, u32::try_from(i).unwrap()))
        .collect();
    let mut gcell_bids: HashSet<u32> = HashSet::default();
    if let Some(g) = source.global_object {
        if let SourceObject::Object(ObjectData { properties, .. }) = source.object(g) {
            for (k, _) in properties {
                if k.is_other() {
                    continue;
                }
                if let SourceObject::String(s) = source.object(*k) {
                    let id = names.intern(s);
                    if let Some(&bid) = syn_gnames.get(&id) {
                        gcell_bids.insert(bid);
                    }
                }
            }
        }
    }
    let likely_fns = collect_likely_gname_fns(source, root_id, &mut names);
    // Fused constant globals (predicted literal + runtime-armed fuse). Read
    // off the root script's bytecode, so it needs nothing from the analysis
    // -- and it interns into the table before that is handed over.
    let fused_list: Vec<(NameId, u64)> = collect_fused_gnames(source, root_id, &mut names);
    if opts.diagnostics.stats {
        crate::diag_line!("night: {} fused constant global(s)", fused_list.len());
    }
    if opts.diagnostics.bbv {
        for &(n, bits) in &fused_list {
            crate::diag_line!(
                "night: fused-gname {} = {:#x}",
                String::from_utf16_lossy(names.get(n)),
                bits
            );
        }
    }
    if opts.diagnostics.stats {
        crate::diag_line!(
            "night: {} likely-callee global function(s)",
            likely_fns.len()
        );
    }
    // The likely-facts analysis (see likelier/): per-site predictions the
    // guarded fast-path arms consume. Passed onward whole -- the translator
    // reads `LikelyFacts` directly rather than through a re-named copy of
    // every table.
    let facts = crate::likelier::analyze(source, &likely_fns, opts, names);
    if let Some(path) = &opts.diagnostics.facts {
        crate::likelier::dump::dump_facts(&facts, path);
    }
    if opts.diagnostics.stats {
        crate::diag_line!(
            "night: likely analysis: {} classes, {} constraints, {} call sites, \
                 {} this-layouts, {} class layouts, {} prop sites, {} ctor stamps, \
                 {} ta sites",
            facts.n_classes,
            facts.n_cons,
            facts.call_sites.len(),
            facts.this_layouts.len(),
            facts.classes.len(),
            facts.prop_sites.len(),
            facts.ctor_stamps.len(),
            facts.ta_elem_sites.len()
        );
    }
    // The one table the translator wants that the analysis does not emit
    // directly: elem and field sites merged. Both are keyed by pc (one op
    // per pc) and the loop-version planner and the value guards consume
    // them identically.
    let likely_elems: HashMap<Site, Claim> = {
        let mut m = facts.elem_sites.clone();
        m.extend(facts.field_sites.iter().map(|(&k, &v)| (k, v)));
        m
    };
    // Field-name rows: the view most layout consumers want.
    let likely_class_layouts: HashMap<LayoutKey, Vec<NameId>> = facts
        .classes
        .iter()
        .map(|(&k, c)| (k, c.fields.iter().map(|f| f.name).collect()))
        .collect();
    // Fullword/dims mask union: the typed tier upgrades the wmask-starved
    // positions.
    let fullword_masks = true;
    let num_global_bindings = syn_gname_names.len();
    let global_slots_base = base;
    // Per binding: an 8-byte row [entry, shape] plus (after all rows) a
    // 16-byte value-fuse cell [bits u64][fuseWord u32][pad] (armed by
    // the resolve leaf when the value is tenured, blown by the compiled
    // global write paths on a value change).
    let global_slots_size = num_global_bindings * 24;
    let global_vals_base = u32::try_from(base as usize + num_global_bindings * 8)
        .map_err(|_| "global vals base exceeds 32-bit memory".to_string())?;

    // Reserve the inline property-IC region right after `gGlobalSlots`. Its
    // base only depends on `gGlobalSlots` (known here), so the translator can
    // bake `prop_ic_base + cacheIdx*stride + way*20` as inline-load addresses;
    // its size (`prop_cache_count * stride`) is known only after translation, so
    // the data segments below shift past it then (like the blob offsets). One
    // leading `u32` is the major-GC generation counter (`prop_ic_gen_base`); the
    // per-site ways follow. The region carries no data segment -> zero-init ==
    // every way empty, generation 0.
    let prop_ic_gen_base = global_slots_base + global_slots_size as u32;
    // One more u32 right after the generation: the AOT stack limit (linear
    // address one past the region), written once by `night_runtime_run_main`.
    // The specialized-call
    // specialized-call guard reads it so deep direct-dispatch chains fall back
    // to `night_runtime_call` (whose `EnterNight` bounds-checks and can hand the frame
    // to the interpreter) instead of running off the region.
    let night_stack_limit_base = prop_ic_gen_base + shape::HOST_STACK_LIMIT_OFF;
    // Startup-written host-constant slots (filled by `night_runtime_run_main`, which
    // can take the addresses the AOT'd module cannot embed):
    //   +8:  &js::FunctionClass          (inline callee classify)
    //   +12: &js::ExtendedFunctionClass  (inline callee classify)
    //   +16: StaticStrings unit-string table base (inline string s[i])
    //   +20: the literal-atom table base (JSAtom* per atom id; JSOp::String)
    //   +24: address of the nursery's position_ word (inline alloc; 0 =
    //        nursery object allocation disabled)
    //   +28: address of the nursery's currentEnd_ word
    //   +32: boxed bits (u64) of the original String.prototype.charCodeAt
    //        (inline string-method call guard; 0 = unarmed; GC re-arms)
    //   +40: boxed bits (u64) of the original String.prototype.charAt
    //   +48: boxed bits (u64) of the original String.fromCharCode
    //   +56: address of OptimizeStringCharOpsFuse's guard word (0 == fuse
    //        intact; the reactor points it at a permanently-popped word when
    //        the fuse is unavailable)
    //   +60: &js::ArrayObject::class_ (startup-written; the inline
    //        array-length arm's clasp compare)
    let fn_class_slot = prop_ic_gen_base + shape::HOST_FN_CLASS_OFF;
    let static_strings_slot = prop_ic_gen_base + shape::HOST_STATIC_STRINGS_OFF;
    let atom_table_slot = prop_ic_gen_base + shape::HOST_ATOM_TABLE_OFF;
    let nursery_pos_slot = prop_ic_gen_base + shape::HOST_NURSERY_POS_OFF;
    let nursery_end_slot = prop_ic_gen_base + shape::HOST_NURSERY_END_OFF;
    let str_ccat_cell = prop_ic_gen_base + shape::HOST_STR_CHAR_CODE_AT_OFF;
    let str_cat_cell = prop_ic_gen_base + shape::HOST_STR_CHAR_AT_OFF;
    let str_fcc_cell = prop_ic_gen_base + shape::HOST_STR_FROM_CHAR_CODE_OFF;
    let str_fuse_addr_slot = prop_ic_gen_base + shape::HOST_STR_CHAR_OPS_FUSE_OFF;
    // +60: &js::ArrayObject::class_ (startup-written; the inline
    // array-length arm's clasp compare).
    let array_class_slot = prop_ic_gen_base + shape::HOST_ARRAY_CLASS_OFF;
    // +64..+248: builtin callee-identity cells (u64 boxed bits of the
    // pristine builtin, 0 = unarmed; armed at startup, re-armed after every
    // major GC from PersistentRooted). Index order is translate::BC_*.
    let builtin_cells_base = prop_ic_gen_base + shape::HOST_BUILTIN_CELLS_OFF;
    // Likely `this`-layout guard cells: one `[shape u32, gen u32]` per
    // layout script, zero-init (0 = unvalidated; the C++ validator fills a
    // real shape word or the invalid sentinel 1). Sits before the prop-IC
    // ways so its base is known pre-translation.
    let mut layout_ctors: Vec<LayoutKey> = facts.classes.keys().copied().collect();
    layout_ctors.sort_unstable();
    let ctor_layout_id: HashMap<LayoutKey, u32> = layout_ctors
        .iter()
        .enumerate()
        .map(|(i, &c)| (c, u32::try_from(i).unwrap()))
        .collect();
    // TA-clasp table: 9 startup-written fixed-length typed-array class
    // pointers (element kind 1..=9 at index kind-1), the inline typed-array
    // read arm's clasp identity guard. 9*4=36 bytes padded to 40 for 8-byte
    // alignment of the following this-cells; the pad word (+36) holds the
    // HasSeenObjectEmulateUndefinedFuse word address (Helpers::
    // dda_fuse_addr_slot). Mirrored in NightRuntime startup.
    let ta_class_base = builtin_cells_base + shape::BUILTIN_CELL_BYTES * shape::BUILTIN_CELL_COUNT;
    // Startup-written arguments-object inline metadata right after the TA-clasp
    // table (16 bytes, 8-aligned): [mapped class @0, unmapped class @4,
    // ArgumentsData::offsetOfArgs() @8, pad @12]. The clasp pair guards the
    // inline `arguments.length` / `arguments[i]` arms; the offset locates the
    // element Value array off `data()`. Mirrored in NightRuntime startup.
    let args_class_base = ta_class_base + shape::TA_CLASS_BLOCK_BYTES;
    // Inline string-literal block (32 bytes; see Helpers::strlit_slot):
    // emptyString slot + the thin/fat replay triples. Startup-armed /
    // helper-filled by the reactor, which mirrors this offset
    // (prop_ic_gen_base + 64 + 8*BC_COUNT + 40 + 16).
    let strlit_slot = args_class_base + shape::ARGS_CLASS_BLOCK_BYTES;
    let this_cells_base = strlit_slot + translate::STRLIT_BLOCK_BYTES;
    let cell_of = |ctor: LayoutKey| this_cells_base + 8 * ctor_layout_id[&ctor];
    // Observed-slot layout table: one row per layout directly after the
    // guard cells -- u32 published-count (high bit = NONPOS flag) + 16 x
    // u16 observed slots (stride 40). Zero-init = unpublished; the
    // validator fills a row once and later revalidations must match it
    // (see NightRuntime). Layout validation mode (the blob flags word keeps the
    // validator and the compiled arms in lockstep): 2 = Option-C dual stamp
    // (positional match -> plain stamp + immediates, order mismatch ->
    // observed row + NONPOS stamp + table sub-arm).
    let layout_mode: u32 = 2;
    let this_slots_base = this_cells_base + 8 * u32::try_from(layout_ctors.len()).unwrap();
    let masks_of = |ctor: LayoutKey| -> Vec<Claim> {
        facts.classes[&ctor]
            .fields
            .iter()
            .map(|f| {
                Claim::of_prims(if fullword_masks {
                    f.typed_prims
                } else {
                    f.prims
                })
            })
            .collect()
    };
    let ranges_of = |ctor: LayoutKey| -> Vec<Option<ValueRange>> {
        facts.classes[&ctor]
            .fields
            .iter()
            .map(|f| f.range)
            .collect()
    };
    // The range a fact spanning layout keys `lo..=hi` may claim at slot
    // `i`: the hull of the members' claims, and only if every member
    // claims (a member that does not is a member whose stores were never
    // range-checked). Exact facts (lo == hi) fall out as the single row.
    let span_range = |lo: LayoutKey, hi: LayoutKey, i: usize| -> Option<ValueRange> {
        (lo.get()..=hi.get())
            .filter(|k| facts.classes.contains_key(&LayoutKey::new(*k)))
            .try_fold(None::<ValueRange>, |acc, k| {
                let r = *ranges_of(LayoutKey::new(k)).get(i)?.as_ref()?;
                Some(Some(acc.map_or(r, |a| a.hull(r))))
            })
            .flatten()
    };
    // Viz layout panel: one line per layout key, ids in the +1-biased
    // stamped space (what cls facts show). Every column is something the
    // codegen consumes -- the panel exists to show what the backend has, so
    // an analysis detail with no emission consumer does not belong in it.
    if opts.diagnostics.viz {
        for &key in &layout_ctors {
            let masks = masks_of(LayoutKey::new(key.get()));
            let franges = ranges_of(LayoutKey::new(key.get()));
            let fields: Vec<String> = likely_class_layouts[&key]
                .iter()
                .enumerate()
                .map(|(i, f)| {
                    format!(
                        "{}=slot{}:{}:{}",
                        bbv::viz_sanitize(&String::from_utf16_lossy(facts.names.get(*f))),
                        i,
                        bbv::viz_claim_str(masks.get(i).copied().unwrap_or(Claim::NONE)),
                        match franges.get(i).copied().flatten() {
                            Some(r) => format!("{}..{}", r.lo, r.hi),
                            None => "-".to_string(),
                        },
                    )
                })
                .collect();
            crate::diag_line!(
                "night: viz layout id {} fields [{}]",
                LayoutKey::new(ctor_layout_id[&key]).stamp(),
                fields.join(" ")
            );
        }
    }
    // Ctor-epilogue class-idx stamps: one per layout ctor; the stamped u16
    // index is `layout_id + 1` (0 = no likely class), so the id space must
    // fit a u16.
    // Bit 15 of the stamped idx half is the NONPOS flag, so the
    // id space is one bit narrower than the u16.
    assert!(
        layout_ctors.len() < LayoutKey::LIMIT as usize,
        "layout id space exceeds 15 bits"
    );
    // The early-key field is the narrower ceiling: a key past it is
    // stamped keyless (sized, SLOTS-unseeded), a perf effect only. Logged
    // so a corpus run confirms the headroom the RANGES bit cost it.
    if layout_ctors.len() >= EARLY_KEY_MAX as usize {
        log::warn!(
            "night: {} layout keys exceeds the {} early-key ceiling -- \
             the overflow stamps keyless",
            layout_ctors.len(),
            EARLY_KEY_MAX
        );
    }
    // One stamp descriptor per layout key; ctor-return sites and literal
    // sites both resolve through it (merged sibling ctors share a key).
    // Byte-offset add-check bound per layout key: the longest prefix over
    // every clump member extending this layout (self included). Also
    // serialized into the layout blob so the runtime can fill the static
    // bound table (the retired guard cells' region) at install.
    let ext_bound_of = |key: LayoutKey| -> u32 {
        let fields = &likely_class_layouts[&key];
        let max_len = layout_ctors
            .iter()
            .filter(|&&e| {
                let ef = &likely_class_layouts[&e];
                ef.len() >= fields.len() && ef[..fields.len()] == fields[..]
            })
            .map(|&e| facts.classes[&e].fields.len())
            .max()
            .unwrap_or(fields.len());
        translate::FIXED_SLOTS_BASE + 8 * u32::try_from(max_len).unwrap()
    };
    let stamp_in_of_key: HashMap<LayoutKey, translate::StampCtorIn> = layout_ctors
        .iter()
        .map(|&key| {
            let fields = &likely_class_layouts[&key];
            let prefix_keys: Vec<u32> = layout_ctors
                .iter()
                .filter(|&&p| {
                    p != key && {
                        let pf = &likely_class_layouts[&p];
                        !pf.is_empty() && pf.len() < fields.len() && fields[..pf.len()] == pf[..]
                    }
                })
                .map(|&p| ctor_layout_id[&p])
                .collect();
            (
                key,
                translate::StampCtorIn {
                    cell_addr: cell_of(LayoutKey::new(key.get())),
                    layout_id: ctor_layout_id[&key],
                    fields: fields.clone(),
                    masks: masks_of(LayoutKey::new(key.get())),
                    ranges: ranges_of(LayoutKey::new(key.get())),
                    prefix_keys,
                    ext_bound: ext_bound_of(LayoutKey::new(key.get())),
                },
            )
        })
        .collect();
    let stamp_ctors_tx: HashMap<ScriptId, translate::StampCtorIn> = facts
        .ctor_stamps
        .iter()
        .filter_map(|(&ctor_sid, key)| stamp_in_of_key.get(key).cloned().map(|si| (ctor_sid, si)))
        .collect();
    // Object-literal stamp sites: site -> stamped layout id, gated to rows
    // whose every field sits in a fixed slot (the offset form the claims
    // and the runtime layout tables assume).
    let lit_stamps_tx: HashMap<Site, u32> = facts
        .lit_stamps
        .iter()
        .filter(|(_, key)| likely_class_layouts[key].len() <= 16)
        .map(|(&site, key)| (site, ctor_layout_id[key]))
        .collect();
    // Per atom: every (layout k+1, predicted byte offset) pair across the
    // corpus, prefix-closed (a receiver keyed/stamped with a prefix layout
    // is adding toward the extension, so the prefix's id predicts the
    // atom at the extension's position too). The unknown-receiver add
    // arms compare the receiver's runtime key against these instead of
    // conservatively clearing SLOTS on every in-prefix add.
    let layout_addpred_tx: HashMap<NameId, Vec<translate::AddPred>> = {
        let mut m: HashMap<NameId, Vec<translate::AddPred>> = HashMap::default();
        for &key in &layout_ctors {
            let fields = &likely_class_layouts[&key];
            let lid = ctor_layout_id[&key];
            for (p, &name) in fields.iter().enumerate() {
                let off = translate::FIXED_SLOTS_BASE + 8 * u32::try_from(p).unwrap();
                let e = m.entry(name).or_default();
                e.push(translate::AddPred {
                    key: LayoutKey::new(lid).stamp(),
                    offset: off,
                });
                for &pk in &stamp_in_of_key[&key].prefix_keys {
                    let plen = likely_class_layouts[&layout_ctors[pk as usize]].len();
                    if plen <= p {
                        e.push(translate::AddPred {
                            key: LayoutKey::new(pk).stamp(),
                            offset: off,
                        });
                    }
                }
            }
        }
        for v in m.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        m
    };
    // Per-layout field value masks, keyed by the stamped class idx
    // (`layout_id + 1`, what a `cls` fact carries). The per-site
    // `prop_sites` rows only exist where the analysis predicted a receiver
    // for that pc; this table lets any receiver carrying a proven class
    // fact answer "does field N of this layout hold a number claim?", which
    // is what the store choke needs to know.
    let layout_field_masks_tx: HashMap<StampKey, HashMap<NameId, Claim>> = layout_ctors
        .iter()
        .map(|&key| {
            let masks = masks_of(LayoutKey::new(key.get()));
            let fields = &likely_class_layouts[&key];
            (
                LayoutKey::new(ctor_layout_id[&key]).stamp(),
                fields
                    .iter()
                    .enumerate()
                    .map(|(i, &n)| (n, masks.get(i).copied().unwrap_or(Claim::NONE)))
                    .collect(),
            )
        })
        .collect();
    // The range parallel, same keying: "does field N of this layout carry
    // a range claim, and which?" -- what the store choke needs to decide
    // between proving a store, checking it, and dropping the claim.
    // Absent name = no claim, so only claiming rows are stored.
    let layout_field_ranges_tx: HashMap<StampKey, HashMap<NameId, ValueRange>> = layout_ctors
        .iter()
        .map(|&key| {
            let ranges = ranges_of(LayoutKey::new(key.get()));
            let fields = &likely_class_layouts[&key];
            (
                LayoutKey::new(ctor_layout_id[&key]).stamp(),
                fields
                    .iter()
                    .enumerate()
                    .filter_map(|(i, &n)| Some((n, (*ranges.get(i)?)?)))
                    .collect(),
            )
        })
        .collect();
    // Array stamp keys (increment 2). Arrays share the object stamp word,
    // so their idx must never collide with a layout key -- `emit_class_fact_get`
    // compares the full idx half, and a collision would let a field site
    // serve a fixed slot off an array. Layout keys grow UP from 1 and are
    // asserted below 0x7FFF; array keys grow down from 0x7FFE, so the two
    // are disjoint by construction as long as they never meet.
    let array_keys: HashMap<RegionRoot, u32> = {
        let mut roots: Vec<RegionRoot> = facts.array_elem_claims.keys().copied().collect();
        roots.sort_unstable();
        assert!(
            layout_ctors.len() + roots.len() < 0x7FFE,
            "layout and array key spaces collide"
        );
        roots
            .iter()
            .enumerate()
            .map(|(i, &r)| (r, 0x7FFE - u32::try_from(i).unwrap()))
            .collect()
    };
    // Alloc site -> the word a compiled array allocation stamps. TYPES and
    // RANGES seed together and vacuously hold: the array is fresh and
    // empty, so every claim about its elements is trivially true, and the
    // element writes that follow carry the maintenance duty.
    let array_stamp_tx: HashMap<Site, u32> = facts
        .array_alloc_sites
        .iter()
        .filter_map(|(&site, root)| {
            let k = array_keys.get(root)?;
            Some((site, k | bbv::CLASS_WORD_SHALLOW | bbv::CLASS_WORD_RANGES))
        })
        .collect();
    // Element site -> (stamp key, mask, lo, hi): the read fold's target and
    // the write's obligation.
    let array_elem_tx: HashMap<Site, translate::ArrayElemIn> = facts
        .array_elem_recv
        .iter()
        .filter_map(|(&site, root)| {
            let key = StampKey::new(*array_keys.get(root)?);
            let &(mask, range) = facts.array_elem_claims.get(root)?;
            Some((site, translate::ArrayElemIn { key, mask, range }))
        })
        .collect();
    // The obligation an element store carries when its receiver did not
    // classify: it could be any claiming population, so only the
    // intersection of every claim is safe to prove against. None = no
    // population claims at all, and then no element store anywhere owes
    // anything -- which is the common case (most bundles claim nothing).
    let array_any_claim: Option<ValueRange> = facts
        .array_elem_claims
        .values()
        .fold(None, |acc: Option<ValueRange>, &(_, r)| {
            Some(acc.map_or(r, |a| ValueRange::new(a.lo.max(r.lo), a.hi.min(r.hi))))
        })
        .filter(|r| r.lo <= r.hi);
    // Viz array panel: one line per claiming population -- its stamp
    // key, the R it claims, and where it is stamped and folded.
    if opts.diagnostics.viz {
        let mut roots: Vec<&RegionRoot> = facts.array_elem_claims.keys().collect();
        roots.sort_unstable();
        for r in roots {
            let (m, range) = facts.array_elem_claims[r];
            let (lo, hi) = (range.lo, range.hi);
            let allocs: Vec<String> = {
                let mut v: Vec<String> = facts
                    .array_alloc_sites
                    .iter()
                    .filter(|(_, x)| *x == r)
                    .map(|(site, _)| site.to_string())
                    .collect();
                v.sort();
                v
            };
            let folds = facts.array_elem_recv.values().filter(|x| *x == r).count();
            crate::diag_line!(
                "night: viz arrclaim root {r} key {} mask {} lo {lo} hi {hi} \
                 allocs [{}] elemsites {folds}",
                array_keys.get(r).copied().unwrap_or(0),
                bbv::viz_prims_str(m),
                allocs.join(" ")
            );
        }
    }
    if opts.diagnostics.stats && (!array_stamp_tx.is_empty() || !array_elem_tx.is_empty()) {
        crate::diag_line!(
            "night: array stamps: {} claiming populations, {} alloc sites, {} elem sites",
            array_keys.len(),
            array_stamp_tx.len(),
            array_elem_tx.len()
        );
    }
    // Construct-site nSlots predictions. Not filtered to stamped ctors:
    // sizing is layout-independent (extra fixed slots are just room), and
    // an empty-prefix two-phase ctor -- an empty `function(){}` plus an init
    // delegate -- carries nslots with no stamp row at all. Clamped to
    // the 16-fixed-slot allocation ceiling (LAY_CAP matches, so this is
    // belt-and-suspenders).
    let ctor_nslots_tx: HashMap<ScriptId, u32> = facts
        .ctor_nslots
        .iter()
        .map(|(&sid, &n)| (sid, n.min(16)))
        .collect();
    // Two-phase construction: init-delegate scripts re-stamp the full
    // layout key at their returns (same stamp descriptor machinery over
    // the full row's key/cell).
    let deleg_restamps_tx: HashMap<ScriptId, translate::StampCtorIn> = facts
        .deleg_restamps
        .iter()
        .filter_map(|(&sid, key)| stamp_in_of_key.get(key).cloned().map(|si| (sid, si)))
        .collect();
    // Formal-receiver fill scripts: the same restamp descriptor, plus
    // which formal's slot holds the object to advance.
    let arg_restamps_tx: HashMap<ScriptId, (u32, translate::StampCtorIn)> = facts
        .arg_restamps
        .iter()
        .filter_map(|(&sid, &(formal, key))| {
            stamp_in_of_key
                .get(&key)
                .cloned()
                .map(|si| (sid, (formal, si)))
        })
        .collect();
    let local_restamps_tx: HashMap<Site, (u32, translate::StampCtorIn)> = facts
        .local_restamps
        .iter()
        .filter_map(|(&site, &(local, key))| {
            stamp_in_of_key
                .get(&key)
                .cloned()
                .map(|si| (site, (local, si)))
        })
        .collect();
    // Shared-generated-ctor construct sites: per-site stamp descriptors
    // (the site's snapshot-resolved class), consulted where the
    // script-keyed maps miss.
    let construct_sites_tx: HashMap<Site, translate::StampCtorIn> = facts
        .construct_site_keys
        .iter()
        .filter_map(|(&site, key)| stamp_in_of_key.get(key).cloned().map(|si| (site, si)))
        .collect();
    // Per-method frame `this` guards: an exact ctor-class home uses the
    // member's own table; a predictor range home (lo < hi, contiguous ids)
    // uses the group's universal-prefix table.
    let this_layouts_tx: HashMap<ScriptId, translate::ThisLayoutIn> = facts
        .this_layouts
        .iter()
        .filter_map(|(&m, &(lo, hi))| {
            let (fields, masks, ranges) = if lo == hi {
                (
                    likely_class_layouts[&lo].clone(),
                    masks_of(LayoutKey::new(lo.get())),
                    ranges_of(LayoutKey::new(lo.get())),
                )
            } else {
                let (f, mk) = facts.group_tables.get(&lo)?;
                // A group home serves every member of the contiguous id
                // span, so a position may claim a range only if every
                // member claims one; the group's row is their hull.
                let rs = (0..f.len()).map(|i| span_range(lo, hi, i)).collect();
                (
                    f.clone(),
                    mk.iter().copied().map(Claim::of_prims).collect(),
                    rs,
                )
            };
            Some((
                m,
                translate::ThisLayoutIn {
                    cell_addr: cell_of(LayoutKey::new(lo.get())),
                    layout_id: ctor_layout_id[&lo],
                    hi_layout_id: ctor_layout_id[&hi],
                    fields,
                    masks,
                    ranges,
                    init_home: facts.deleg_inits.contains(&m),
                },
            ))
        })
        .collect();
    // ...and per-site class facts for arbitrary receivers (same exact vs
    // range split; the slot indexes the served table either way).
    let masked = |key: LayoutKey| masks_of(key).iter().any(|m| !m.is_none());
    let shallow_possible = |key: LayoutKey| {
        masked(key)
            && stamp_in_of_key.get(&key).is_none_or(|si| {
                si.prefix_keys
                    .iter()
                    .all(|&p| masked(layout_ctors[p as usize]))
            })
    };
    let prop_sites_tx: HashMap<Site, translate::PropSiteIn> = facts
        .prop_sites
        .iter()
        .map(|(&k, &(lo, hi, slot, mask))| {
            // The mask rides the fact from emission: sub-range los are
            // not group los, so recomputing from group tables here would
            // silently drop (or zero) sub-range facts. Fullword/dims mode
            // fills wmask-starved sites from the typed tier (same key
            // range only).
            let mask = if fullword_masks && mask.is_none() {
                facts
                    .typed_sites
                    .get(&k)
                    .filter(|&&(tlo, thi, tm)| tlo == lo && thi == hi && !tm.is_none())
                    .map_or(Claim::NONE, |&(_, _, tm)| tm)
            } else {
                mask
            };
            // Ranges ride the same key span as the fact, hulled over its
            // members. Gated on the mask: the RANGES bit is only ever
            // consumed beside a tag claim.
            let range = (!mask.is_none())
                .then(|| span_range(lo, hi, slot.get() as usize))
                .flatten();
            (
                k,
                translate::PropSiteIn {
                    cell_addr: cell_of(LayoutKey::new(lo.get())),
                    slot: slot.get(),
                    layout_id: ctor_layout_id[&lo],
                    hi_layout_id: ctor_layout_id[&hi],
                    claim: mask,
                    range,
                    shallow_possible: (lo.get()..=hi.get())
                        .all(|key| shallow_possible(LayoutKey::new(key))),
                },
            )
        })
        .collect();
    // Per-fused-binding fuse words (u32 each; 0 unarmed, 1 armed ==
    // reads fold to the predicted literal, else blown), zero-init.
    let gname_fuse_base = this_slots_base + 40 * u32::try_from(layout_ctors.len()).unwrap();
    let fused_gnames_tx: HashMap<NameId, translate::FusedGname> = fused_list
        .iter()
        .enumerate()
        .map(|(i, &(n, b))| {
            (
                n,
                translate::FusedGname {
                    fuse_addr: gname_fuse_base + 4 * i as u32,
                    boxed: b,
                },
            )
        })
        .collect();
    // The global megamorphic get table (fixed size, so its base is
    // known pre-translation for the inline poly probe; GC-zeroed).
    let mega_get_base = gname_fuse_base + 4 * u32::try_from(fused_list.len()).unwrap();
    // The set-side megamorphic table follows (fixed size, GC-zeroed).
    let mega_set_base = mega_get_base + translate::MEGA_GET_SIZE * translate::MEGA_GET_ENTRY_BYTES;
    // Math native-pointer slots (startup-written JSNative addresses; the
    // math arms' clone-proof callee matches). 4 bytes per MN_* slot.
    let math_natives_base =
        mega_set_base + translate::MEGA_SET_SIZE * translate::MEGA_SET_ENTRY_BYTES;
    let append_cache_base = math_natives_base + 4 * translate::MATH_NATIVE_SLOTS;
    // The (shape, atom)-hashed accessor-call cache (fixed size, GC-zeroed;
    // published through its own region-table slot, ABI v5).
    let accessor_cache_base =
        append_cache_base + translate::APPEND_CACHE_SIZE * translate::APPEND_CACHE_ENTRY_BYTES;
    let prop_ic_base = accessor_cache_base
        + translate::ACCESSOR_CACHE_SIZE * translate::ACCESSOR_CACHE_ENTRY_BYTES;
    Ok(EnvLayout {
        syn_gname_names,
        syn_gnames,
        gcell_bids,
        likely_fns,
        facts,
        likely_class_layouts,
        likely_elems,
        fused_list,
        stamp_ctors_tx,
        lit_stamps_tx,
        layout_addpred_tx,
        ctor_nslots_tx,
        deleg_restamps_tx,
        arg_restamps_tx,
        local_restamps_tx,
        construct_sites_tx,
        this_layouts_tx,
        prop_sites_tx,
        layout_field_masks_tx,
        layout_field_ranges_tx,
        array_stamp_tx,
        array_elem_tx,
        array_any_claim,
        fused_gnames_tx,
        ctor_layout_id,
        layout_ctors,
        layout_mode,
        num_global_bindings,
        global_slots_base,
        global_vals_base,
        prop_ic_gen_base,
        night_stack_limit_base,
        fn_class_slot,
        static_strings_slot,
        atom_table_slot,
        nursery_pos_slot,
        nursery_end_slot,
        str_ccat_cell,
        str_cat_cell,
        str_fcc_cell,
        str_fuse_addr_slot,
        array_class_slot,
        builtin_cells_base,
        ta_class_base,
        args_class_base,
        strlit_slot,
        this_cells_base,
        this_slots_base,
        gname_fuse_base,
        mega_get_base,
        mega_set_base,
        math_natives_base,
        append_cache_base,
        accessor_cache_base,
        prop_ic_base,
    })
}

pub struct TranslateOut {
    pub atoms: translate::AtomTable,
    pub source_id_to_func: HashMap<u32, Func>,
    /// Per sid, the function actually sitting in the funcref table: the
    /// body itself (single-result ABI) or its `night_abi_sig` adapter
    /// (widened-ABI bodies).
    pub source_id_to_table_func: HashMap<u32, Func>,
    pub sid_to_index: HashMap<u32, u32>,
    pub fuse_binding_index: HashMap<u32, u32>,
    pub strlit_patches: Vec<(Func, waffle::Value, u32)>,
    pub regex_entries: Vec<(JsString, u32, u32, u32, u32, u32)>,
    pub prop_ic_base: usize,
    pub prop_ic_size: usize,
    pub call_cells_base: usize,
    pub call_cells_size: usize,
    pub alloc_cells_base: usize,
    pub alloc_cells_size: usize,
    pub intrinsic_cells_base: usize,
    pub intrinsic_cells_size: usize,
    /// Per-funcidx ctor full-layout slot counts (u32 each, 0 = unknown).
    /// The production caller fills the content from the likelier's
    /// `ctor_nslots` map via `sid_to_index`; in-process batches leave it
    /// zero (sizing off, codegen identical).
    pub ctor_nslots_base: usize,
    pub ctor_nslots_size: usize,
}

/// Translate every compilable script (and regex program) into an appended
/// body, then arm the likely-callee / fuse-call sites and patch the cell-region
/// placeholder consts. `skip` and `on_compiled` are the caller's per-script
/// hooks (debug skip lists, compiled-script bookkeeping; a caller can pass
/// no-ops). `post_region` supplies the base of the contiguous
/// post-translation region (prop-IC ways + cell regions), given its total
/// size and the string-literal blob size (snapshot flow: the fixed
/// `env.prop_ic_base`; in-process: a caller allocation that also reserves the
/// strlit blob after an 8-aligned pad).
pub fn translate_all(
    m: &mut Module,
    source: &Source,
    root_id: SourceObjectId,
    opts: &Options,
    helpers: translate::Helpers,
    env: &EnvLayout,
    // The compilation's string table, moved in for the translation phase
    // (`std::mem::take(&mut env.facts.names)` at the call site): codegen
    // still interns -- it reaches scripts the analysis skipped -- and the
    // atom table adds the emitted module's dense `atomId` numbering on top of
    // the shared ids.
    names: Names,
    mem: waffle::Memory,
    skip: &mut dyn FnMut(SourceObjectId) -> bool,
    on_compiled: &mut dyn FnMut(SourceObjectId, u32),
    post_region: &mut dyn FnMut(u32, u32) -> Result<u32, String>,
) -> Result<TranslateOut, String> {
    let mut atoms = translate::AtomTable::new(names);

    // Direct calls: callee source_id -> its compiled `Func` (for the direct
    // `call` target), and the collected per-function placeholders to rewrite once
    // all bodies are placed.
    let mut source_id_to_func: HashMap<u32, Func> = HashMap::default();
    let mut source_id_to_table_func: HashMap<u32, Func> = HashMap::default();
    let mut sid_to_index: HashMap<u32, u32> = HashMap::default();
    let mut pending_adapters: Vec<(SourceObjectId, Func)> = Vec::new();
    let mut body_off_patch_sites: Vec<(Func, waffle::Value)> = Vec::new();
    let mut ctor_nslots_patch_sites: Vec<(Func, waffle::Value, u32)> = Vec::new();
    let mut likely_patches: Vec<(Func, waffle::Value, waffle::Value, u32)> = Vec::new();
    let mut fuse_call_patches: Vec<(Func, translate::FuseCallPatch)> = Vec::new();
    let mut call_cell_patches: Vec<(Func, waffle::Value, u32)> = Vec::new();
    let mut intrinsic_cell_patches: Vec<(Func, waffle::Value, u32)> = Vec::new();
    let mut alloc_cell_patches: Vec<(Func, waffle::Value, u32)> = Vec::new();
    let mut iof_cell_patches: Vec<(Func, waffle::Value, u32)> = Vec::new();
    let mut construct_cell_patches: Vec<(Func, waffle::Value, u32)> = Vec::new();
    let mut strlit_patches: Vec<(Func, waffle::Value, u32)> = Vec::new();
    let mut prop_ic_patches: Vec<(Func, waffle::Value, u32)> = Vec::new();
    let mut n_compiled = 0usize;
    let mut n_skipped = 0usize;
    let script_ids: Vec<SourceObjectId> = source
        .objects()
        .filter_map(|(id, obj)| matches!(obj, SourceObject::Script(_)).then_some(id))
        .collect();
    // Whole-module BigInt-freedom (for the F64 arith fast track): a
    // module that can never manufacture a BigInt lets Sub/Mul/Div carry their
    // (then always-numeric) result on the unboxed f64 track soundly, even when
    // the operand types are statically unknown.
    let bigint_free = module_is_bigint_free(source, &script_ids);
    let flag_demand = bbv::compute_flag_demand(source, &env.facts);
    let tx_ctx = translate::TranslateCtx {
        helpers,
        source,
        opts,
        bigint_free,
        syn_gnames: &env.syn_gnames,
        gcell_bids: &env.gcell_bids,
        likely_fns: &env.likely_fns,
        facts: &env.facts,
        flag_demand: &flag_demand,
        this_layouts_in: &env.this_layouts_tx,
        stamp_ctors_in: &env.stamp_ctors_tx,
        layout_addpred_in: &env.layout_addpred_tx,
        ctor_nslots_in: &env.ctor_nslots_tx,
        deleg_restamps_in: &env.deleg_restamps_tx,
        arg_restamps_in: &env.arg_restamps_tx,
        local_restamps_in: &env.local_restamps_tx,
        construct_sites_in: &env.construct_sites_tx,
        lit_stamps_in: &env.lit_stamps_tx,
        prop_sites_in: &env.prop_sites_tx,
        layout_field_masks_in: &env.layout_field_masks_tx,
        layout_field_ranges_in: &env.layout_field_ranges_tx,
        array_stamp_in: &env.array_stamp_tx,
        array_elem_in: &env.array_elem_tx,
        array_any_claim: env.array_any_claim,
        likely_elems: &env.likely_elems,
        fused_gnames: &env.fused_gnames_tx,
    };
    for id in script_ids {
        let SourceObject::Script(script) = source.object(id) else {
            unreachable!()
        };
        if skip(id) {
            n_skipped += 1;
            continue;
        }
        match bbv::translate_script(
            &tx_ctx,
            m,
            &mut atoms,
            ScriptId::new(id.id()),
            script,
            id == root_id,
        )? {
            translate::Outcome::Compiled {
                sig,
                body,
                likely_patches: lp,
                fuse_call_patches: fcp,
                call_cell_patches: ccp,
                alloc_cell_patches: acp,
                iof_cell_patches: icp,
                construct_cell_patches: xcp,
                strlit_patches: slp,
                intrinsic_cell_patches: gicp,
                prop_ic_patches: icp2,
                body_off_patches: bop,
                ctor_nslots_patches: cnp,
            } => {
                let f = m.funcs.push(FuncDecl::Body(
                    sig,
                    format!("night_script_{}", id.id()),
                    body,
                ));
                // Widened-ABI (BBV) bodies go in the table behind a
                // `night_abi_sig` adapter; direct-call patches still
                // target the body itself (source_id_to_func). The body
                // takes its own table slot now (the module's table order
                // must stay exactly the blob order -- the in-process
                // runner appends every blob to the funcref table) and the
                // adapters are emitted as one contiguous block after the
                // loop, because interleaving them with bodies measurably
                // worsens instruction-cache behaviour. `body slot ==
                // adapter slot - count`
                // holds because bodies and adapters keep the same order.
                if sig == tx_ctx.helpers.night_abi_sig2 {
                    place_in_table(m, f)?;
                    pending_adapters.push((id, f));
                } else {
                    let index = place_in_table(m, f)?;
                    on_compiled(id, index);
                    source_id_to_table_func.insert(id.id(), f);
                    sid_to_index.insert(id.id(), index);
                }
                source_id_to_func.insert(id.id(), f);
                for (expected, call, callee_sid) in lp {
                    likely_patches.push((f, expected, call, callee_sid));
                }
                for p in fcp {
                    fuse_call_patches.push((f, p));
                }
                for (addr, idx) in ccp {
                    call_cell_patches.push((f, addr, idx));
                }
                for (addr, idx) in acp {
                    alloc_cell_patches.push((f, addr, idx));
                }
                for (addr, idx) in icp {
                    iof_cell_patches.push((f, addr, idx));
                }
                for (addr, idx) in xcp {
                    construct_cell_patches.push((f, addr, idx));
                }
                for (addr, off) in slp {
                    strlit_patches.push((f, addr, off));
                }
                for (addr, row) in gicp {
                    intrinsic_cell_patches.push((f, addr, row));
                }
                for (addr, off) in icp2 {
                    prop_ic_patches.push((f, addr, off));
                }
                for v in bop {
                    body_off_patch_sites.push((f, v));
                }
                for v in cnp {
                    ctor_nslots_patch_sites.push((f, v, 0));
                }
                n_compiled += 1;
            }
            translate::Outcome::Skipped(reason) => {
                n_skipped += 1;
                if opts.diagnostics.bbv {
                    crate::diag_line!("night: skip script#{} ({reason})", id.id());
                }
                log::trace!("night: skip script#{} ({reason})", id.id());
            }
        }
    }
    // The contiguous adapter block (see the loop comment): one
    // `night_abi_sig` adapter per widened-ABI body, in body order, so every
    // body's table slot is exactly `its adapter's slot - n_bodies`. The
    // `funcidx - offset` placeholders patch to that count.
    let n_bodies = u32::try_from(pending_adapters.len()).unwrap();
    for &(id, f) in &pending_adapters {
        let a = abi_adapter(m, tx_ctx.helpers.night_abi_sig, f, id.id());
        let index = place_in_table(m, a)?;
        on_compiled(id, index);
        source_id_to_table_func.insert(id.id(), a);
        sid_to_index.insert(id.id(), index);
    }
    for (f, v) in body_off_patch_sites {
        if let FuncDecl::Body(_, _, body) = &mut m.funcs[f] {
            if let ValueDef::Operator(Operator::I32Const { value }, _, _) = &mut body.values[v] {
                *value = n_bodies;
            }
        }
    }
    if opts.diagnostics.stats {
        crate::diag_line!("night: {n_compiled} scripts compiled, {n_skipped} skipped");
    }

    // ---- Regex AOT: compile each snapshotted irregexp bytecode program to a
    // wasm matcher (one per subject encoding) with its own all-i32 signature
    // (callable from C by casting the table index to a function pointer).
    // Entries land in the regex descriptor table the reactor parses at
    // startup; a variant that fails to translate keeps table index 0 (the
    // runtime falls back to the bytecode interpreter for it).
    let regex_sig = m.signatures.push(SignatureData {
        params: vec![
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
        ],
        returns: vec![Type::I32],
    });
    let regex_ci_helper = find_export_func(m, "night_runtime_regex_ci_compare").ok();
    // (pattern, flags, latin1 idx, twobyte idx, num_registers, pair_count)
    let mut regex_entries: Vec<(JsString, u32, u32, u32, u32, u32)> = Vec::new();
    {
        let mut n_regex_variants = 0usize;
        for (i, rp) in source.regex_programs.iter().enumerate() {
            let mut idx_pair = [0u32; 2];
            for (k, (bytes, wide)) in [(&rp.latin1_bytecode, false), (&rp.twobyte_bytecode, true)]
                .iter()
                .enumerate()
            {
                if bytes.is_empty() {
                    continue;
                }
                let inp = regex::RegexTranslateInput {
                    bytecode: bytes,
                    wide: *wide,
                    total_regs: rp.num_registers,
                    output_regs: rp.pair_count * 2,
                };
                match regex::translate(m, regex_sig, mem, regex_ci_helper, &inp) {
                    Ok(body) => {
                        let f = m.funcs.push(FuncDecl::Body(
                            regex_sig,
                            format!("night_regex_{}_{}", i, if *wide { "tb" } else { "l1" }),
                            body,
                        ));
                        idx_pair[k] = place_in_table(m, f)?;
                        n_regex_variants += 1;
                    }
                    Err(e) => {
                        log::warn!(
                            "night: regex#{i} {} variant skipped: {e}",
                            if *wide { "twobyte" } else { "latin1" }
                        );
                    }
                }
            }
            if idx_pair[0] != 0 || idx_pair[1] != 0 {
                regex_entries.push((
                    rp.pattern.clone(),
                    rp.flags,
                    idx_pair[0],
                    idx_pair[1],
                    rp.num_registers,
                    rp.pair_count,
                ));
            }
        }
        if opts.diagnostics.stats {
            crate::diag_line!(
                "night: {} regexes AOT-compiled ({} matcher variants) of {}",
                regex_entries.len(),
                n_regex_variants,
                source.regex_programs.len()
            );
        }
    }

    // Likely-callee sites: patch the expected-funcidx const to the callee's
    // table index and the stub `call` to the callee body. An uncompiled
    // callee leaves the const at u32::MAX (never equals a live funcidx), so
    // the likely arm is dead and dispatch stays classify + call_indirect.
    let mut n_likely = 0usize;
    for (f, expected, call, callee_sid) in likely_patches {
        let (Some(&callee), Some(&index)) = (
            source_id_to_func.get(&callee_sid),
            sid_to_index.get(&callee_sid),
        ) else {
            continue;
        };
        if let FuncDecl::Body(_, _, body) = &mut m.funcs[f] {
            if let waffle::ValueDef::Operator(waffle::Operator::I32Const { value: g }, _, _) =
                &mut body.values[expected]
            {
                *g = index;
            }
            if let waffle::ValueDef::Operator(waffle::Operator::Call { function_index }, _, _) =
                &mut body.values[call]
            {
                *function_index = callee;
                n_likely += 1;
            }
        }
    }
    if opts.diagnostics.stats {
        crate::diag_line!("night: {n_likely} likely-callee sites armed");
    }

    // Fuse-guarded direct calls: a binding gets one expected callee
    // (the reactor validates the armed value's AOT target against it before
    // arming). Bindings predicted with conflicting callees across sites, or
    // whose callee did not compile, stay out of the table and their sites'
    // arms stay dead (enabled const 0).
    let mut fuse_binding_expected: HashMap<u32, u32> = HashMap::default();
    let mut fuse_binding_conflict: HashSet<u32> = HashSet::default();
    for (_, p) in &fuse_call_patches {
        match fuse_binding_expected.entry(p.binding) {
            std::collections::hash_map::Entry::Occupied(e) => {
                if *e.get() != p.callee.get() {
                    fuse_binding_conflict.insert(p.binding);
                }
            }
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(p.callee.get());
            }
        }
    }
    for bid in &fuse_binding_conflict {
        fuse_binding_expected.remove(bid);
    }
    let mut n_fuse_calls = 0usize;
    for (f, p) in fuse_call_patches {
        let (enabled, call, bid) = (p.enabled, p.call, p.binding);
        if fuse_binding_conflict.contains(&bid) {
            continue;
        }
        let Some(&callee) = source_id_to_func.get(&p.callee.get()) else {
            fuse_binding_expected.remove(&bid);
            continue;
        };
        if let FuncDecl::Body(_, _, body) = &mut m.funcs[f] {
            if let waffle::ValueDef::Operator(waffle::Operator::I32Const { value: g }, _, _) =
                &mut body.values[enabled]
            {
                *g = 1;
            }
            if let waffle::ValueDef::Operator(waffle::Operator::Call { function_index }, _, _) =
                &mut body.values[call]
            {
                *function_index = callee;
                n_fuse_calls += 1;
            }
        }
    }
    // bindingId -> callee funcref-table index (what the reactor's arm-time
    // validation compares NightCalleeNightTarget's low word against).
    let fuse_binding_index: HashMap<u32, u32> = fuse_binding_expected
        .iter()
        .filter_map(|(&bid, sid)| sid_to_index.get(sid).map(|&idx| (bid, idx)))
        .collect();
    if opts.diagnostics.stats {
        crate::diag_line!(
            "night: {n_fuse_calls} fuse-guarded call sites armed ({} bindings)",
            fuse_binding_index.len()
        );
    }

    let prop_ic_size = atoms.prop_cache_count() as usize * translate::INLINE_IC_STRIDE as usize;
    if opts.diagnostics.stats {
        crate::diag_line!(
            "night: {} property-IC sites, {} bytes ({} per site)",
            atoms.prop_cache_count(),
            prop_ic_size,
            translate::INLINE_IC_STRIDE
        );
    }
    let call_cells_size = if atoms.call_cell_count() > 0 {
        (atoms.call_cell_count() as usize + 1) * translate::CALL_CELL_BYTES as usize
    } else {
        0
    };
    let alloc_cells_size = atoms.alloc_cell_count() as usize * translate::ALLOC_CELL_BYTES as usize;
    let iof_cells_size = if atoms.iof_cell_count() > 0 {
        (atoms.iof_cell_count() as usize + 1) * translate::IOF_CELL_BYTES as usize
    } else {
        0
    };
    let construct_cells_size = if atoms.construct_cell_count() > 0 {
        (atoms.construct_cell_count() as usize + 1) * translate::CONSTRUCT_CELL_BYTES as usize
    } else {
        0
    };
    let intrinsic_cells_size =
        atoms.intrinsic_cell_count() as usize * translate::INTRINSIC_CELL_BYTES as usize;
    // Ctor-nslots region: one u32 per funcref-table index, absolute
    // indexing (the classified funcidx indexes it directly; the prefix
    // below the first script slot stays zero). Static data -- deliberately
    // absent from every GC-zeroing descriptor.
    let ctor_nslots_size = 4 * (sid_to_index.values().max().copied().unwrap_or(0) as usize + 1);
    let post_total = prop_ic_size
        + call_cells_size
        + alloc_cells_size
        + iof_cells_size
        + construct_cells_size
        + intrinsic_cells_size
        + ctor_nslots_size;
    let prop_ic_base = post_region(
        u32::try_from(post_total).map_err(|_| "post-translation region exceeds u32".to_string())?,
        u32::try_from(atoms.strlit_blob().len())
            .map_err(|_| "strlit blob exceeds u32".to_string())?,
    )? as usize;
    // Prop-IC way/row consts were emitted with the layout base already baked
    // (a no-op re-patch there); re-anchor them to the served region base.
    patch_const(m, prop_ic_patches, u32::try_from(prop_ic_base).unwrap(), 1);
    // Callee value-cell region: one 16-byte row per inline-classify site (plus
    // the shared trash row 0 nursery-callee stores divert to), right after the
    // prop-IC ways. Its base is only known now (the prop-IC size is a
    // translation output), so each site baked placeholder address consts;
    // patch them to the real row addresses. No data segment: zero == empty
    // row. The reactor zeroes the region on major GC (cached value/script
    // bits are GC pointers).
    let call_cells_base = prop_ic_base + prop_ic_size;
    patch_const(
        m,
        call_cell_patches,
        u32::try_from(call_cells_base).unwrap(),
        translate::CALL_CELL_BYTES,
    );
    if opts.diagnostics.stats {
        crate::diag_line!("night: {} callee value cells", atoms.call_cell_count());
    }
    // Inline-alloc cell region: one 32-byte row per object/array literal
    // site, right after the call cells (same lifecycle: placeholder consts
    // patched here, no data segment so zero == empty, reactor zeroes on
    // major GC since rows cache shape/site pointers).
    let alloc_cells_base = call_cells_base + call_cells_size;
    patch_const(
        m,
        alloc_cell_patches,
        u32::try_from(alloc_cells_base).unwrap(),
        translate::ALLOC_CELL_BYTES,
    );
    if opts.diagnostics.stats {
        crate::diag_line!("night: {} inline-alloc cells", atoms.alloc_cell_count());
    }
    // Instanceof cell region: one 16-byte row per Instanceof site (row idx+1,
    // row 0 reserved), right after the alloc cells. No data segment (zero ==
    // empty). NOT GC-zeroed -- the per-cell generation stamp (populated with
    // InlineGen(), which the major-GC callback bumps) invalidates stale rows,
    // and the inline hit reads the live prototype off the receiver, never a
    // cached pointer.
    let iof_cells_base = alloc_cells_base + alloc_cells_size;
    patch_const(
        m,
        iof_cell_patches,
        u32::try_from(iof_cells_base).unwrap(),
        translate::IOF_CELL_BYTES,
    );
    if opts.diagnostics.stats {
        crate::diag_line!("night: {} instanceof cells", atoms.iof_cell_count());
    }
    // Construct-`this` cell region: one 40-byte row per specialized `new` site
    // (row idx+1), right after the iof cells. No data segment (zero == empty).
    // NOT GC-zeroed -- the generation stamp invalidates stale rows and the
    // inline hit re-reads the live ctor prototype; the nursery-bump alloc
    // fields are only consulted after those guards pass.
    let construct_cells_base = iof_cells_base + iof_cells_size;
    patch_const(
        m,
        construct_cell_patches,
        u32::try_from(construct_cells_base).unwrap(),
        translate::CONSTRUCT_CELL_BYTES,
    );
    if opts.diagnostics.stats {
        crate::diag_line!("night: {} construct cells", atoms.construct_cell_count());
    }
    // Intrinsic value-cell region: one 8-byte row per distinct intrinsic name
    // (shared across sites), right after the construct cells. No data segment
    // (zero == unresolved); the reactor zeroes it on major GC (cached bits
    // are GC pointers).
    let intrinsic_cells_base = construct_cells_base + construct_cells_size;
    patch_const(
        m,
        intrinsic_cell_patches,
        u32::try_from(intrinsic_cells_base).unwrap(),
        translate::INTRINSIC_CELL_BYTES,
    );
    if opts.diagnostics.stats {
        crate::diag_line!(
            "night: {} intrinsic value cells",
            atoms.intrinsic_cell_count()
        );
    }
    let ctor_nslots_base = intrinsic_cells_base + intrinsic_cells_size;
    patch_const(
        m,
        ctor_nslots_patch_sites,
        u32::try_from(ctor_nslots_base).unwrap(),
        1,
    );

    Ok(TranslateOut {
        atoms,
        source_id_to_func,
        source_id_to_table_func,
        sid_to_index,
        fuse_binding_index,
        strlit_patches,
        regex_entries,
        prop_ic_base,
        prop_ic_size,
        call_cells_base,
        call_cells_size,
        alloc_cells_base,
        alloc_cells_size,
        intrinsic_cells_base,
        intrinsic_cells_size,
        ctor_nslots_base,
        ctor_nslots_size,
    })
}
