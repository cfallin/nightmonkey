// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! In-process AOT batch compilation: build a fresh module whose engine
//! helpers are function imports, translate the Source tree into defined
//! bodies, and carve those bodies into wasm-jit-runner function blobs
//! (`0x60 functype ++ code-entry body`, no size prefix). The runner
//! reassembles them with the extern imports at function indices
//! `0..nextern` and blob `i` at `nextern + i`, and appends blob `i` to the
//! live funcref table at `table_base + i` -- both index spaces match this
//! module by construction, so call/const immediates are correct as
//! emitted. All region addresses come from a caller-supplied allocator
//! (two calls: the fixed layout region, then the post-translation prop-IC/
//! cell region + string-literal blob); zero-initialized memory means
//! every cell is unarmed, so the caller must return zeroed (calloc-style),
//! 8-aligned allocations.

use waffle::entity::EntityRef;
use waffle::{
    Export, ExportKind, Func, FuncDecl, FunctionBody, Import, ImportKind, MemoryData, Module,
    Operator, SignatureData, TableData, Type, ValueDef,
};

use super::{
    layout_env, patch_const, resolve_helpers, serialize_atom_table, serialize_fuse_table,
    serialize_global_binding_table, serialize_layout_table, serialize_regex_table, translate,
    translate_all, HelperPrebuilt, TranslateOut,
};
use crate::env_regions::{RegionWords, ABI_VERSION, ENV_DESC_HEADER_WORDS, REGION_COUNT};
use crate::options::Options;
use crate::source::{Source, SourceObjectId};
use rustc_hash::FxHashMap as HashMap;

/// One engine helper the batch imports: its name, the live funcref-table
/// index of the C function (what the runner resolves the import from), and
/// its signature.
pub struct HelperImportSpec {
    pub name: String,
    pub sig: SignatureData,
    pub table_index: u32,
}

/// The built batch. `blobs[i]` is runner blob `i` (function index
/// `nextern + i`, predicted table index `table_base + i`); `scripts` maps
/// each compiled script's source id to its blob position; `env_desc` is the
/// serialized environment descriptor (see `ENV_DESC_WORDS`).
pub struct InprocOut {
    pub blobs: Vec<Vec<u8>>,
    pub extern_table_indices: Vec<u32>,
    pub scripts: Vec<(u32, u32)>,
    pub env_desc: Vec<u8>,
}

/// env_desc layout (the engine side is `NightEnvDescHeaderWords` and
/// `NIGHT_ENV_REGIONS` in runtime/NightEnv.h): a header of
/// `ENV_DESC_HEADER_WORDS` little-endian u32 words --
///   0 abi_version   1 region_count
///   2 strlit_off    3 strlit_len    4 strlit_addr (copy dest; 0 = none)
/// -- then `REGION_COUNT` region words in `RegionWords` order, then the
/// serialized tables.
///
/// `strlit_off` and every `RegionKind::Table` region word are byte offsets
/// into the env_desc buffer, which the reader rebases onto the buffer's
/// address; `Addr` words are absolute linear-memory addresses inside the
/// caller-allocated regions and `Len` words are byte lengths. (The snapshot
/// flow's region table has no offsets: there every word is already
/// absolute.)
pub const ENV_DESC_WORDS: usize = ENV_DESC_HEADER_WORDS + REGION_COUNT;

/// Parse a helper signature string: `<ret>(<params>)` with one char per
/// type -- `i` = i32, `j` = i64, `f` = f32, `d` = f64, and `v` (return
/// position only) = void.
pub fn parse_sig_str(s: &str) -> Result<SignatureData, String> {
    let ty = |c: u8| -> Result<Type, String> {
        match c {
            b'i' => Ok(Type::I32),
            b'j' => Ok(Type::I64),
            b'f' => Ok(Type::F32),
            b'd' => Ok(Type::F64),
            _ => Err(format!("bad type char `{}` in sig `{s}`", c as char)),
        }
    };
    let b = s.as_bytes();
    if b.len() < 3 || b[1] != b'(' || b[b.len() - 1] != b')' {
        return Err(format!("malformed sig string `{s}`"));
    }
    let returns = if b[0] == b'v' {
        vec![]
    } else {
        vec![ty(b[0])?]
    };
    let params = b[2..b.len() - 1]
        .iter()
        .map(|&c| ty(c))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SignatureData { params, returns })
}

fn write_leb_u32(out: &mut Vec<u8>, mut v: u32) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
}

fn valtype_byte(v: wasmparser::ValType) -> Result<u8, String> {
    match v {
        wasmparser::ValType::I32 => Ok(0x7F),
        wasmparser::ValType::I64 => Ok(0x7E),
        wasmparser::ValType::F32 => Ok(0x7D),
        wasmparser::ValType::F64 => Ok(0x7C),
        other => Err(format!("unsupported blob valtype {other:?}")),
    }
}

/// Carve the emitted module's defined functions into runner blobs.
fn carve_blobs(bytes: &[u8], n_imports: usize) -> Result<Vec<Vec<u8>>, String> {
    use wasmparser::{Parser, Payload};
    let mut types: Vec<wasmparser::FuncType> = Vec::new();
    let mut func_types: Vec<u32> = Vec::new();
    let mut n_func_imports = 0usize;
    let mut blobs: Vec<Vec<u8>> = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.map_err(|e| format!("parse emitted batch: {e}"))? {
            Payload::TypeSection(reader) => {
                for rec_group in reader {
                    for ty in rec_group
                        .map_err(|e| format!("type section: {e}"))?
                        .into_types()
                    {
                        match &ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(fty) => types.push(fty.clone()),
                            _ => return Err("non-function type in emitted batch".to_string()),
                        }
                    }
                }
            }
            Payload::ImportSection(reader) => {
                let is_func = |ty: &wasmparser::TypeRef| {
                    matches!(
                        ty,
                        wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_)
                    )
                };
                for imports in reader {
                    match imports.map_err(|e| format!("import section: {e}"))? {
                        wasmparser::Imports::Single(_, import) => {
                            if is_func(&import.ty) {
                                n_func_imports += 1;
                            }
                        }
                        wasmparser::Imports::Compact1 { items, .. } => {
                            for item in items {
                                let item = item.map_err(|e| format!("import section: {e}"))?;
                                if is_func(&item.ty) {
                                    n_func_imports += 1;
                                }
                            }
                        }
                        wasmparser::Imports::Compact2 { ty, names, .. } => {
                            if is_func(&ty) {
                                n_func_imports += names.count() as usize;
                            }
                        }
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                for sig_idx in reader {
                    func_types.push(sig_idx.map_err(|e| format!("function section: {e}"))?);
                }
            }
            Payload::CodeSectionEntry(body) => {
                let i = blobs.len();
                let ty_idx = *func_types
                    .get(i)
                    .ok_or_else(|| "code entry without function entry".to_string())?;
                let fty = types
                    .get(ty_idx as usize)
                    .ok_or_else(|| "function type out of range".to_string())?;
                let mut blob = vec![0x60u8];
                write_leb_u32(&mut blob, fty.params().len() as u32);
                for &p in fty.params() {
                    blob.push(valtype_byte(p)?);
                }
                write_leb_u32(&mut blob, fty.results().len() as u32);
                for &r in fty.results() {
                    blob.push(valtype_byte(r)?);
                }
                blob.extend_from_slice(&bytes[body.range()]);
                blobs.push(blob);
            }
            _ => {}
        }
    }
    if n_func_imports != n_imports {
        return Err(format!(
            "emitted batch has {n_func_imports} function imports, expected {n_imports}"
        ));
    }
    if blobs.len() != func_types.len() {
        return Err("code/function section length mismatch".to_string());
    }
    Ok(blobs)
}

/// Defined functions pushed before `translate_all` runs; the funcref table is
/// pre-padded past them so every table-placed function's index is exactly
/// `table_base + blob position`.
const PRE_BODIES: u32 = 10;

pub fn build_inprocess_batch(
    source: &Source,
    root_id: SourceObjectId,
    opts: &Options,
    helper_specs: &[HelperImportSpec],
    table_base: u32,
    alloc: &mut dyn FnMut(u32) -> Result<u32, String>,
) -> Result<InprocOut, String> {
    let mut m = Module::empty();
    let mem = m.memories.push(MemoryData {
        initial_pages: 1,
        maximum_pages: None,
        segments: Vec::new(),
    });
    let mut by_name: HashMap<&str, Func> = HashMap::default();
    for spec in helper_specs {
        let sig = m.signatures.push(spec.sig.clone());
        let f = m.funcs.push(FuncDecl::Import(sig, spec.name.clone()));
        m.imports.push(Import {
            module: "env".to_string(),
            name: spec.name.clone(),
            kind: ImportKind::Func(f),
        });
        if by_name.insert(spec.name.as_str(), f).is_some() {
            return Err(format!("duplicate helper `{}`", spec.name));
        }
    }
    let n_imports = helper_specs.len();
    // translate_all resolves the optional regex case-insensitive helper via
    // an export lookup; alias the import as an export.
    if let Some(&f) = by_name.get("night_runtime_regex_ci_compare") {
        m.exports.push(Export {
            name: "night_runtime_regex_ci_compare".to_string(),
            kind: ExportKind::Func(f),
        });
    }

    // Size the fixed region with a base-0 layout (sizes are base-invariant),
    // then lay out for real at the allocated base.
    let fixed_size = layout_env(source, root_id, 0, opts)?.prop_ic_base;
    let arena_base = alloc(fixed_size)?;
    if arena_base == 0 || arena_base % 8 != 0 {
        return Err(format!("bad fixed-region base {arena_base:#x}"));
    }
    let mut env = layout_env(source, root_id, arena_base, opts)?;

    let night_abi_sig = m.signatures.push(SignatureData {
        params: vec![
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I64,
        ],
        returns: vec![Type::I32],
    });
    // The runner's reassembled type section is [extern types 0..nextern,
    // blob types nextern..]; `call_indirect` immediates reference this
    // signature index, so it must land at nextern and blob 0 (the stub
    // below) must carry this functype for the immediate to stay
    // structurally correct.
    if night_abi_sig.index() != n_imports {
        return Err("ABI signature index misaligned".to_string());
    }

    let indirect_table = m.tables.push(TableData {
        ty: Type::FuncRef,
        initial: u64::from(table_base + PRE_BODIES),
        max: None,
        func_elements: Some(vec![Func::invalid(); (table_base + PRE_BODIES) as usize]),
    });

    let direct_call_stub = {
        let mut body = FunctionBody::new(&m, night_abi_sig);
        let entry = body.entry;
        let i32_ty = body.single_type_list(Type::I32);
        let one = body.add_value(ValueDef::Operator(
            Operator::I32Const { value: 1 },
            Default::default(),
            i32_ty,
        ));
        body.append_to_block(entry, one);
        body.set_terminator(entry, waffle::Terminator::Return { values: vec![one] });
        m.funcs.push(FuncDecl::Body(
            night_abi_sig,
            "night_direct_stub".to_string(),
            body,
        ))
    };
    let (ta_get_poly, ta_set_poly) =
        translate::build_ta_poly_helpers(&mut m, mem, env.ta_class_base);
    let ic_get_poly = translate::build_ic_get_helper(&mut m, mem, env.mega_get_base);
    let call_classify = super::build_call_classify_helper(&mut m, mem, env.fn_class_slot);
    let elem_append_check =
        super::build_elem_append_helper(&mut m, mem, env.append_cache_base, opts.instrument.guards);
    let ic_set_cold = super::build_ic_set_cold_helper(&mut m, mem, env.mega_set_base);
    let (elem_mega_get, elem_mega_set_probe) =
        super::build_elem_mega_helpers(&mut m, mem, env.mega_get_base, env.mega_set_base);
    if direct_call_stub.index() != n_imports
        || elem_append_check.index() != n_imports + 5
        || ic_set_cold.index() != n_imports + 6
        || elem_mega_get.index() != n_imports + 7
        || elem_mega_set_probe.index() != n_imports + 8
    {
        return Err("pre-body function indices misaligned".to_string());
    }
    let night_abi_sig2 = m.signatures.push(SignatureData {
        params: vec![
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I64,
        ],
        returns: vec![Type::I32, Type::I32],
    });
    let direct_call_stub2 = {
        let mut body = FunctionBody::new(&m, night_abi_sig2);
        let entry = body.entry;
        let i32_ty = body.single_type_list(Type::I32);
        let one = body.add_value(ValueDef::Operator(
            Operator::I32Const { value: 1 },
            Default::default(),
            i32_ty,
        ));
        body.append_to_block(entry, one);
        let zero = body.add_value(ValueDef::Operator(
            Operator::I32Const { value: 0 },
            Default::default(),
            i32_ty,
        ));
        body.append_to_block(entry, zero);
        body.set_terminator(
            entry,
            waffle::Terminator::Return {
                values: vec![one, zero],
            },
        );
        m.funcs.push(FuncDecl::Body(
            night_abi_sig2,
            "night_direct_stub2".to_string(),
            body,
        ))
    };
    if direct_call_stub2.index() != n_imports + PRE_BODIES as usize - 1 {
        return Err("pre-body function count misaligned".to_string());
    }

    let helpers = resolve_helpers(
        &mut m,
        &mut |_, name| {
            by_name
                .get(name)
                .copied()
                .ok_or_else(|| format!("in-process helper `{name}` not provided"))
        },
        HelperPrebuilt {
            mem,
            ta_get_poly,
            ta_set_poly,
            ic_get_poly,
            ic_set_cold,
            elem_mega_get,
            elem_mega_set_probe,
            call_classify,
            elem_append_check,
            night_abi_sig,
            indirect_table,
            direct_call_stub,
            night_abi_sig2,
            direct_call_stub2,
        },
        env.helper_bases(),
        opts.diagnostics.viz,
    )?;

    let mut strlit_addr: u32 = 0;
    // The string table moves from the analysis output to the translator here.
    let names = std::mem::take(&mut env.facts.names);
    let out = translate_all(
        &mut m,
        source,
        root_id,
        opts,
        helpers,
        &env,
        names,
        mem,
        &mut |_| false,
        &mut |id, index| {
            if let Some((_, sh_name)) = source.selfhosted.iter().find(|(sid, _)| *sid == id) {
                log::trace!(
                    "night: compiled selfhosted script#{} ({sh_name}) -> table[{index}]",
                    id.id()
                );
            }
        },
        &mut |cells_total, strlit_len| {
            let cells_padded = if strlit_len > 0 {
                cells_total.next_multiple_of(8)
            } else {
                cells_total
            };
            let base = alloc(cells_padded + strlit_len)?;
            if base == 0 || base % 8 != 0 {
                return Err(format!("bad post-region base {base:#x}"));
            }
            if strlit_len > 0 {
                strlit_addr = base + cells_padded;
            }
            Ok(base)
        },
    )?;
    let TranslateOut {
        mut atoms,
        source_id_to_func: _,
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
        ctor_nslots_base: _,
        ctor_nslots_size: _,
    } = out;

    let strlit_blob = atoms.strlit_blob().to_vec();
    patch_const(&mut m, strlit_patches, strlit_addr, 1);

    // Interned before the atom table serializes (the ids must be in it).
    let layout_bytes = serialize_layout_table(&env, &mut atoms);
    for &(name, _) in &env.fused_list {
        atoms.intern(name);
    }
    let atom_bytes = serialize_atom_table(&atoms);
    let gbind_bytes =
        serialize_global_binding_table(&atoms.names, &env.syn_gname_names, &fuse_binding_index);
    let fuse_bytes = serialize_fuse_table(&env, &mut atoms);
    let regex_bytes = serialize_regex_table(&regex_entries);

    let mut body = Vec::new();
    let mut place = |bytes: &[u8]| -> (u32, u32) {
        let off = ENV_DESC_WORDS * 4 + body.len();
        body.extend_from_slice(bytes);
        (
            u32::try_from(off).unwrap(),
            u32::try_from(bytes.len()).unwrap(),
        )
    };
    // Placement order is the buffer's byte order; the wire order is
    // RegionWords'.
    let (atom_off, atom_len) = place(&atom_bytes);
    let (gbind_off, gbind_len) = place(&gbind_bytes);
    let (layout_off, layout_len) = place(&layout_bytes);
    let (fuse_off, fuse_len) = place(&fuse_bytes);
    let (regex_off, regex_len) = place(&regex_bytes);
    let (strlit_off, strlit_len) = place(&strlit_blob);
    let regions = RegionWords {
        atomPtr: atom_off,
        atomLen: atom_len,
        gbindPtr: gbind_off,
        gbindLen: gbind_len,
        layoutPtr: layout_off,
        layoutLen: layout_len,
        fusePtr: fuse_off,
        fuseLen: fuse_len,
        regexPtr: regex_off,
        regexLen: regex_len,
        gslotsPtr: env.global_slots_base,
        propicPtr: u32::try_from(prop_ic_base).unwrap(),
        propicLen: u32::try_from(prop_ic_size).unwrap(),
        propicGenPtr: env.prop_ic_gen_base,
        layoutCellsPtr: env.this_cells_base,
        callCellsPtr: u32::try_from(call_cells_base).unwrap(),
        callCellsLen: u32::try_from(call_cells_size).unwrap(),
        allocCellsPtr: u32::try_from(alloc_cells_base).unwrap(),
        allocCellsLen: u32::try_from(alloc_cells_size).unwrap(),
        intrinsicCellsPtr: u32::try_from(intrinsic_cells_base).unwrap(),
        intrinsicCellsLen: u32::try_from(intrinsic_cells_size).unwrap(),
        fuseCellsPtr: env.gname_fuse_base,
        megaGetPtr: env.mega_get_base,
        megaSetPtr: env.mega_set_base,
        mathNativesPtr: env.math_natives_base,
        appendCachePtr: env.append_cache_base,
        accessorCachePtr: env.accessor_cache_base,
    };

    let mut header = [0u32; ENV_DESC_WORDS];
    header[0] = ABI_VERSION;
    header[1] = u32::try_from(REGION_COUNT).unwrap();
    header[2] = strlit_off;
    header[3] = strlit_len;
    header[4] = strlit_addr;
    header[ENV_DESC_HEADER_WORDS..].copy_from_slice(&regions.to_words());
    let mut env_desc = Vec::with_capacity(ENV_DESC_WORDS * 4 + body.len());
    for w in header {
        env_desc.extend_from_slice(&w.to_le_bytes());
    }
    env_desc.extend_from_slice(&body);

    let bytes = m
        .to_wasm_bytes()
        .map_err(|e| format!("serialize in-process batch: {e}"))?;
    let blobs = carve_blobs(&bytes, n_imports)?;

    let mut scripts: Vec<(u32, u32)> = Vec::new();
    for (&sid, &f) in &source_id_to_table_func {
        let blob_pos = u32::try_from(f.index() - n_imports).unwrap();
        let predicted = table_base + blob_pos;
        if sid_to_index.get(&sid) != Some(&predicted) {
            return Err(format!(
                "script#{sid}: table index {:?} != predicted {predicted}",
                sid_to_index.get(&sid)
            ));
        }
        scripts.push((sid, blob_pos));
    }
    scripts.sort_unstable();

    Ok(InprocOut {
        blobs,
        extern_table_indices: helper_specs.iter().map(|s| s.table_index).collect(),
        scripts,
        env_desc,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::JSOp;
    use crate::source::SourceObject;

    const HELPER_NAMES: &[&str] = &[
        "night_runtime_callee_night_target",
        "night_runtime_add",
        "night_runtime_concat",
        "night_runtime_call",
        "night_runtime_call_iter",
        "night_runtime_native_dispatch",
        "night_runtime_apply_fwd",
        "night_runtime_construct",
        "night_runtime_get_property",
        "night_runtime_set_property",
        "night_runtime_get_prop_ic_miss",
        "night_runtime_set_prop_ic_miss",
        "night_runtime_get_gname",
        "night_runtime_get_element",
        "night_runtime_set_element",
        "night_runtime_binop",
        "night_runtime_compare",
        "night_runtime_string",
        "night_runtime_get_intrinsic",
        "night_runtime_get_intrinsic_cell",
        "night_runtime_strlit_verify",
        "night_runtime_str_chars_eq",
        "night_runtime_tonumeric",
        "night_runtime_pos",
        "night_runtime_neg",
        "night_runtime_instanceof",
        "night_runtime_del_prop",
        "night_runtime_arguments",
        "night_runtime_arguments_env",
        "night_runtime_box_nonstrict_this",
        "night_runtime_get_mapped_arg",
        "night_runtime_set_mapped_arg",
        "night_runtime_validate_this_layout",
        "night_runtime_in",
        "night_runtime_has_own",
        "night_runtime_to_property_key",
        "night_runtime_mutate_proto",
        "night_runtime_init_home_object",
        "night_runtime_super_base",
        "night_runtime_super_fun",
        "night_runtime_get_prop_super",
        "night_runtime_get_elem_super",
        "night_runtime_set_prop_super",
        "night_runtime_set_elem_super",
        "night_runtime_tostring",
        "night_runtime_pow",
        "night_runtime_check_obj_coercible",
        "night_runtime_check_class_heritage",
        "night_runtime_create_generator",
        "night_runtime_gen_suspend",
        "night_runtime_gen_restore",
        "night_runtime_gen_check_resume",
        "night_runtime_gen_closing",
        "night_runtime_gen_final",
        "night_runtime_async_await",
        "night_runtime_async_resolve",
        "night_runtime_async_reject",
        "night_runtime_can_skip_await",
        "night_runtime_maybe_extract_await",
        "night_runtime_check_is_obj",
        "night_runtime_check_this",
        "night_runtime_check_lexical",
        "night_runtime_throw_set_const",
        "night_runtime_push_lexical_env",
        "night_runtime_push_class_body_env",
        "night_runtime_freshen_lexical_env",
        "night_runtime_recreate_lexical_env",
        "night_runtime_init_glexical",
        "night_runtime_get_name",
        "night_runtime_bind_name",
        "night_runtime_get_bound_name",
        "night_runtime_bind_unqualified_name",
        "night_runtime_bind_var",
        "night_runtime_del_name",
        "night_runtime_push_var_env",
        "night_runtime_enter_with",
        "night_runtime_throw_msg",
        "night_runtime_builtin_object",
        "night_runtime_builtin_object_cell",
        "night_runtime_del_elem",
        "night_runtime_global_this",
        "night_runtime_regexp",
        "night_runtime_init_prop_getset",
        "night_runtime_to_boolean",
        "night_runtime_typeof",
        "night_runtime_typeof_eq",
        "night_runtime_constant_strict_eq",
        "night_runtime_bind_unqualified_gname",
        "night_runtime_set_name",
        "night_runtime_new_object",
        "night_runtime_new_array",
        "night_runtime_init_prop",
        "night_runtime_init_elem",
        "night_runtime_init_elem_getset",
        "night_runtime_check_private_field",
        "night_runtime_new_private_name",
        "night_runtime_env_setup",
        "night_runtime_get_aliased",
        "night_runtime_set_aliased",
        "night_runtime_lambda",
        "night_runtime_exception",
        "night_runtime_throw",
        "night_runtime_throw_with_stack",
        "night_runtime_get_exception_for_finally",
        "night_runtime_global_decl_instantiation",
        "night_runtime_iter",
        "night_runtime_more_iter",
        "night_runtime_end_iter",
        "night_runtime_close_iter_for_exception",
        "night_runtime_symbol",
        "night_runtime_optimize_get_iterator",
        "night_runtime_close_iter",
        "night_runtime_to_async_iter",
        "night_runtime_spread_call",
        "night_runtime_optimize_spread_call",
        "night_runtime_object",
        "night_runtime_post_write_barrier",
        "night_runtime_post_write_barrier_elem",
        "night_runtime_pre_write_barrier",
        "night_runtime_resolve_global_slot",
        "night_runtime_resolve_global_slot_guarded",
        "night_runtime_set_global",
        "night_runtime_binding_written",
        "night_runtime_binding_value",
        "night_runtime_math_unary",
        "night_runtime_math_pow",
        "night_runtime_fmod",
        "night_runtime_create_this",
        "night_runtime_rest",
        "night_runtime_implicit_this",
        "night_runtime_check_this_reinit",
        "night_runtime_check_return",
        "night_runtime_obj_with_proto",
        "night_runtime_fun_with_proto",
        "night_runtime_set_fun_name",
        "night_runtime_no_extra_indexed",
        "night_runtime_gen_is_closing",
        "night_runtime_regex_ci_compare",
    ];

    /// Signature strings for the helpers the toy batch's emitted code
    /// actually calls (validation checks call-site arg types against the
    /// import types); everything else gets a generic placeholder.
    fn sig_of(name: &str) -> &'static str {
        match name {
            "night_runtime_callee_night_target" => "j(j)",
            "night_runtime_add" => "i(iijj)",
            "night_runtime_concat" => "i(iijj)",
            "night_runtime_call" => "i(iiii)",
            "night_runtime_call_iter" => "i(iiii)",
            "night_runtime_native_dispatch" => "i(iiii)",
            "night_runtime_env_setup" => "i(iii)",
            "night_runtime_global_decl_instantiation" => "i(ii)",
            "night_runtime_check_return" => "i(iij)",
            "night_runtime_builtin_object_cell" => "i(iiii)",
            "night_runtime_binding_value" => "j(ii)",
            _ => "i(ii)",
        }
    }

    fn toy_source() -> Source {
        // GetArg 0; One; Add; Return -- the leaf-add vertical slice.
        let code = vec![
            JSOp::GetArg as u16 as u8,
            0,
            0,
            JSOp::One as u16 as u8,
            JSOp::Add as u16 as u8,
            JSOp::Return as u16 as u8,
        ];
        let script = crate::bytecode::Script {
            bytecode: code,
            addr: 0,
            gcthings: Vec::new(),
            resume_offsets: Vec::new(),
            try_notes: Vec::new(),
            scope_notes: Vec::new(),
            body_scope: None,
            nargs: 1,
            is_generator_or_async: false,
            is_class_ctor: false,
            strict: true,
            has_mapped_args: false,
        };
        Source {
            objects: vec![SourceObject::Script(script)],
            global_object: None,
            selfhosted: Vec::new(),
            regex_programs: Vec::new(),
        }
    }

    fn enc_valtype(t: Type) -> wasm_encoder::ValType {
        match t {
            Type::I32 => wasm_encoder::ValType::I32,
            Type::I64 => wasm_encoder::ValType::I64,
            Type::F32 => wasm_encoder::ValType::F32,
            Type::F64 => wasm_encoder::ValType::F64,
            _ => panic!("unexpected type"),
        }
    }

    /// Mirror wasm-jit-runner's `build_module`: extern-function types then
    /// blob types; imports = functions, one memory, one table; blob i is
    /// function (and type) index `n_extern + i`.
    fn reassemble(blobs: &[Vec<u8>], extern_sigs: &[SignatureData]) -> Vec<u8> {
        use wasm_encoder::{
            CodeSection, EntityType, ExportKind as EExportKind, ExportSection, FunctionSection,
            ImportSection, Module as EModule, TypeSection,
        };
        let n_extern = extern_sigs.len() as u32;
        let mut parsed: Vec<(
            Vec<wasm_encoder::ValType>,
            Vec<wasm_encoder::ValType>,
            Vec<u8>,
        )> = Vec::new();
        for b in blobs {
            let mut reader = wasmparser::BinaryReader::new(b, 0);
            assert_eq!(reader.read_u8().unwrap(), 0x60);
            let fty: wasmparser::FuncType = reader.read().unwrap();
            let params: Vec<_> = fty
                .params()
                .iter()
                .map(|p| match p {
                    wasmparser::ValType::I32 => wasm_encoder::ValType::I32,
                    wasmparser::ValType::I64 => wasm_encoder::ValType::I64,
                    wasmparser::ValType::F32 => wasm_encoder::ValType::F32,
                    wasmparser::ValType::F64 => wasm_encoder::ValType::F64,
                    other => panic!("unexpected valtype {other:?}"),
                })
                .collect();
            let results: Vec<_> = fty
                .results()
                .iter()
                .map(|r| match r {
                    wasmparser::ValType::I32 => wasm_encoder::ValType::I32,
                    wasmparser::ValType::I64 => wasm_encoder::ValType::I64,
                    wasmparser::ValType::F32 => wasm_encoder::ValType::F32,
                    wasmparser::ValType::F64 => wasm_encoder::ValType::F64,
                    other => panic!("unexpected valtype {other:?}"),
                })
                .collect();
            let body = b[reader.current_position()..].to_vec();
            assert!(!body.is_empty());
            parsed.push((params, results, body));
        }

        let mut module = EModule::new();
        let mut types = TypeSection::new();
        for sd in extern_sigs {
            types.ty().function(
                sd.params.iter().map(|&t| enc_valtype(t)),
                sd.returns.iter().map(|&t| enc_valtype(t)),
            );
        }
        for (params, results, _) in &parsed {
            types
                .ty()
                .function(params.iter().copied(), results.iter().copied());
        }
        module.section(&types);

        let mut import_sec = ImportSection::new();
        let mut field = 0u32;
        for i in 0..n_extern {
            import_sec.import("e", &format!("i{field}"), EntityType::Function(i));
            field += 1;
        }
        import_sec.import(
            "e",
            &format!("i{field}"),
            EntityType::Memory(wasm_encoder::MemoryType {
                minimum: 0,
                maximum: None,
                memory64: false,
                shared: false,
                page_size_log2: None,
            }),
        );
        field += 1;
        import_sec.import(
            "e",
            &format!("i{field}"),
            EntityType::Table(wasm_encoder::TableType {
                element_type: wasm_encoder::RefType::FUNCREF,
                table64: false,
                minimum: 0,
                maximum: None,
                shared: false,
            }),
        );
        module.section(&import_sec);

        let mut func_sec = FunctionSection::new();
        for i in 0..parsed.len() as u32 {
            func_sec.function(n_extern + i);
        }
        module.section(&func_sec);

        let mut export_sec = ExportSection::new();
        for i in 0..parsed.len() as u32 {
            export_sec.export(&format!("f{i}"), EExportKind::Func, n_extern + i);
        }
        module.section(&export_sec);

        let mut code = CodeSection::new();
        for (_, _, body) in &parsed {
            code.raw(body);
        }
        module.section(&code);
        module.finish()
    }

    #[test]
    fn inproc_batch_builds_and_validates() {
        let source = toy_source();
        let specs: Vec<HelperImportSpec> = HELPER_NAMES
            .iter()
            .enumerate()
            .map(|(i, &name)| HelperImportSpec {
                name: name.to_string(),
                sig: parse_sig_str(sig_of(name)).unwrap(),
                table_index: 100 + i as u32,
            })
            .collect();
        let table_base = 5000u32;
        let mut n_allocs = 0usize;
        let mut bump = 0x1000_0000u32;
        let out = build_inprocess_batch(
            &source,
            SourceObjectId::new(0),
            &Options::default(),
            &specs,
            table_base,
            &mut |size| {
                n_allocs += 1;
                let base = bump;
                bump += size.next_multiple_of(8) + 64;
                Ok(base)
            },
        )
        .expect("build_inprocess_batch");

        assert_eq!(n_allocs, 2, "allocator called exactly twice");
        assert_eq!(out.extern_table_indices.len(), HELPER_NAMES.len());
        assert_eq!(out.extern_table_indices[0], 100);
        // stub + 2 TA poly helpers + stub2 precede the compiled script's
        // widened-ABI body (slot PRE_BODIES); the script's dispatched table
        // entry is its night_abi adapter, appended right after the body.
        assert_eq!(out.scripts, vec![(0, PRE_BODIES + 1)]);
        assert!(out.blobs.len() >= PRE_BODIES as usize + 2);
        // Blob 0 (the direct-call stub) carries the compiled-body ABI functype: the
        // runner's type section places it at index nextern, where the
        // emitted call_indirect immediates point.
        assert_eq!(
            &out.blobs[0][..10],
            &[0x60, 6, 0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0x7E, 0x01, 0x7F][..]
        );

        assert!(out.env_desc.len() >= ENV_DESC_WORDS * 4);
        let word =
            |i: usize| u32::from_le_bytes(out.env_desc[i * 4..i * 4 + 4].try_into().unwrap());
        assert_eq!(word(0), ABI_VERSION);
        assert_eq!(word(1) as usize, REGION_COUNT);
        let region = |name: &str| {
            let i = crate::env_regions::REGION_NAMES
                .iter()
                .position(|&n| n == name)
                .unwrap();
            word(ENV_DESC_HEADER_WORDS + i)
        };
        // gslotsPtr is the fixed-region (first-allocation) base.
        assert_eq!(region("gslotsPtr"), 0x1000_0000);
        // The strlit blob and every Table word (each followed by its Len)
        // stay inside the descriptor buffer.
        assert!((word(2) + word(3)) as usize <= out.env_desc.len());
        for (i, kind) in crate::env_regions::REGION_KINDS.iter().enumerate() {
            if *kind != crate::env_regions::RegionKind::Table {
                continue;
            }
            assert_eq!(
                crate::env_regions::REGION_KINDS[i + 1],
                crate::env_regions::RegionKind::Len
            );
            let (off, len) = (
                word(ENV_DESC_HEADER_WORDS + i),
                word(ENV_DESC_HEADER_WORDS + i + 1),
            );
            assert!((off + len) as usize <= out.env_desc.len());
        }

        let extern_sigs: Vec<SignatureData> = HELPER_NAMES
            .iter()
            .map(|&n| parse_sig_str(sig_of(n)).unwrap())
            .collect();
        let reassembled = reassemble(&out.blobs, &extern_sigs);
        wasmparser::validate(&reassembled).expect("reassembled batch validates");
    }
}
