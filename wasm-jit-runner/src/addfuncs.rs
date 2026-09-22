/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Implementation of the `wasm_add_funcs` host import.
//!
//! The guest calls:
//!
//! ```c
//! err_t wasm_add_funcs(uint8_t** bytecode, size_t* lens, int nfuncs, funcptr_t* out);
//! ```
//!
//! Each `bytecode[i]` (of length `lens[i]`) is a self-describing "function blob"
//! (see [`parse_blob`]). The host assembles all `nfuncs` blobs into a single new
//! core-wasm module in which:
//!
//!   * function indices `0..n_extern` are the imported extern (helper)
//!     functions, and function index `n_extern + i` is the i-th supplied blob,
//!     so the new functions can `call` each other and the helpers by index;
//!   * the existing guest module's memories, tables and globals are imported, at
//!     the same indices they have in the guest (so new code can reference them
//!     directly), but the guest's *functions* are deliberately not visible.
//!
//! The new module is instantiated into the same store. Each new function is then
//! appended to table 0 (the guest's funcptr / `__indirect_function_table`) and
//! the resulting table indices ("funcptrs") are written back to `out`.

use crate::modedit::{GLOBAL_PREFIX, MEM_PREFIX, TABLE_PREFIX};
use crate::{Host, WtResultExt};
use anyhow::{bail, Context, Result};
use wasmtime::{Caller, Engine, Extern, Func, Global, Instance, Memory, Module, Ref, Table};

/// A parsed function blob.
struct ParsedFunc {
    params: Vec<wasm_encoder::ValType>,
    results: Vec<wasm_encoder::ValType>,
    /// The function body: a `vec(locals)` followed by the instruction `expr`
    /// (terminated by the `end` opcode), exactly as it appears in a wasm code
    /// section entry (but without the leading byte-size prefix).
    body: Vec<u8>,
}

/// Convert a wasmparser valtype to a wasm-encoder valtype.
fn enc_valtype(t: &wasmparser::ValType) -> Result<wasm_encoder::ValType> {
    use wasm_encoder::reencode::{Reencode, RoundtripReencoder};
    RoundtripReencoder
        .val_type(*t)
        .map_err(|e| anyhow::anyhow!("valtype: {e:?}"))
}

/// Parse a single function blob. Format:
///
/// ```text
/// 0x60                      ; functype tag
/// vec(valtype)  params      ; standard wasm functype encoding
/// vec(valtype)  results
/// <code-body>               ; the rest of the blob: vec(locals) ++ expr
/// ```
///
/// The functype is decoded with wasmparser; the remaining bytes are the wasm
/// code body, which we keep verbatim (wasmtime validates it on compile).
fn parse_blob(bytes: &[u8]) -> Result<ParsedFunc> {
    let mut reader = wasmparser::BinaryReader::new(bytes, 0);
    let tag = reader.read_u8().context("empty function blob")?;
    if tag != 0x60 {
        bail!("function blob must start with functype tag 0x60, got 0x{tag:02x}");
    }
    let func_ty: wasmparser::FuncType = reader.read().context("decoding functype in blob")?;
    let params = func_ty
        .params()
        .iter()
        .map(enc_valtype)
        .collect::<Result<Vec<_>>>()?;
    let results = func_ty
        .results()
        .iter()
        .map(enc_valtype)
        .collect::<Result<Vec<_>>>()?;

    let body = bytes
        .get(reader.current_position()..)
        .filter(|b| !b.is_empty())
        .context("function blob has empty code body")?
        .to_vec();
    Ok(ParsedFunc {
        params,
        results,
        body,
    })
}

// ---------------------------------------------------------------------------
// wasmtime type -> wasm-encoder type conversions
// ---------------------------------------------------------------------------

fn ref_to_enc(r: &wasmtime::RefType) -> Result<wasm_encoder::RefType> {
    use wasm_encoder::{AbstractHeapType, HeapType};
    use wasmtime::HeapType as H;
    let ty = match r.heap_type() {
        H::Func | H::ConcreteFunc(_) | H::NoFunc => AbstractHeapType::Func,
        H::Extern | H::NoExtern => AbstractHeapType::Extern,
        other => bail!("unsupported heap type in import: {other:?}"),
    };
    Ok(wasm_encoder::RefType {
        nullable: r.is_nullable(),
        heap_type: HeapType::Abstract { shared: false, ty },
    })
}

fn val_to_enc(v: &wasmtime::ValType) -> Result<wasm_encoder::ValType> {
    use wasm_encoder::ValType as E;
    use wasmtime::ValType as W;
    Ok(match v {
        W::I32 => E::I32,
        W::I64 => E::I64,
        W::F32 => E::F32,
        W::F64 => E::F64,
        W::V128 => E::V128,
        W::Ref(r) => E::Ref(ref_to_enc(r)?),
    })
}

/// Types of the imports the new module needs, gathered from the live guest
/// instance, in import order (memories, then tables, then globals).
struct ImportTypes {
    mems: Vec<wasm_encoder::MemoryType>,
    tables: Vec<wasm_encoder::TableType>,
    globals: Vec<wasm_encoder::GlobalType>,
}

/// Assemble the new module's bytes from the parsed functions, extern-function
/// types (imported functions occupying indices `0..externs.len()`, so blob
/// `call` immediates can reference them and blob i is function index
/// `externs.len() + i`), and item import types.
fn build_module(
    funcs: &[ParsedFunc],
    externs: &[(Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>)],
    imports: &ImportTypes,
) -> Vec<u8> {
    use wasm_encoder::{
        CodeSection, EntityType, ExportKind, ExportSection, FunctionSection, ImportSection, Module,
        TypeSection,
    };

    let n_extern = externs.len() as u32;
    let mut module = Module::new();

    // Type section: extern-function types first, then one type per supplied
    // function, in order.
    let mut types = TypeSection::new();
    for (params, results) in externs {
        types
            .ty()
            .function(params.iter().copied(), results.iter().copied());
    }
    for f in funcs {
        types
            .ty()
            .function(f.params.iter().copied(), f.results.iter().copied());
    }
    module.section(&types);

    // Import section: functions first (they occupy the low function indices),
    // then memories, tables and globals matching the guest's index spaces.
    // Field names are arbitrary (imports resolve positionally).
    let mut import_sec = ImportSection::new();
    let mut field = 0u32;
    for i in 0..n_extern {
        import_sec.import("e", &format!("i{field}"), EntityType::Function(i));
        field += 1;
    }
    for mt in &imports.mems {
        import_sec.import("e", &format!("i{field}"), EntityType::Memory(*mt));
        field += 1;
    }
    for tt in &imports.tables {
        import_sec.import("e", &format!("i{field}"), EntityType::Table(*tt));
        field += 1;
    }
    for gt in &imports.globals {
        import_sec.import("e", &format!("i{field}"), EntityType::Global(*gt));
        field += 1;
    }
    module.section(&import_sec);

    // Function section: blob i uses type n_extern + i.
    let mut func_sec = FunctionSection::new();
    for i in 0..funcs.len() as u32 {
        func_sec.function(n_extern + i);
    }
    module.section(&func_sec);

    // Export section: export each blob function so the host can grab a handle.
    let mut export_sec = ExportSection::new();
    for i in 0..funcs.len() as u32 {
        export_sec.export(&format!("f{i}"), ExportKind::Func, n_extern + i);
    }
    module.section(&export_sec);

    // Code section. We already have raw bodies, so build the section payload by
    // hand and splice it in as a raw section.
    let mut code = CodeSection::new();
    for f in funcs {
        // `CodeSection::raw` length-prefixes its argument, turning `locals ++
        // expr` into a complete (size-prefixed) code-section entry.
        code.raw(&f.body);
    }
    module.section(&code);

    module.finish()
}

// ---------------------------------------------------------------------------
// Host function
// ---------------------------------------------------------------------------

fn read_u32(data: &[u8], addr: u32) -> Result<u32> {
    let a = addr as usize;
    let slice = data.get(a..a + 4).context("guest pointer out of bounds")?;
    Ok(u32::from_le_bytes(slice.try_into().unwrap()))
}

/// Address of element `i` of a u32 array at `base`. Plain `base + i * 4`
/// wraps in the guest's 32-bit address space, and a wrapped address lands
/// back in bounds, so it would pass every later check while naming the
/// wrong memory.
fn elem_addr(base: u32, i: u32) -> Result<u32> {
    i.checked_mul(4)
        .and_then(|off| base.checked_add(off))
        .context("guest array address overflows")
}

/// Core implementation; returns `Ok(())` on success. Any error is reported to
/// the guest as a non-zero error code (and logged to stderr).
fn add_funcs_impl(
    caller: &mut Caller<'_, Host>,
    bytecode_arr: u32,
    lens_arr: u32,
    nfuncs: i32,
    extern_arr: u32,
    nextern: i32,
    out_ptr: u32,
) -> Result<()> {
    if nfuncs < 0 || nextern < 0 {
        bail!("negative nfuncs/nextern");
    }
    let n = nfuncs as usize;
    let n_extern = nextern as usize;
    if n == 0 {
        return Ok(());
    }

    let layout = caller.data().layout;

    // The guest's main memory (WASI exports it as "memory").
    let memory: Memory = caller
        .get_export("memory")
        .and_then(Extern::into_memory)
        .context("guest has no exported `memory`")?;

    // Read all blob pointers/lengths, the blob bytes, and the extern-function
    // table indices out of guest memory into owned buffers, so we can drop the
    // immutable borrow before mutating store.
    let (blobs, extern_indices): (Vec<Vec<u8>>, Vec<u32>) = {
        let data = memory.data(&caller);
        // Both counts index u32 arrays in guest memory, so a count past
        // that many words in the whole memory cannot be honest; refuse it
        // before it sizes an allocation.
        let max_entries = data.len() / 4;
        if n > max_entries || n_extern > max_entries {
            bail!("nfuncs/nextern exceed guest memory ({n}, {n_extern})");
        }
        let mut blobs = Vec::with_capacity(n);
        for i in 0..n as u32 {
            let ptr = read_u32(data, elem_addr(bytecode_arr, i)?)?;
            let len = read_u32(data, elem_addr(lens_arr, i)?)?;
            let start = ptr as usize;
            let end = start
                .checked_add(len as usize)
                .filter(|&e| e <= data.len())
                .context("blob bytes out of bounds")?;
            blobs.push(data[start..end].to_vec());
        }
        let mut extern_indices = Vec::with_capacity(n_extern);
        for i in 0..n_extern as u32 {
            extern_indices.push(read_u32(data, elem_addr(extern_arr, i)?)?);
        }
        (blobs, extern_indices)
    };

    let funcs: Vec<ParsedFunc> = blobs
        .iter()
        .enumerate()
        .map(|(i, b)| parse_blob(b).with_context(|| format!("parsing function blob {i}")))
        .collect::<Result<_>>()?;

    // Gather handles to the guest's memories, tables and globals (added as
    // synthetic exports during module editing), in import order.
    let mut mem_externs: Vec<Memory> = Vec::new();
    for i in 0..layout.n_mem {
        let m = caller
            .get_export(&format!("{MEM_PREFIX}{i}"))
            .and_then(Extern::into_memory)
            .with_context(|| format!("missing export {MEM_PREFIX}{i}"))?;
        mem_externs.push(m);
    }
    let mut table_externs: Vec<Table> = Vec::new();
    for i in 0..layout.n_table {
        let t = caller
            .get_export(&format!("{TABLE_PREFIX}{i}"))
            .and_then(Extern::into_table)
            .with_context(|| format!("missing export {TABLE_PREFIX}{i}"))?;
        table_externs.push(t);
    }
    let mut global_externs: Vec<Global> = Vec::new();
    for i in 0..layout.n_global {
        let g = caller
            .get_export(&format!("{GLOBAL_PREFIX}{i}"))
            .and_then(Extern::into_global)
            .with_context(|| format!("missing export {GLOBAL_PREFIX}{i}"))?;
        global_externs.push(g);
    }

    // Resolve extern functions from live table-0 entries: each guest-supplied
    // index must hold a funcref; its type becomes the corresponding function
    // import's type (so a type mismatch fails instantiation loudly).
    let mut extern_funcs: Vec<Func> = Vec::with_capacity(n_extern);
    let mut extern_types: Vec<(Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>)> =
        Vec::with_capacity(n_extern);
    if n_extern > 0 {
        let t0 = *table_externs
            .first()
            .context("guest has no table 0 for extern functions")?;
        for (i, &idx) in extern_indices.iter().enumerate() {
            let elem = t0
                .get(&mut *caller, idx as u64)
                .with_context(|| format!("extern {i}: table index {idx} out of bounds"))?;
            let f = match elem {
                Ref::Func(Some(f)) => f,
                _ => bail!("extern {i}: table index {idx} does not hold a function"),
            };
            let ty = f.ty(&*caller);
            let params = ty
                .params()
                .map(|p| val_to_enc(&p))
                .collect::<Result<Vec<_>>>()?;
            let results = ty
                .results()
                .map(|r| val_to_enc(&r))
                .collect::<Result<Vec<_>>>()?;
            extern_funcs.push(f);
            extern_types.push((params, results));
        }
    }

    // Derive the import types from the live items.
    let import_types = ImportTypes {
        mems: mem_externs
            .iter()
            .map(|m| {
                let t = m.ty(&caller);
                // Relax the limits to a supertype so matching always succeeds;
                // preserve the 64-bit/shared identity bits.
                wasm_encoder::MemoryType {
                    minimum: 0,
                    maximum: None,
                    memory64: t.is_64(),
                    shared: t.is_shared(),
                    page_size_log2: None,
                }
            })
            .collect(),
        tables: table_externs
            .iter()
            .map(|t| {
                let ty = t.ty(&caller);
                Ok(wasm_encoder::TableType {
                    element_type: ref_to_enc(ty.element())?,
                    table64: false,
                    minimum: 0,
                    maximum: None,
                    shared: false,
                })
            })
            .collect::<Result<_>>()?,
        globals: global_externs
            .iter()
            .map(|g| {
                let ty = g.ty(&caller);
                Ok(wasm_encoder::GlobalType {
                    val_type: val_to_enc(ty.content())?,
                    mutable: matches!(ty.mutability(), wasmtime::Mutability::Var),
                    shared: false,
                })
            })
            .collect::<Result<_>>()?,
    };

    // Build and compile the new module.
    let wasm = build_module(&funcs, &extern_types, &import_types);
    let engine: Engine = caller.engine().clone();
    let module = Module::new(&engine, &wasm)
        .anyhow()
        .context("compiling dynamically-added module")?;

    // Imports, in the same order the module declares them.
    let mut imports: Vec<Extern> = Vec::new();
    imports.extend(extern_funcs.iter().map(|f| Extern::Func(*f)));
    imports.extend(mem_externs.iter().map(|m| Extern::Memory(*m)));
    imports.extend(table_externs.iter().map(|t| Extern::Table(*t)));
    imports.extend(global_externs.iter().map(|g| Extern::Global(*g)));

    let instance: Instance = Instance::new(&mut *caller, &module, &imports)
        .anyhow()
        .context("instantiating dynamically-added module")?;

    // Collect the new functions.
    let mut new_funcs: Vec<Func> = Vec::with_capacity(n);
    for i in 0..n as u32 {
        let f = instance
            .get_func(&mut *caller, &format!("f{i}"))
            .with_context(|| format!("new module missing export f{i}"))?;
        new_funcs.push(f);
    }

    // Append them to table 0 (the funcptr table) and record their indices.
    let table0 = *table_externs
        .first()
        .context("guest has no table 0 to hold funcptrs")?;
    let base = table0
        .grow(&mut *caller, n as u64, Ref::Func(None))
        .anyhow()
        .context("growing funcptr table (build guest with -Wl,--growable-table)")?;
    for (i, f) in new_funcs.iter().enumerate() {
        table0
            .set(&mut *caller, base + i as u64, Ref::Func(Some(*f)))
            .anyhow()
            .context("setting funcptr table entry")?;
    }

    // Write the resulting funcptrs back to the guest's `out` array.
    {
        let data = memory.data_mut(&mut *caller);
        for i in 0..n {
            let funcptr = (base + i as u64) as u32;
            let addr = elem_addr(out_ptr, i as u32)? as usize;
            let slot = data
                .get_mut(addr..addr + 4)
                .context("out pointer out of bounds")?;
            slot.copy_from_slice(&funcptr.to_le_bytes());
        }
    }

    Ok(())
}

/// The current size of table 0 (the funcptr table). Because added functions
/// are appended contiguously, a guest that queries this before calling
/// `wasm_add_funcs*` can predict the returned indices: blob i lands at
/// `size + i`. This contiguity is an API guarantee.
fn table_size_impl(caller: &mut Caller<'_, Host>) -> Result<u32> {
    let t0 = caller
        .get_export(&format!("{TABLE_PREFIX}0"))
        .and_then(Extern::into_table)
        .context("guest has no table 0")?;
    Ok(t0.size(&*caller) as u32)
}

/// Register `env.wasm_add_funcs`, `env.wasm_add_funcs2` and
/// `env.wasm_table_size` on the linker.
pub fn add_to_linker(linker: &mut wasmtime::Linker<Host>) -> Result<()> {
    linker.func_wrap(
        "env",
        "wasm_add_funcs",
        |mut caller: Caller<'_, Host>,
         bytecode_arr: u32,
         lens_arr: u32,
         nfuncs: i32,
         out_ptr: u32|
         -> i32 {
            match add_funcs_impl(&mut caller, bytecode_arr, lens_arr, nfuncs, 0, 0, out_ptr) {
                Ok(()) => 0,
                Err(e) => {
                    eprintln!("[wasm-jit-runner] wasm_add_funcs failed: {e:?}");
                    1
                }
            }
        },
    )?;
    linker.func_wrap(
        "env",
        "wasm_add_funcs2",
        |mut caller: Caller<'_, Host>,
         bytecode_arr: u32,
         lens_arr: u32,
         nfuncs: i32,
         extern_arr: u32,
         nextern: i32,
         out_ptr: u32|
         -> i32 {
            match add_funcs_impl(
                &mut caller,
                bytecode_arr,
                lens_arr,
                nfuncs,
                extern_arr,
                nextern,
                out_ptr,
            ) {
                Ok(()) => 0,
                Err(e) => {
                    eprintln!("[wasm-jit-runner] wasm_add_funcs2 failed: {e:?}");
                    1
                }
            }
        },
    )?;
    linker.func_wrap(
        "env",
        "wasm_table_size",
        |mut caller: Caller<'_, Host>| -> i32 {
            match table_size_impl(&mut caller) {
                Ok(sz) => sz as i32,
                Err(e) => {
                    eprintln!("[wasm-jit-runner] wasm_table_size failed: {e:?}");
                    -1
                }
            }
        },
    )?;
    Ok(())
}
