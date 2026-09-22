/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

// Stylistic lints the emitter's shape legitimately conflicts with: lowering
// entry points take many arguments, `to_*` converts an operand rather than
// `self`, and rustdoc list formatting is not a goal.
#![allow(
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::wrong_self_convention,
    clippy::large_enum_variant,
    clippy::doc_lazy_continuation,
    clippy::doc_overindented_list_items
)]
//! NightMonkey: an ahead-of-time compiler from SpiderMonkey bytecode to
//! WebAssembly.
//!
//! The compiler takes a snapshot of a JavaScript program -- its scripts plus
//! the object graph they have built by the end of setup -- and emits a Wasm
//! module that runs it, with no bytecode interpreter on the hot path.
//!
//! JavaScript has no static types, so a translation that committed to
//! nothing would be a threaded interpreter in Wasm clothing: every operand
//! boxed, every operator a helper call. NightMonkey instead runs a
//! whole-program *likely-types* analysis and compiles code specialized to
//! what it finds -- unboxed int32 and double values, direct calls, inline
//! property loads at predicted slots.
//!
//! What the analysis produces is a **prediction, never a proof**. Every
//! specialization is emitted behind a runtime guard, and every guard has a
//! generic fallback that is correct for any value. Correctness therefore
//! rests entirely on the guards and the fallbacks; a wrong prediction costs
//! a failed guard and a slower path, never a wrong answer. Nothing in the
//! analysis has to be sound, which is what lets it be aggressive. Scripts
//! the translator cannot handle are simply left interpreted.
//!
//! The pipeline, in order:
//!
//! - [`source`] -- the input object graph, built on the SpiderMonkey side
//!   and handed over through the FFI in [`source::ffi`]. The sole input:
//!   the compiler reads no other channel, and in particular takes no
//!   profiling data.
//! - [`bytecode`] -- the SpiderMonkey bytecode reader ([`disasm`] dumps it).
//! - [`likelier`] -- the likely-types analysis: one incremental fixpoint
//!   over constraints generated once per function, with calling context as
//!   part of edge identity. Its output is [`facts::LikelyFacts`], the whole
//!   contract between analysis and translator.
//! - [`wasm`] -- the translator. `wasm::bbv` is the one codegen path:
//!   workqueue basic-block versioning, which lowers each bytecode op in as
//!   many type-specialized versions as the program actually reaches, so a
//!   failed speculation is an ordinary edge to a differently-typed version
//!   rather than a deoptimization event.
//! - [`opsem`] -- the operator-semantics vocabulary (result types, numeric
//!   ranges, interval arithmetic) that the analysis and the lowering share,
//!   so both reason about `+` in the same words.
//!
//! Output is either an in-process batch of function bodies compiled into a
//! live engine ([`wasm::inprocess`], entered at [`night_inproc_build`]) or a
//! standalone module produced by the snapshot compiler in
//! `js/src/night/nightmonkey`.

pub mod bytecode;
pub mod constants;
pub mod disasm;
pub mod env_regions;
pub mod facts;
pub mod ids;
pub mod likelier;
pub mod opsem;
pub mod options;
pub mod region_shape;
pub mod source;
pub mod view;
pub mod wasm;

pub use options::{Diagnostics, Options};

/// Build an in-process AOT batch for the `Source` graph at `analysis_source`
/// (root `root_id`): compiled function blobs in wasm-jit-runner format, the
/// extern (helper) table-index array, the compiled-script map, and the
/// serialized environment descriptor. `helper_*` describe the engine helpers
/// (parallel arrays of length `n_helpers`): NUL-terminated name,
/// NUL-terminated signature string (see night_compiler.h), and live funcref-table
/// index. `table_base` is the current table size (`wasm_table_size()`);
/// blob `i` is predicted at `table_base + i`. `alloc` is called exactly
/// twice and must return zeroed, 8-aligned, non-null memory (calloc-style;
/// it may be called with size 0). Returns null on failure (message on
/// stderr); free with `night_inproc_delete`.
///
/// # Safety
/// `helper_names`/`helper_sigs` must point to `n_helpers` valid
/// NUL-terminated strings and `helper_funcptrs` to `n_helpers` u32s.
#[no_mangle]
pub unsafe extern "C" fn night_inproc_build(
    analysis_source: &source::Source,
    root_id: u32,
    helper_names: *const *const core::ffi::c_char,
    helper_sigs: *const *const core::ffi::c_char,
    helper_funcptrs: *const u32,
    n_helpers: u32,
    table_base: u32,
    alloc: extern "C" fn(usize) -> u32,
) -> *mut wasm::inprocess::InprocOut {
    let n = usize::try_from(n_helpers).unwrap();
    let mut specs = Vec::with_capacity(n);
    for i in 0..n {
        let name = match core::ffi::CStr::from_ptr(*helper_names.add(i)).to_str() {
            Ok(s) => s.to_string(),
            Err(e) => {
                log::error!("night_inproc_build: helper name {i}: {e}");
                return core::ptr::null_mut();
            }
        };
        let sig_str = match core::ffi::CStr::from_ptr(*helper_sigs.add(i)).to_str() {
            Ok(s) => s,
            Err(e) => {
                log::error!("night_inproc_build: helper sig {i}: {e}");
                return core::ptr::null_mut();
            }
        };
        let sig = match wasm::inprocess::parse_sig_str(sig_str) {
            Ok(s) => s,
            Err(e) => {
                log::error!("night_inproc_build: helper `{name}`: {e}");
                return core::ptr::null_mut();
            }
        };
        specs.push(wasm::inprocess::HelperImportSpec {
            name,
            sig,
            table_index: *helper_funcptrs.add(i),
        });
    }
    let root_id = source::SourceObjectId::new(root_id);
    let opts = Options::default();
    let build = move || {
        wasm::inprocess::build_inprocess_batch(
            analysis_source,
            root_id,
            &opts,
            &specs,
            table_base,
            &mut |size: u32| {
                let p = alloc(usize::try_from(size).unwrap());
                if p == 0 {
                    Err("in-process arena allocation failed".to_string())
                } else {
                    Ok(p)
                }
            },
        )
    };
    // Big-stack discipline: waffle's Wasm backend lowers nested blocks
    // recursively, and a large program overflows the default 8 MB main
    // stack -- a silent sigsegv. On wasm32-wasi there are no threads; run
    // inline on the main stack, which the shell link sizes accordingly
    // (-z stack-size).
    #[cfg(target_family = "wasm")]
    let result = build();
    #[cfg(not(target_family = "wasm"))]
    let result = std::thread::scope(|s| {
        std::thread::Builder::new()
            .name("night_compiler-inproc-build".to_string())
            .stack_size(1 << 30)
            .spawn_scoped(s, build)
            .expect("spawn night_compiler-inproc-build thread")
            .join()
            .expect("night_compiler-inproc-build thread panicked")
    });
    match result {
        Ok(out) => Box::into_raw(Box::new(out)),
        Err(e) => {
            // First line only: a waffle validation failure appends the whole
            // function body, which is megabytes. The C++ side reports only
            // "batch build failed", so without this a failure has no reason
            // attached at all.
            let head = e.lines().next().unwrap_or("");
            crate::diag_line!("night: inprocess: {head}");
            log::error!("night_inproc_build: {e}");
            core::ptr::null_mut()
        }
    }
}

#[no_mangle]
pub extern "C" fn night_inproc_num_blobs(out: &wasm::inprocess::InprocOut) -> u32 {
    u32::try_from(out.blobs.len()).unwrap()
}

#[no_mangle]
pub extern "C" fn night_inproc_blob_ptr(out: &wasm::inprocess::InprocOut, i: u32) -> *const u8 {
    out.blobs[i as usize].as_ptr()
}

#[no_mangle]
pub extern "C" fn night_inproc_blob_len(out: &wasm::inprocess::InprocOut, i: u32) -> u32 {
    u32::try_from(out.blobs[i as usize].len()).unwrap()
}

#[no_mangle]
pub extern "C" fn night_inproc_num_externs(out: &wasm::inprocess::InprocOut) -> u32 {
    u32::try_from(out.extern_table_indices.len()).unwrap()
}

#[no_mangle]
pub extern "C" fn night_inproc_extern_indices(out: &wasm::inprocess::InprocOut) -> *const u32 {
    out.extern_table_indices.as_ptr()
}

#[no_mangle]
pub extern "C" fn night_inproc_num_scripts(out: &wasm::inprocess::InprocOut) -> u32 {
    u32::try_from(out.scripts.len()).unwrap()
}

#[no_mangle]
pub extern "C" fn night_inproc_script_source_id(out: &wasm::inprocess::InprocOut, i: u32) -> u32 {
    out.scripts[i as usize].0
}

#[no_mangle]
pub extern "C" fn night_inproc_script_blob(out: &wasm::inprocess::InprocOut, i: u32) -> u32 {
    out.scripts[i as usize].1
}

#[no_mangle]
pub extern "C" fn night_inproc_env_desc_ptr(out: &wasm::inprocess::InprocOut) -> *const u8 {
    out.env_desc.as_ptr()
}

#[no_mangle]
pub extern "C" fn night_inproc_env_desc_len(out: &wasm::inprocess::InprocOut) -> u32 {
    u32::try_from(out.env_desc.len()).unwrap()
}

#[no_mangle]
pub extern "C" fn night_inproc_delete(_out: Box<wasm::inprocess::InprocOut>) {}
