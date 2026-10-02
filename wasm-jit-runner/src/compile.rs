//! Implementation of the `night_compile` host import: the in-process lane's
//! NightMonkey compiler, run natively in the host.
//!
//! The guest (`runtime/NightInproc.cpp`) registers its root script, records
//! the self-hosted roots and regex programs in the registration block (as
//! the snapshot flow does), seals the addresses, and calls:
//!
//! ```c
//! int32_t night_compile(uint32_t req_ptr, uint32_t req_len, uint32_t resp_ptr);
//! ```
//!
//! The host walks the guest's linear memory from the registration block
//! with the same reader `nightmonkey` uses on a snapshot image, compiles the
//! tree with `build_inprocess_batch`, injects the bodies into the store
//! (the `wasm_add_funcs2` path, without the guest round trip), and writes
//! the environment descriptor and the script map into guest memory. The
//! guest installs the environment and arms the scripts.
//!
//! Request (`req_len` bytes of little-endian u32 words at `req_ptr`):
//!
//! ```text
//! 0 version (REQ_VERSION)   1 registration block address
//! 2 helper table address    3 helper count
//! 4 options (NUL-terminated string address; 0 = none)
//! ```
//!
//! The helper table is the engine's `kNightHelpers`: `{name, funcptr, sig}`
//! entries of three words, `name` and `sig` NUL-terminated strings and
//! `funcptr` the helper's funcref-table index.
//!
//! Response (`RESP_WORDS` words the host writes at `resp_ptr`):
//!
//! ```text
//! 0 env_desc address        1 env_desc length
//! 2 script map address      3 script count
//! 4 blob count              5 table index of blob 0
//! ```
//!
//! The script map is `{BaseScript address, table index}` pairs. Both
//! buffers come from the guest's exported `night_inproc_alloc` (zeroed,
//! 8-aligned, never freed), as do the compiler's region allocations; the
//! guest owns them from then on. The environment tables alias the
//! env_desc buffer, so it must stay live.

use crate::addfuncs::{add_funcs_core, table_size_impl};
use crate::Host;
use anyhow::{bail, ensure, Context, Result};
use night_compiler::source::SourceObjectId;
use night_compiler::wasm::inprocess::{
    build_inprocess_batch, parse_sig_str, HelperImportSpec, InprocOut,
};
use night_compiler::Options;
use night_snapshot::{walk_compile_input, Registration, SliceMem};
use std::sync::mpsc;
use wasmtime::{Caller, Extern, Memory};

const REQ_VERSION: u32 = 1;
const REQ_WORDS: usize = 5;
const RESP_WORDS: usize = 6;

/// The guest's allocator export.
const ALLOC_EXPORT: &str = "night_inproc_alloc";

/// Stack for the compiler's threads: waffle's backend lowers nested blocks
/// recursively, as does MIR's builder over nested bytecode, and a large
/// program overflows a default-sized stack. (In the guest the compiler ran
/// on the shell's 64 MiB stack.)
const COMPILE_STACK: usize = 256 << 20;

fn read_u32(data: &[u8], addr: u32) -> Result<u32> {
    let a = addr as usize;
    let slice = data
        .get(a..a.checked_add(4).context("guest address overflows")?)
        .with_context(|| format!("guest read out of bounds at {addr:#x}"))?;
    Ok(u32::from_le_bytes(slice.try_into().unwrap()))
}

fn read_cstr(data: &[u8], addr: u32) -> Result<String> {
    let tail = data
        .get(addr as usize..)
        .with_context(|| format!("guest string out of bounds at {addr:#x}"))?;
    let len = tail
        .iter()
        .position(|&b| b == 0)
        .with_context(|| format!("unterminated guest string at {addr:#x}"))?;
    Ok(std::str::from_utf8(&tail[..len])
        .with_context(|| format!("guest string at {addr:#x} is not UTF-8"))?
        .to_string())
}

fn guest_memory(caller: &mut Caller<'_, Host>) -> Result<Memory> {
    caller
        .get_export("memory")
        .and_then(Extern::into_memory)
        .context("guest has no exported `memory`")
}

/// One allocation from the guest's `night_inproc_alloc`: zeroed, 8-aligned,
/// never freed. The call may grow memory, so callers re-fetch any view of
/// it afterwards.
fn guest_alloc(caller: &mut Caller<'_, Host>, size: u32) -> Result<u32, String> {
    let f = caller
        .get_export(ALLOC_EXPORT)
        .and_then(Extern::into_func)
        .ok_or_else(|| format!("guest does not export `{ALLOC_EXPORT}`"))?;
    let f = f
        .typed::<u32, u32>(&*caller)
        .map_err(|e| format!("`{ALLOC_EXPORT}` has the wrong type: {e}"))?;
    let addr = f
        .call(&mut *caller, size)
        .map_err(|e| format!("`{ALLOC_EXPORT}` trapped: {e}"))?;
    if addr == 0 || addr % 8 != 0 {
        return Err(format!("`{ALLOC_EXPORT}({size})` returned {addr:#x}"));
    }
    Ok(addr)
}

fn write_bytes(caller: &mut Caller<'_, Host>, addr: u32, bytes: &[u8]) -> Result<()> {
    let memory = guest_memory(caller)?;
    let data = memory.data_mut(&mut *caller);
    let start = addr as usize;
    let dst = start
        .checked_add(bytes.len())
        .and_then(|end| data.get_mut(start..end))
        .with_context(|| format!("guest write out of bounds at {addr:#x}"))?;
    dst.copy_from_slice(bytes);
    Ok(())
}

fn words_to_bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

struct Request {
    reg_addr: u32,
    helpers: Vec<HelperImportSpec>,
    options: Options,
}

fn read_request(data: &[u8], req_ptr: u32, req_len: u32) -> Result<Request> {
    ensure!(
        req_len as usize >= REQ_WORDS * 4,
        "request is {req_len} bytes, expected {}",
        REQ_WORDS * 4
    );
    let word = |i: u32| read_u32(data, req_ptr.wrapping_add(4 * i));
    let version = word(0)?;
    ensure!(
        version == REQ_VERSION,
        "request version {version}, host speaks {REQ_VERSION}"
    );
    let reg_addr = word(1)?;
    let table = word(2)?;
    let n_helpers = word(3)?;
    let options_ptr = word(4)?;
    // Each entry is three words; a count past what memory could hold cannot
    // be honest, so refuse it before it sizes an allocation.
    ensure!(
        (n_helpers as usize) <= data.len() / 12,
        "helper count {n_helpers} exceeds guest memory"
    );
    let mut helpers = Vec::with_capacity(n_helpers as usize);
    for i in 0..n_helpers {
        let entry = table
            .checked_add(i.checked_mul(12).context("helper table overflows")?)
            .context("helper table overflows")?;
        let name = read_cstr(data, read_u32(data, entry)?)?;
        let table_index = read_u32(data, entry + 4)?;
        let sig_str = read_cstr(data, read_u32(data, entry + 8)?)?;
        let sig = parse_sig_str(&sig_str)
            .map_err(|e| anyhow::anyhow!("helper `{name}`: {e}"))?;
        helpers.push(HelperImportSpec {
            name,
            sig,
            table_index,
        });
    }
    let options = if options_ptr == 0 {
        Options::default()
    } else {
        Options::parse_str(&read_cstr(data, options_ptr)?)
            .map_err(|e| anyhow::anyhow!("bad options: {e}"))?
    };
    Ok(Request {
        reg_addr,
        helpers,
        options,
    })
}

/// The compiler's Rayon pool, with stacks sized for it. Its own pool, not
/// the global one: wasmtime's parallel compilation may already have built
/// that with default stacks. `WJR_COMPILE_THREADS` caps its threads.
fn compile_pool() -> Result<&'static rayon::ThreadPool, String> {
    static POOL: std::sync::OnceLock<Result<rayon::ThreadPool, String>> =
        std::sync::OnceLock::new();
    POOL.get_or_init(|| {
        let mut b = rayon::ThreadPoolBuilder::new()
            .thread_name(|i| format!("night-compile-{i}"))
            .stack_size(COMPILE_STACK);
        if let Some(n) = std::env::var("WJR_COMPILE_THREADS")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
        {
            b = b.num_threads(n);
        }
        b.build().map_err(|e| format!("building the compile pool: {e}"))
    })
    .as_ref()
    .map_err(Clone::clone)
}

/// Run `build_inprocess_batch` in the compile pool. Its two region
/// allocations come back to this thread, which owns the store and calls the
/// guest allocator for them.
fn compile(
    caller: &mut Caller<'_, Host>,
    walk: &night_snapshot::WalkOutput,
    req: &Request,
    table_base: u32,
) -> Result<InprocOut, String> {
    let pool = compile_pool()?;
    let (size_tx, size_rx) = mpsc::channel::<u32>();
    let (addr_tx, addr_rx) = mpsc::channel::<Result<u32, String>>();
    let root_id: SourceObjectId = walk.root_ids[0];
    std::thread::scope(|s| {
        // `install` blocks its caller, so a helper thread waits on it while
        // this one serves the allocations.
        let worker = s.spawn(move || {
            pool.install(move || {
                build_inprocess_batch(
                    &walk.source,
                    root_id,
                    &req.options,
                    &req.helpers,
                    table_base,
                    &mut |size: u32| {
                        size_tx
                            .send(size)
                            .map_err(|_| "allocator channel closed".to_string())?;
                        addr_rx
                            .recv()
                            .map_err(|_| "allocator channel closed".to_string())?
                    },
                )
                // `size_tx` drops here, ending the service loop below.
            })
        });
        for size in size_rx {
            if addr_tx.send(guest_alloc(caller, size)).is_err() {
                break;
            }
        }
        // A compiler panic is a bug, never a decline: abort, as the trap did
        // when the compiler ran in the guest. (The panic hook has already
        // printed the message.)
        worker.join().unwrap_or_else(|_| std::process::abort())
    })
}

fn night_compile_impl(
    caller: &mut Caller<'_, Host>,
    req_ptr: u32,
    req_len: u32,
    resp_ptr: u32,
) -> Result<()> {
    let t0 = std::time::Instant::now();
    let stats = std::env::var_os("WJR_COMPILE_STATS").is_some();
    let memory = guest_memory(caller)?;
    let table_base = table_size_impl(caller)?;

    // Request and walk, over one view of guest memory.
    let (req, walk) = {
        let data = memory.data(&*caller);
        let req = read_request(data, req_ptr, req_len)?;
        let mem = SliceMem(data);
        let mut reg = Registration::read(&mem, req.reg_addr).context("reading registration")?;
        let walk = walk_compile_input(&mem, &mut reg).context("walking the live heap")?;
        (req, walk)
    };
    let t_walk = t0.elapsed();
    let strict = req.options.strict_coverage;

    let out = match compile(caller, &walk, &req, table_base) {
        Ok(out) => out,
        Err(e) => {
            // First line only: a waffle validation failure appends the
            // whole function body, which is megabytes.
            let head = e.lines().next().unwrap_or("");
            eprintln!("night: inprocess: {head}");
            if strict {
                // A test lane must not pass by silently interpreting.
                std::process::abort();
            }
            bail!("batch build failed");
        }
    };
    let t_compile = t0.elapsed();

    let base = add_funcs_core(caller, &out.blobs, &out.extern_table_indices)
        .context("injecting the compiled bodies")?;
    ensure!(
        base == u64::from(table_base),
        "blobs landed at table[{base}], predicted {table_base}"
    );

    // Script map: the source ids resolve to BaseScript addresses here,
    // where the walk's address table is.
    let mut script_words = Vec::with_capacity(out.scripts.len() * 2);
    for &(sid, blob) in &out.scripts {
        let Some(&addr) = walk.script_addr.get(&sid) else {
            eprintln!("night: inprocess: script source#{sid} has no heap address");
            continue;
        };
        script_words.push(addr);
        script_words.push(table_base + blob);
    }
    let n_scripts = (script_words.len() / 2) as u32;

    let env_len = u32::try_from(out.env_desc.len()).context("env_desc exceeds 4 GiB")?;
    let env_addr = guest_alloc(caller, env_len).map_err(anyhow::Error::msg)?;
    write_bytes(caller, env_addr, &out.env_desc)?;
    let map_addr =
        guest_alloc(caller, (script_words.len() * 4) as u32).map_err(anyhow::Error::msg)?;
    write_bytes(caller, map_addr, &words_to_bytes(&script_words))?;

    let resp: [u32; RESP_WORDS] = [
        env_addr,
        env_len,
        map_addr,
        n_scripts,
        out.blobs.len() as u32,
        table_base,
    ];
    write_bytes(caller, resp_ptr, &words_to_bytes(&resp))?;
    if stats {
        eprintln!(
            "night: host compile: {} objects, {} blobs; walk {}ms, compile {}ms, total {}ms",
            walk.source.objects.len(),
            out.blobs.len(),
            t_walk.as_millis(),
            (t_compile - t_walk).as_millis(),
            t0.elapsed().as_millis()
        );
    }
    Ok(())
}

/// Register `env.night_compile` on the linker.
pub fn add_to_linker(linker: &mut wasmtime::Linker<Host>) -> Result<()> {
    linker.func_wrap(
        "env",
        "night_compile",
        |mut caller: Caller<'_, Host>, req_ptr: u32, req_len: u32, resp_ptr: u32| -> i32 {
            match night_compile_impl(&mut caller, req_ptr, req_len, resp_ptr) {
                Ok(()) => 0,
                Err(e) => {
                    eprintln!("[wasm-jit-runner] night_compile failed: {e:#}");
                    1
                }
            }
        },
    )?;
    Ok(())
}
