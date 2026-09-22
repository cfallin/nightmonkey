/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! wasm-jit-runner: a small WASI (preview 1) CLI runner built on the `wasmtime`
//! crate, with one extra trick: it exposes a host import, `env.wasm_add_funcs`,
//! that lets the running guest add *new wasm functions to itself on the fly* and
//! call them — without a round-trip back out to the runner. This is handy for
//! testing a wasm-targeting compiler "in situ".
//!
//! Usage:
//!
//! ```text
//! wasm-jit-runner <module.wasm> [guest args...]
//! ```

mod addfuncs;
mod cache;
mod modedit;

use anyhow::{Context, Result};
use modedit::ModuleLayout;
use wasmtime::{Config, Engine, Linker, Store};
use wasmtime_wasi::p1::WasiP1Ctx;
use wasmtime_wasi::WasiCtxBuilder;

/// `wasmtime` 45 uses its own `Error`/`Result` types rather than `anyhow`.
/// This adapter converts a `wasmtime::Result` into an `anyhow::Result` so the
/// two compose with `?` and `.context(..)`.
pub trait WtResultExt<T> {
    fn anyhow(self) -> anyhow::Result<T>;
}
impl<T> WtResultExt<T> for wasmtime::Result<T> {
    fn anyhow(self) -> anyhow::Result<T> {
        self.map_err(anyhow::Error::from)
    }
}

/// Per-store host state: the WASI context plus the guest module's layout (how
/// many memories/tables/globals it has), needed by the `wasm_add_funcs` import.
pub struct Host {
    wasi: WasiP1Ctx,
    layout: ModuleLayout,
}

struct Options {
    module_path: String,
    guest_args: Vec<String>,
    /// Host dirs to preopen, as (host, guest) path pairs.
    dirs: Vec<(String, String)>,
    cache_dir: Option<String>,
}

fn usage(exe: &str) -> ! {
    eprintln!(
        "usage: {exe} [--dir HOST[::GUEST]]... [--cache-dir DIR] [--] \
         <module.wasm> [guest args...]"
    );
    std::process::exit(2);
}

fn parse_args() -> Options {
    let mut args = std::env::args();
    let exe = args.next().unwrap_or_else(|| "wasm-jit-runner".into());
    let mut dirs: Vec<(String, String)> = Vec::new();
    let mut cache_dir: Option<String> = None;
    let mut module_path: Option<String> = None;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--dir" => {
                let v = args.next().unwrap_or_else(|| usage(&exe));
                let (host, guest) = match v.split_once("::") {
                    Some((h, g)) => (h.to_string(), g.to_string()),
                    None => (v.clone(), v.clone()),
                };
                dirs.push((host, guest));
            }
            "--cache-dir" => {
                cache_dir = Some(args.next().unwrap_or_else(|| usage(&exe)));
            }
            "--" => {
                module_path = args.next();
                break;
            }
            _ => {
                module_path = Some(a);
                break;
            }
        }
    }
    let Some(module_path) = module_path else {
        usage(&exe);
    };
    if dirs.is_empty() {
        // Default: give the guest the whole host filesystem, so absolute
        // paths (e.g. test files and -f includes) resolve.
        dirs.push(("/".to_string(), "/".to_string()));
    }
    let mut guest_args: Vec<String> = args.collect();
    // Support `runner <module> -- <guest args...>`: a solo `--` right after
    // the module separates runner args from guest args; drop it so the guest
    // (e.g. the JS shell, where `--` ends option parsing) still sees its
    // options.
    if guest_args.first().is_some_and(|a| a == "--") {
        guest_args.remove(0);
    }
    Options {
        module_path,
        guest_args,
        dirs,
        cache_dir,
    }
}

/// Native wasm stack budget: deep guest recursion (e.g. JS self-recursion in
/// AOT-compiled bodies) must hit the guest's own catchable limits before the
/// host stack runs out. The runner work runs on a thread whose stack exceeds
/// this by a margin.
const MAX_WASM_STACK: usize = 256 * 1024 * 1024;

fn main() -> Result<()> {
    std::thread::Builder::new()
        .stack_size(MAX_WASM_STACK + 32 * 1024 * 1024)
        .spawn(run)
        .context("spawning runner thread")?
        .join()
        .map_err(|_| anyhow::anyhow!("runner thread panicked"))?
}

fn run() -> Result<()> {
    let opts = parse_args();
    let module_path = &opts.module_path;

    let mut config = Config::new();
    config.max_wasm_stack(MAX_WASM_STACK);
    config.async_stack_size(MAX_WASM_STACK + 16 * 1024 * 1024);
    let engine = Engine::new(&config)?;

    // Load the guest module and rewrite it so all memories/tables/globals are
    // exported (we need handles to them at runtime).
    let raw =
        std::fs::read(module_path).with_context(|| format!("reading module {module_path}"))?;
    let (edited, layout) = modedit::add_item_exports(&raw)
        .with_context(|| format!("preparing module {module_path}"))?;
    let module = cache::load_module(&engine, &edited, opts.cache_dir.as_deref())
        .context("compiling guest module")?;

    // Set up the linker: WASI preview1 plus our `wasm_add_funcs` import.
    let mut linker: Linker<Host> = Linker::new(&engine);
    wasmtime_wasi::p1::add_to_linker_sync(&mut linker, |h: &mut Host| &mut h.wasi)
        .anyhow()
        .context("adding WASI to linker")?;
    addfuncs::add_to_linker(&mut linker).context("adding wasm_add_funcs to linker")?;

    // Build the WASI context: inherit stdio/env, preopen dirs, pass argv.
    let mut builder = WasiCtxBuilder::new();
    builder.inherit_stdio().inherit_env();
    for (host, guest) in &opts.dirs {
        builder
            .preopened_dir(
                host,
                guest,
                wasmtime_wasi::DirPerms::all(),
                wasmtime_wasi::FilePerms::all(),
            )
            .anyhow()
            .with_context(|| format!("preopening {host} as {guest}"))?;
    }
    builder.arg(module_path);
    for a in &opts.guest_args {
        builder.arg(a);
    }
    let wasi = builder.build_p1();

    let mut store = Store::new(&engine, Host { wasi, layout });

    let instance = linker
        .instantiate(&mut store, &module)
        .anyhow()
        .context("instantiating guest module")?;
    let start = instance
        .get_typed_func::<(), ()>(&mut store, "_start")
        .anyhow()
        .context("guest module has no `_start` (is it a WASI command?)")?;

    match start.call(&mut store, ()) {
        Ok(()) => Ok(()),
        Err(e) => {
            if let Some(exit) = e.downcast_ref::<wasmtime_wasi::I32Exit>() {
                std::process::exit(exit.0);
            }
            Err(anyhow::Error::from(e)).context("guest trapped")
        }
    }
}
