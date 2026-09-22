/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Content-addressed compiled-module (.cwasm) cache.
//!
//! Keyed by sha256 of the (edited) module bytes plus the wasmtime version, so
//! a rebuilt guest or a runner upgrade never sees a stale entry. The cache
//! directory is trusted: `Module::deserialize_file` runs no validation on the
//! precompiled code.

use anyhow::{Context, Result};
use sha2::{Digest, Sha256};
use wasmtime::{Engine, Module};

use crate::WtResultExt;

pub fn load_module(engine: &Engine, bytes: &[u8], cache_dir: Option<&str>) -> Result<Module> {
    let Some(dir) = cache_dir else {
        return Module::new(engine, bytes).anyhow();
    };

    let mut hasher = Sha256::new();
    hasher.update(env!("CARGO_PKG_VERSION").as_bytes());
    // Covers the wasmtime version, target and engine config, so a runner or
    // config change never hits a stale entry.
    {
        use std::hash::{Hash, Hasher};
        let mut h = std::hash::DefaultHasher::new();
        engine.precompile_compatibility_hash().hash(&mut h);
        hasher.update(h.finish().to_le_bytes());
    }
    hasher.update(bytes);
    let key = hex(&hasher.finalize());
    let path = std::path::Path::new(dir).join(format!("{key}.cwasm"));

    if path.exists() {
        // SAFETY: the cache entry was serialized by this same runner version
        // from these same module bytes; the directory is trusted.
        match unsafe { Module::deserialize_file(engine, &path) } {
            Ok(m) => return Ok(m),
            Err(e) => {
                eprintln!("[wasm-jit-runner] ignoring bad cache entry {path:?}: {e}");
            }
        }
    }

    let module = Module::new(engine, bytes).anyhow()?;
    std::fs::create_dir_all(dir).with_context(|| format!("creating cache dir {dir}"))?;
    let serialized = module.serialize().anyhow()?;
    // Write-then-rename so concurrent runners never observe a partial entry.
    let tmp = path.with_extension(format!("tmp.{}", std::process::id()));
    std::fs::write(&tmp, &serialized).with_context(|| format!("writing {tmp:?}"))?;
    std::fs::rename(&tmp, &path).with_context(|| format!("renaming into {path:?}"))?;
    Ok(module)
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
