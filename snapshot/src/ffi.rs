/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! C FFI for the in-process compile driver (the wasm JS shell walking its
//! own live heap): `MemAccess` over raw linear-memory pointers, plus an
//! opaque walk handle whose `Source` is handed to `night_inproc_build`.
//! wasm32-only: addresses are u32 linear-memory pointers.

use crate::mem::MemAccess;
use crate::registration::Registration;
use crate::walker::walk;
use anyhow::{bail, Result};
use night_compiler::source::Source;
use rustc_hash::FxHashMap;
use std::borrow::Cow;

/// Reads straight out of the running instance's linear memory. Every
/// address and length reaching it is itself read out of that memory, so a
/// desynced or corrupted image must fail here rather than turn into an
/// out-of-bounds host read: `limit` is the end of linear memory and bounds
/// every access, matching what `SliceMem` gets from its slice length.
struct LiveMem {
    limit: u64,
}

#[cfg(target_arch = "wasm32")]
fn linear_memory_end() -> u64 {
    const WASM_PAGE: u64 = 65536;
    core::arch::wasm32::memory_size(0) as u64 * WASM_PAGE
}

#[cfg(not(target_arch = "wasm32"))]
fn linear_memory_end() -> u64 {
    // The live walk only runs inside the wasm shell; off wasm there is no
    // linear memory to read, so admit nothing.
    0
}

impl MemAccess for LiveMem {
    fn read_bytes(&self, addr: u32, len: u32) -> Result<Cow<'_, [u8]>> {
        if addr == 0 {
            bail!("null read of {len} bytes");
        }
        let end = u64::from(addr) + u64::from(len);
        if end > self.limit {
            bail!(
                "out-of-bounds read: {len} bytes at {addr:#x}, linear memory ends at {:#x}",
                self.limit
            );
        }
        Ok(Cow::Borrowed(unsafe {
            core::slice::from_raw_parts(addr as usize as *const u8, len as usize)
        }))
    }
}

pub struct LiveWalk {
    source: Source,
    root: u32,
    extra_roots: Vec<u32>,
    script_addr: FxHashMap<u32, u32>,
}

/// Walk the live heap from the registration block at `reg_addr` (the address
/// of `js::night::gNightRegistration`), plus `n_extra` extra BaseScript roots
/// (self-hosted builtins joining the batch; their trees must already be in
/// the registration digest). Returns null on failure (message on stderr);
/// free with `night_snapshot_walk_delete`.
#[no_mangle]
pub extern "C" fn night_snapshot_walk_live(
    reg_addr: u32,
    extra_script_addrs: *const u32,
    n_extra: u32,
) -> *mut LiveWalk {
    let extras: &[u32] = if extra_script_addrs.is_null() || n_extra == 0 {
        &[]
    } else {
        unsafe { core::slice::from_raw_parts(extra_script_addrs, n_extra as usize) }
    };
    let mem = LiveMem {
        limit: linear_memory_end(),
    };
    let run = || -> Result<LiveWalk> {
        let mut reg = Registration::read(&mem, reg_addr)?;
        let n_reg = reg.roots.len();
        reg.roots.extend_from_slice(extras);
        let out = walk(&mem, &reg)?;
        Ok(LiveWalk {
            source: out.source,
            root: out.root_ids[0].id(),
            extra_roots: out.root_ids[n_reg..].iter().map(|id| id.id()).collect(),
            script_addr: out.script_addr,
        })
    };
    match run() {
        Ok(w) => Box::into_raw(Box::new(w)),
        Err(e) => {
            eprintln!("night_snapshot_walk_live: {e}");
            core::ptr::null_mut()
        }
    }
}

/// The walked `Source` graph, usable as a `night_source_t*`. Borrowed from
/// the handle; valid until `night_snapshot_walk_delete`.
#[no_mangle]
pub extern "C" fn night_snapshot_walk_source(w: &mut LiveWalk) -> *mut Source {
    &mut w.source
}

#[no_mangle]
pub extern "C" fn night_snapshot_walk_root(w: &LiveWalk) -> u32 {
    w.root
}

/// Source id of extra root `i` (the walker dedups by address, so two extras
/// can share an id), or 0 if `i` is out of range.
#[no_mangle]
pub extern "C" fn night_snapshot_walk_extra_root(w: &LiveWalk, i: u32) -> u32 {
    usize::try_from(i)
        .ok()
        .and_then(|i| w.extra_roots.get(i))
        .copied()
        .unwrap_or(0)
}

/// The BaseScript address of the walked script with the given source id
/// (the nightFuncIndex patch target), or 0 if the id is not a walked script.
#[no_mangle]
pub extern "C" fn night_snapshot_walk_script_addr(w: &LiveWalk, source_id: u32) -> u32 {
    w.script_addr.get(&source_id).copied().unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn night_snapshot_walk_delete(_w: Box<LiveWalk>) {}
