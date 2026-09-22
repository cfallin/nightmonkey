/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Debug-section stripping. waffle regenerates the `name` section from its
//! own function names on every serialization, so it cannot express dropping
//! it; the strip therefore runs over the serialized bytes, where the
//! top-level section framing is all that has to be understood.

use anyhow::{bail, Result};

fn dropped(name: &str) -> bool {
    name == "name" || name.starts_with(".debug")
}

/// Drop the name and DWARF custom sections from a serialized module.
pub fn strip(wasm: &[u8]) -> Result<Vec<u8>> {
    if !wasm.starts_with(b"\0asm") || wasm.len() < 8 {
        bail!("not a wasm module");
    }
    let mut out = Vec::with_capacity(wasm.len());
    out.extend_from_slice(&wasm[..8]);
    let mut i = 8;
    while i < wasm.len() {
        let start = i;
        let id = wasm[i];
        i += 1;
        let (size, next) = uleb(wasm, i)?;
        i = next + size;
        if i > wasm.len() {
            bail!("section runs past end of module");
        }
        if id == 0 {
            let (len, after) = uleb(wasm, next)?;
            let end = after + len;
            if end > i {
                bail!("custom section name runs past its section");
            }
            let name = std::str::from_utf8(&wasm[after..end])?;
            if dropped(name) {
                continue;
            }
        }
        out.extend_from_slice(&wasm[start..i]);
    }
    Ok(out)
}

fn uleb(b: &[u8], mut i: usize) -> Result<(usize, usize)> {
    let mut v = 0usize;
    let mut shift = 0;
    loop {
        let Some(&byte) = b.get(i) else {
            bail!("truncated LEB128");
        };
        i += 1;
        v |= usize::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Ok((v, i));
        }
        shift += 7;
        if shift >= usize::BITS as usize {
            bail!("oversized LEB128");
        }
    }
}
