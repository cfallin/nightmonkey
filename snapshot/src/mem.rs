/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Guest-memory access abstraction: the external tool reads a snapshot
//! image; the in-process mode overrides the word reads with raw pointer
//! loads on its own live linear memory.

use anyhow::{bail, Result};
use std::borrow::Cow;

pub trait MemAccess {
    fn read_bytes(&self, addr: u32, len: u32) -> Result<Cow<'_, [u8]>>;

    fn read_u8(&self, addr: u32) -> Result<u8> {
        Ok(self.read_bytes(addr, 1)?[0])
    }
    fn read_u16(&self, addr: u32) -> Result<u16> {
        let b = self.read_bytes(addr, 2)?;
        Ok(u16::from_le_bytes([b[0], b[1]]))
    }
    fn read_u32(&self, addr: u32) -> Result<u32> {
        let b = self.read_bytes(addr, 4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }
    fn read_u64(&self, addr: u32) -> Result<u64> {
        let b = self.read_bytes(addr, 8)?;
        Ok(u64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }
}

/// Memory as a flat byte slice (a snapshot image or a wasmtime memory view).
pub struct SliceMem<'a>(pub &'a [u8]);

impl MemAccess for SliceMem<'_> {
    fn read_bytes(&self, addr: u32, len: u32) -> Result<Cow<'_, [u8]>> {
        let start = addr as usize;
        let Some(end) = start.checked_add(len as usize) else {
            bail!("address overflow at {addr:#x}+{len}");
        };
        if end > self.0.len() {
            bail!("read out of bounds: {addr:#x}+{len} > {:#x}", self.0.len());
        }
        Ok(Cow::Borrowed(&self.0[start..end]))
    }
}
