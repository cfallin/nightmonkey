/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Snapshot memory image: materialize the main linear memory from the
//! module's active data segments, mutate it, and write it back as merged
//! data segments.
//!
//! Adapted from weval's `src/image.rs` (bytecodealliance/weval, Apache-2.0
//! WITH LLVM-exception), whose segment merging is itself adapted from
//! wizer's `snapshot.rs`. Simplified here to the single main heap, serial
//! scanning, and byte-level access only.

use anyhow::{bail, Context, Result};
use std::ops::Range;
use waffle::{Memory, MemorySegment, Module, WASM_PAGE};

const MAX_DATA_SEGMENTS: usize = 10_000;

// Minimum overhead of one active data segment: memory index LEB, i32.const
// opcode + immediate LEB, data length LEB.
const MIN_ACTIVE_SEGMENT_OVERHEAD: usize = 4;

pub struct Image {
    pub memory: Memory,
    pub bytes: Vec<u8>,
}

pub fn build_image(module: &Module) -> Result<Image> {
    let memory = module
        .memories
        .iter()
        .next()
        .context("module has no memory")?;
    let mem = &module.memories[memory];
    let mut bytes = vec![0u8; mem.initial_pages * WASM_PAGE];
    for segment in &mem.segments {
        let end = segment.offset + segment.data.len();
        if end > bytes.len() {
            bail!("data segment out of bounds: {:#x}", end);
        }
        bytes[segment.offset..end].copy_from_slice(&segment.data);
    }
    Ok(Image { memory, bytes })
}

impl Image {
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Grow the image to cover `end`, rounded up to a page multiple; new
    /// bytes are zero.
    pub fn extend_to(&mut self, end: usize) {
        let target = end.next_multiple_of(WASM_PAGE);
        if target > self.bytes.len() {
            self.bytes.resize(target, 0);
        }
    }

    pub fn write_bytes(&mut self, addr: u32, data: &[u8]) -> Result<()> {
        let start = addr as usize;
        let end = start
            .checked_add(data.len())
            .context("image write overflow")?;
        if end > self.bytes.len() {
            bail!("image write out of bounds: {addr:#x}+{}", data.len());
        }
        self.bytes[start..end].copy_from_slice(data);
        Ok(())
    }

    pub fn write_u32(&mut self, addr: u32, value: u32) -> Result<()> {
        self.write_bytes(addr, &value.to_le_bytes())
    }

    pub fn read_u32(&self, addr: u32) -> Result<u32> {
        let start = addr as usize;
        let end = start.checked_add(4).context("image read overflow")?;
        if end > self.bytes.len() {
            bail!("image read out of bounds: {addr:#x}");
        }
        Ok(u32::from_le_bytes(
            self.bytes[start..end].try_into().unwrap(),
        ))
    }
}

/// Find all non-zero regions, merge nearby ones, and return the final data
/// segments (wizer's `snapshot_memories`, serial).
fn snapshot_memory(bytes: &[u8]) -> Vec<MemorySegment> {
    let mut ranges: Vec<Range<usize>> = Vec::new();
    let num_pages = bytes.len() / WASM_PAGE;
    for i in 0..num_pages {
        let page_end = (i + 1) * WASM_PAGE;
        let mut start = i * WASM_PAGE;
        while start < page_end {
            let nonzero = match bytes[start..page_end].iter().position(|b| *b != 0) {
                None => break,
                Some(i) => i,
            };
            start += nonzero;
            let end = bytes[start..page_end]
                .iter()
                .position(|b| *b == 0)
                .map_or(page_end, |zero| start + zero);
            ranges.push(start..end);
            start = end;
        }
    }
    if ranges.is_empty() {
        return Vec::new();
    }

    let mut merged: Vec<Range<usize>> = Vec::with_capacity(ranges.len());
    merged.push(ranges[0].clone());
    for r in &ranges[1..] {
        let last = merged.last_mut().unwrap();
        if r.start - last.end <= MIN_ACTIVE_SEGMENT_OVERHEAD {
            last.end = r.end;
        } else {
            merged.push(r.clone());
        }
    }

    // Engines cap the segment count; merge the smallest gaps until we fit.
    if merged.len() > MAX_DATA_SEGMENTS {
        let excess = merged.len() - MAX_DATA_SEGMENTS;
        let mut gaps: Vec<(usize, usize)> = merged
            .windows(2)
            .enumerate()
            .map(|(i, w)| (w[1].start - w[0].end, i))
            .collect();
        gaps.sort_unstable();
        let mut to_merge: Vec<usize> = gaps[..excess].iter().map(|&(_, i)| i).collect();
        to_merge.sort_unstable_by(|a, b| b.cmp(a));
        for i in to_merge {
            let end = merged[i + 1].end;
            merged[i].end = end;
            merged.remove(i + 1);
        }
    }

    merged
        .into_iter()
        .map(|r| MemorySegment {
            offset: r.start,
            data: bytes[r].to_vec(),
        })
        .collect()
}

/// Replace the memory's data segments with a fresh snapshot of the image and
/// bump its limits to cover it.
pub fn update(module: &mut Module, image: &Image) {
    let segments = snapshot_memory(&image.bytes);
    let mem = &mut module.memories[image.memory];
    mem.segments = segments;
    let image_pages = image.bytes.len() / WASM_PAGE;
    mem.initial_pages = mem.initial_pages.max(image_pages);
    if let Some(max) = mem.maximum_pages {
        if max < mem.initial_pages {
            mem.maximum_pages = Some(mem.initial_pages);
        }
    }
}
