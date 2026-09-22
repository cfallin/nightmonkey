/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Reading the engine's `NightRegistration` block and its serialized digest.

use crate::layout::Layout;
use crate::mem::MemAccess;
use anyhow::{bail, Result};
use rustc_hash::FxHashMap;

pub const MAX_ROOTS: u32 = 8;

pub const FLAG_TOPLEVEL_EXECUTED_AT_INIT: u32 = 1 << 0;
/// Reserved (never set by current images); kept so the bit is never reused.
pub const FLAG_COMPACTION_DISABLED_RETIRED: u32 = 1 << 1;

pub struct Registration {
    pub addr: u32,
    pub flags: u32,
    pub roots: Vec<u32>,
    pub layout: Layout,
    pub digest: Digest,
    pub compiled: u32,
    /// ABI v2 engine-written extras: self-hosted compilation roots
    /// `(BaseScript address, dotted global path)`.
    pub selfhosted: Vec<(u32, String)>,
    /// ABI v2 engine-written extras: force-compiled regex bytecode programs.
    pub regex_programs: Vec<night_compiler::source::RegexProgramSrc>,
    /// ABI v3 engine-written heap oracle, keyed by object address. Empty
    /// when the snapshot was taken before the top level ran (defer mode).
    pub heap: FxHashMap<u32, HeapObject>,
    /// The live global object's address, 0 when the heap was not captured.
    pub global_object: u32,
    /// ABI v3: per-scope environment slot values read out of live
    /// CallObjects -- the closure-captured module handles the analysis
    /// otherwise cannot see through. Keyed by `js::Scope` address.
    pub env_slots: FxHashMap<u32, Vec<(u32, u64)>>,
}

/// One live object transcribed by `js::NightSnapshotCaptureHeap`.
pub struct HeapObject {
    /// The object's JSClass address, re-checked against the live cell before
    /// the entry is trusted (a freed-and-reused address reads as opaque).
    pub clasp: u32,
    /// 1 = Plain, 2 = Array, 3 = interpreted Function.
    pub kind: u32,
    /// [[Prototype]], 0 for null or a primordial (which the reader models
    /// from `kind` instead).
    pub proto: u32,
    /// Own named data properties in definition order: (atom address, raw
    /// `JS::Value` bits).
    pub props: Vec<(u32, u64)>,
    /// Dense elements: (index, raw `JS::Value` bits).
    pub elems: Vec<(u32, u64)>,
}

// Field offsets within NightRegistration (a plain u32 struct; see
// NightRegistration.h): abiVersion, layoutDescriptor, cx, flags, numRoots,
// roots[8], digest, digestLen, compiled, toolVersion, selfHosted,
// selfHostedLen, regexPrograms, regexProgramsLen, regionTable[REGION_TABLE_WORDS].
const OFF_ABI: u32 = 0;
const OFF_LAYOUT: u32 = 4;
const OFF_FLAGS: u32 = 12;
const OFF_NUM_ROOTS: u32 = 16;
const OFF_ROOTS: u32 = 20;
const OFF_DIGEST: u32 = OFF_ROOTS + 4 * MAX_ROOTS;
const OFF_DIGEST_LEN: u32 = OFF_DIGEST + 4;
pub const OFF_COMPILED: u32 = OFF_DIGEST_LEN + 4;
pub const OFF_TOOL_VERSION: u32 = OFF_COMPILED + 4;
const OFF_SELFHOSTED: u32 = OFF_TOOL_VERSION + 4;
const OFF_SELFHOSTED_LEN: u32 = OFF_SELFHOSTED + 4;
const OFF_REGEX_PROGRAMS: u32 = OFF_SELFHOSTED_LEN + 4;
const OFF_REGEX_PROGRAMS_LEN: u32 = OFF_REGEX_PROGRAMS + 4;
pub const OFF_REGION_TABLE: u32 = OFF_REGEX_PROGRAMS_LEN + 4;
/// One word per `NIGHT_ENV_REGIONS` entry, generated from NightEnv.h.
pub const REGION_TABLE_WORDS: u32 = night_compiler::env_regions::REGION_COUNT as u32;
// Both mirrors are generated from the same headers; a skew here would mean
// one of them was generated against a stale tree.
const _: () = assert!(crate::layout::ABI_VERSION == night_compiler::env_regions::ABI_VERSION);
const OFF_HEAP_OBJECTS: u32 = OFF_REGION_TABLE + 4 * REGION_TABLE_WORDS;
const OFF_HEAP_OBJECTS_LEN: u32 = OFF_HEAP_OBJECTS + 4;
const OFF_GLOBAL_OBJECT: u32 = OFF_HEAP_OBJECTS_LEN + 4;

impl Registration {
    pub fn read(mem: &impl MemAccess, addr: u32) -> Result<Registration> {
        let abi = mem.read_u32(addr + OFF_ABI)?;
        if abi != crate::layout::ABI_VERSION {
            bail!("registration ABI version {abi} (module never registered a root?)");
        }
        let num_roots = mem.read_u32(addr + OFF_NUM_ROOTS)?;
        if num_roots == 0 || num_roots > MAX_ROOTS {
            bail!("registration has {num_roots} roots");
        }
        let mut roots = Vec::new();
        for i in 0..num_roots {
            roots.push(mem.read_u32(addr + OFF_ROOTS + 4 * i)?);
        }
        let layout = Layout::read(mem, mem.read_u32(addr + OFF_LAYOUT)?)?;
        let digest_addr = mem.read_u32(addr + OFF_DIGEST)?;
        let digest_len = mem.read_u32(addr + OFF_DIGEST_LEN)?;
        let digest = Digest::parse(mem, digest_addr, digest_len)?;
        let selfhosted = parse_selfhosted(
            mem,
            mem.read_u32(addr + OFF_SELFHOSTED)?,
            mem.read_u32(addr + OFF_SELFHOSTED_LEN)?,
        )?;
        let regex_programs = parse_regex_programs(
            mem,
            mem.read_u32(addr + OFF_REGEX_PROGRAMS)?,
            mem.read_u32(addr + OFF_REGEX_PROGRAMS_LEN)?,
        )?;
        let (heap, env_slots) = parse_heap(
            mem,
            mem.read_u32(addr + OFF_HEAP_OBJECTS)?,
            mem.read_u32(addr + OFF_HEAP_OBJECTS_LEN)?,
        )?;
        Ok(Registration {
            addr,
            flags: mem.read_u32(addr + OFF_FLAGS)?,
            roots,
            layout,
            digest,
            compiled: mem.read_u32(addr + OFF_COMPILED)?,
            selfhosted,
            regex_programs,
            heap,
            global_object: mem.read_u32(addr + OFF_GLOBAL_OBJECT)?,
            env_slots,
        })
    }
}

struct TableReader<'a> {
    b: &'a [u8],
    pos: usize,
}

impl<'a> TableReader<'a> {
    fn u32(&mut self) -> Result<u32> {
        if self.pos + 4 > self.b.len() {
            bail!("registration extras table truncated at {}", self.pos);
        }
        let v = u32::from_le_bytes(self.b[self.pos..self.pos + 4].try_into().unwrap());
        self.pos += 4;
        Ok(v)
    }

    fn bytes(&mut self, n: usize) -> Result<&'a [u8]> {
        if self.pos + n > self.b.len() {
            bail!("registration extras table truncated at {}", self.pos);
        }
        let s = &self.b[self.pos..self.pos + n];
        self.pos += n;
        while self.pos & 3 != 0 {
            self.pos += 1;
        }
        Ok(s)
    }
}

// Format: u32 count, per entry u32 scriptAddr, u32 nameLen, nameLen UTF-8
// bytes padded to 4 (serialized by js::NightSnapshotCaptureExtras).
fn parse_selfhosted(mem: &impl MemAccess, addr: u32, len: u32) -> Result<Vec<(u32, String)>> {
    if addr == 0 || len == 0 {
        return Ok(Vec::new());
    }
    let bytes = mem.read_bytes(addr, len)?;
    let mut r = TableReader { b: &bytes, pos: 0 };
    let count = r.u32()?;
    let mut out = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let script = r.u32()?;
        let name_len = r.u32()? as usize;
        let name = String::from_utf8(r.bytes(name_len)?.to_vec())
            .map_err(|_| anyhow::anyhow!("selfhosted name is not UTF-8"))?;
        out.push((script, name));
    }
    Ok(out)
}

// Format: u32 count, per entry u32 flags, u32 numRegisters, u32 pairCount,
// u32 patternLen + patternLen x u16 (padded to 4), u32 latin1Len + bytes
// (padded to 4), u32 twobyteLen + bytes (padded to 4).
fn parse_regex_programs(
    mem: &impl MemAccess,
    addr: u32,
    len: u32,
) -> Result<Vec<night_compiler::source::RegexProgramSrc>> {
    if addr == 0 || len == 0 {
        return Ok(Vec::new());
    }
    let bytes = mem.read_bytes(addr, len)?;
    let mut r = TableReader { b: &bytes, pos: 0 };
    let count = r.u32()?;
    let mut out = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let flags = r.u32()?;
        let num_registers = r.u32()?;
        let pair_count = r.u32()?;
        let pattern_len = r.u32()? as usize;
        let pattern: Vec<u16> = r
            .bytes(pattern_len * 2)?
            .chunks_exact(2)
            .map(|c| u16::from_le_bytes([c[0], c[1]]))
            .collect();
        let latin1_len = r.u32()? as usize;
        let latin1_bytecode = r.bytes(latin1_len)?.to_vec();
        let twobyte_len = r.u32()? as usize;
        let twobyte_bytecode = r.bytes(twobyte_len)?.to_vec();
        out.push(night_compiler::source::RegexProgramSrc {
            pattern: night_compiler::ids::JsString::from_chars(pattern),
            flags,
            latin1_bytecode,
            twobyte_bytecode,
            num_registers,
            pair_count,
        });
    }
    Ok(out)
}

// Format: u32 count, per entry u32 objAddr, u32 claspAddr, u32 kind, u32
// protoAddr, u32 numProps + per prop (u32 atomAddr, u32 valueLow, u32
// valueHigh), u32 numElems + per elem (u32 index, u32 valueLow, u32
// valueHigh); then u32 scopeCount, per scope u32 scopeAddr, u32 numSlots +
// per slot (u32 slot, u32 valueLow, u32 valueHigh). Serialized by
// js::NightSnapshotCaptureHeap.
type HeapTables = (FxHashMap<u32, HeapObject>, FxHashMap<u32, Vec<(u32, u64)>>);

fn parse_heap(mem: &impl MemAccess, addr: u32, len: u32) -> Result<HeapTables> {
    if addr == 0 || len == 0 {
        return Ok((FxHashMap::default(), FxHashMap::default()));
    }
    let bytes = mem.read_bytes(addr, len)?;
    let mut r = TableReader { b: &bytes, pos: 0 };
    let count = r.u32()?;
    let mut out = FxHashMap::default();
    let value = |r: &mut TableReader| -> Result<u64> {
        let lo = r.u32()?;
        let hi = r.u32()?;
        Ok(u64::from(lo) | (u64::from(hi) << 32))
    };
    for _ in 0..count {
        let obj = r.u32()?;
        let clasp = r.u32()?;
        let kind = r.u32()?;
        let proto = r.u32()?;
        let nprops = r.u32()?;
        let mut props = Vec::with_capacity(nprops as usize);
        for _ in 0..nprops {
            let atom = r.u32()?;
            props.push((atom, value(&mut r)?));
        }
        let nelems = r.u32()?;
        let mut elems = Vec::with_capacity(nelems as usize);
        for _ in 0..nelems {
            let index = r.u32()?;
            elems.push((index, value(&mut r)?));
        }
        out.insert(
            obj,
            HeapObject {
                clasp,
                kind,
                proto,
                props,
                elems,
            },
        );
    }
    let mut env_slots = FxHashMap::default();
    let nscopes = r.u32()?;
    for _ in 0..nscopes {
        let scope = r.u32()?;
        let n = r.u32()?;
        let mut slots = Vec::with_capacity(n as usize);
        for _ in 0..n {
            let slot = r.u32()?;
            slots.push((slot, value(&mut r)?));
        }
        env_slots.insert(scope, slots);
    }
    Ok((out, env_slots))
}

pub struct DigestBinding {
    pub name_atom: u32,
    pub is_var: bool,
    pub env_slot: Option<u32>,
}

/// Engine-serialized facts keyed by cell address: per-script gcthing trace
/// kinds (0xff = null entry) and per-scope binding lists.
pub struct Digest {
    pub script_gcthing_kinds: FxHashMap<u32, Vec<u8>>,
    pub scope_bindings: FxHashMap<u32, Vec<DigestBinding>>,
}

impl Digest {
    pub fn parse(mem: &impl MemAccess, addr: u32, len: u32) -> Result<Digest> {
        let bytes = mem.read_bytes(addr, len)?;
        let b: &[u8] = &bytes;
        let mut pos = 0usize;
        let u32_at = |pos: &mut usize| -> Result<u32> {
            if *pos + 4 > b.len() {
                bail!("digest truncated at {pos}");
            }
            let v = u32::from_le_bytes(b[*pos..*pos + 4].try_into().unwrap());
            *pos += 4;
            Ok(v)
        };
        let mut script_gcthing_kinds = FxHashMap::default();
        let num_scripts = u32_at(&mut pos)?;
        for _ in 0..num_scripts {
            let script = u32_at(&mut pos)?;
            let n = u32_at(&mut pos)? as usize;
            if pos + n > b.len() {
                bail!("digest truncated in gcthing kinds");
            }
            let kinds = b[pos..pos + n].to_vec();
            pos += n;
            while pos & 3 != 0 {
                pos += 1;
            }
            script_gcthing_kinds.insert(script, kinds);
        }
        let mut scope_bindings = FxHashMap::default();
        let num_scopes = u32_at(&mut pos)?;
        for _ in 0..num_scopes {
            let scope = u32_at(&mut pos)?;
            let n = u32_at(&mut pos)?;
            let mut bindings = Vec::with_capacity(n as usize);
            for _ in 0..n {
                let name_atom = u32_at(&mut pos)?;
                let is_var = u32_at(&mut pos)? != 0;
                let has_slot = u32_at(&mut pos)? != 0;
                let slot = u32_at(&mut pos)?;
                bindings.push(DigestBinding {
                    name_atom,
                    is_var,
                    env_slot: has_slot.then_some(slot),
                });
            }
            scope_bindings.insert(scope, bindings);
        }
        Ok(Digest {
            script_gcthing_kinds,
            scope_bindings,
        })
    }
}
