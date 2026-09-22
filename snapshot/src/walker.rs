/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The JSScript-graph walker over raw guest memory, with non-function
//! objects treated as opaque. Cells get IDs on first sight
//! (address-deduped), and composite cells are processed from a LIFO
//! worklist that visits children in the same order.

use crate::layout::{Field, Layout};
use crate::mem::MemAccess;
use crate::registration::Registration;
use anyhow::{anyhow, bail, Context, Result};
use night_compiler::bytecode::{ScopeNote, Script, TryNote, TryNoteKind};
use night_compiler::ids::Pc;
use night_compiler::source::{
    ObjectData, ObjectKind, Primitive, ScopeData, Source, SourceObject, SourceObjectId,
};
use rustc_hash::FxHashMap;

const SOURCE_OTHER: u32 = 0xffff_ffff;

pub struct WalkOutput {
    pub source: Source,
    pub root_ids: Vec<SourceObjectId>,
    /// Source id of each walked script -> its BaseScript linear-memory
    /// address (the nightFuncIndex_ patch target).
    pub script_addr: FxHashMap<u32, u32>,
    /// Source id of each heap-transcribed object -> its linear-memory
    /// address (the snapshot-stamp patch target).
    pub object_addr: FxHashMap<u32, u32>,
}

struct Walker<'a, M: MemAccess> {
    mem: &'a M,
    lay: &'a Layout,
    reg: &'a Registration,
    source: Source,
    dedup: FxHashMap<u32, u32>,
    worklist: Vec<(u32, u8, u32)>, // (cell addr, trace kind, source id)
    script_addr: FxHashMap<u32, u32>,
    object_addr: FxHashMap<u32, u32>,
}

pub fn walk(mem: &impl MemAccess, reg: &Registration) -> Result<WalkOutput> {
    let mut w = Walker {
        mem,
        lay: &reg.layout,
        reg,
        source: Source {
            objects: vec![],
            global_object: None,
            selfhosted: vec![],
            regex_programs: vec![],
        },
        dedup: FxHashMap::default(),
        worklist: Vec::new(),
        script_addr: FxHashMap::default(),
        object_addr: FxHashMap::default(),
    };
    let mut root_ids = Vec::new();
    for &root in &reg.roots {
        let kind_script = w.lay.get(Field::traceKindScript) as u8;
        let id = w.add(root, kind_script)?;
        w.drain()?;
        root_ids.push(SourceObjectId::new(id));
    }
    // The live global, when the snapshot was taken after the top level ran:
    // its own properties are the heap oracle's entry point.
    if reg.global_object != 0 {
        let kind_object = w.lay.get(Field::traceKindObject) as u8;
        let id = w.add(reg.global_object, kind_object)?;
        w.drain()?;
        if id != SOURCE_OTHER {
            w.source.global_object = Some(SourceObjectId::new(id));
        }
    }
    Ok(WalkOutput {
        source: w.source,
        root_ids,
        script_addr: w.script_addr,
        object_addr: w.object_addr,
    })
}

impl<'a, M: MemAccess> Walker<'a, M> {
    fn push(&mut self, obj: SourceObject) -> u32 {
        self.source.push(obj).id()
    }

    // Assign an id on first sight, push composites onto the worklist.
    // Kinds outside {Object, Script, String, Scope} map to OTHER without a
    // dedup entry.
    fn add(&mut self, addr: u32, kind: u8) -> Result<u32> {
        let lay = self.lay;
        let is = |f: Field| lay.get(f) as u8 == kind;
        if !(is(Field::traceKindObject)
            || is(Field::traceKindScript)
            || is(Field::traceKindString)
            || is(Field::traceKindScope))
        {
            return Ok(SOURCE_OTHER);
        }
        if let Some(&id) = self.dedup.get(&addr) {
            return Ok(id);
        }
        let id = if is(Field::traceKindObject) {
            let id = self.push(SourceObject::Object(ObjectData {
                non_native: false,
                kind: ObjectKind::Other,
                slots_exact: false,
                script: None,
                name: None,
                proto: None,
                builtin_id: None,
                properties: vec![],
                elements: vec![],
            }));
            self.worklist.push((addr, kind, id));
            id
        } else if is(Field::traceKindScript) {
            let id = self.read_script(addr)?;
            self.worklist.push((addr, kind, id));
            self.script_addr.insert(id, addr);
            id
        } else if is(Field::traceKindString) {
            self.read_string(addr)?
        } else {
            let id = self.read_scope_shallow(addr)?;
            self.worklist.push((addr, kind, id));
            id
        };
        self.dedup.insert(addr, id);
        Ok(id)
    }

    fn drain(&mut self) -> Result<()> {
        while let Some((addr, kind, id)) = self.worklist.pop() {
            let lay = self.lay;
            if lay.get(Field::traceKindObject) as u8 == kind {
                self.visit_object(addr, id)?;
            } else if lay.get(Field::traceKindScript) as u8 == kind {
                self.visit_script(addr, id)?;
            } else if lay.get(Field::traceKindScope) as u8 == kind {
                self.visit_scope(addr, id)?;
            }
        }
        Ok(())
    }

    // ---- cell readers -----------------------------------------------------

    fn clasp(&self, obj: u32) -> Result<u32> {
        let shape = self.mem.read_u32(obj + self.lay.get(Field::shapeBase))?;
        // The shape's header word is the BaseShape; its header word is the
        // clasp. (Both offsets are descriptor-carried; they are header
        // pointers today.)
        let base = self.mem.read_u32(shape)?;
        self.mem
            .read_u32(base + self.lay.get(Field::baseShapeClasp))
    }

    fn fun_flags_and_argc(&self, fun: u32) -> Result<u32> {
        // Fixed slot holding a PrivateUint32Value: payload is the low word.
        self.mem
            .read_u32(fun + self.lay.get(Field::functionFlagsAndArgCount))
    }

    /// The heap-oracle entry for `addr`, if the engine transcribed one and
    /// the live cell still has the class it was recorded with (an entry
    /// whose address was freed and reused reads as opaque).
    fn heap_entry(&self, addr: u32, clasp: u32) -> Option<&'a crate::registration::HeapObject> {
        let e = self.reg.heap.get(&addr)?;
        (e.clasp == clasp).then_some(e)
    }

    /// One transcribed property/element value. Object values are followed
    /// only when the oracle has them (native and self-hosted callables are
    /// left opaque); non-linear strings and exotic tags are dropped.
    fn read_value(&mut self, bits: u64) -> Result<u32> {
        let lay = self.lay;
        let tag = (bits >> lay.get(Field::valueTagShift)) as u32;
        let payload = bits as u32;
        let prim = |p: Primitive| SourceObject::Primitive(p);
        let obj = if tag == lay.get(Field::valueTagObject) {
            if !self.reg.heap.contains_key(&payload) {
                return Ok(SOURCE_OTHER);
            }
            let kind_object = lay.get(Field::traceKindObject) as u8;
            return self.add(payload, kind_object);
        } else if tag == lay.get(Field::valueTagString) {
            let flags = self.mem.read_u32(payload + lay.get(Field::stringFlags))?;
            if flags & lay.get(Field::stringLinearBit) == 0 {
                return Ok(SOURCE_OTHER);
            }
            let kind_string = lay.get(Field::traceKindString) as u8;
            return self.add(payload, kind_string);
        } else if tag == lay.get(Field::valueTagInt32) {
            prim(Primitive::Int32(payload as i32))
        } else if tag == lay.get(Field::valueTagUndefined) {
            prim(Primitive::Undefined)
        } else if tag == lay.get(Field::valueTagNull) {
            prim(Primitive::Null)
        } else if tag == lay.get(Field::valueTagBoolean) {
            prim(Primitive::Boolean(payload != 0))
        } else if tag == lay.get(Field::valueTagSymbol) {
            if let Some(&id) = self.dedup.get(&payload) {
                return Ok(id);
            }
            let id = self.push(SourceObject::Symbol);
            self.dedup.insert(payload, id);
            return Ok(id);
        } else if tag < lay.get(Field::valueTagClear) {
            prim(Primitive::Double(f64::from_bits(bits)))
        } else {
            return Ok(SOURCE_OTHER);
        };
        Ok(self.push(obj))
    }

    // Fill an object's transcribed structure (proto, own named data
    // properties, dense elements) from the heap oracle.
    fn visit_heap_entry(&mut self, addr: u32, id: u32, clasp: u32) -> Result<bool> {
        let Some(entry) = self.heap_entry(addr, clasp) else {
            return Ok(false);
        };
        self.source
            .object_mut(SourceObjectId::new(id))
            .as_object_mut()
            .slots_exact = entry.kind & 0x100 != 0;
        self.object_addr.insert(id, addr);
        let proto = entry.proto;
        let props: Vec<(u32, u64)> = entry.props.clone();
        let elems: Vec<(u32, u64)> = entry.elems.clone();
        let kind_object = self.lay.get(Field::traceKindObject) as u8;
        let kind_string = self.lay.get(Field::traceKindString) as u8;
        if proto != 0 && self.reg.heap.contains_key(&proto) {
            let pid = self.add(proto, kind_object)?;
            if pid != SOURCE_OTHER {
                self.source
                    .object_mut(SourceObjectId::new(id))
                    .as_object_mut()
                    .proto = Some(SourceObjectId::new(pid));
            }
        }
        for (atom, bits) in props {
            let nid = self.add(atom, kind_string)?;
            let vid = self.read_value(bits)?;
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_object_mut()
                .properties
                .push((SourceObjectId::new(nid), SourceObjectId::new(vid)));
        }
        for (index, bits) in elems {
            let vid = self.read_value(bits)?;
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_object_mut()
                .elements
                .push((index, SourceObjectId::new(vid)));
        }
        Ok(true)
    }

    fn visit_object(&mut self, addr: u32, id: u32) -> Result<()> {
        let lay = self.lay;
        let clasp = self.clasp(addr)?;
        let is_function = clasp == lay.get(Field::claspFunction)
            || clasp == lay.get(Field::claspFunctionExtended);
        let kind = if is_function {
            ObjectKind::Function
        } else if clasp == lay.get(Field::claspPlain) {
            ObjectKind::Plain
        } else if clasp == lay.get(Field::claspArray) {
            ObjectKind::Array
        } else if let Some(e) = self.heap_entry(addr, clasp) {
            if e.kind & 0xf == 4 {
                // A typed-array view: kind bits 4..7 carry the element
                // kind's 1-based TaKind code.
                ObjectKind::TypedArray(((e.kind >> 4) & 0xf) as u8)
            } else {
                // The global: not Plain-classed, but a property bag all
                // the same.
                ObjectKind::Plain
            }
        } else {
            ObjectKind::Other
        };
        self.source
            .object_mut(SourceObjectId::new(id))
            .as_object_mut()
            .kind = kind;

        if is_function {
            let fa = self.fun_flags_and_argc(addr)?;
            let flags = fa & 0xffff;
            let basescript = lay.get(Field::functionFlagsBaseScript);
            let selfhostlazy = lay.get(Field::functionFlagsSelfHostLazy);
            if flags & selfhostlazy != 0 {
                bail!("function {addr:#x} is self-hosted-lazy (tree not delazified?)");
            }
            // A function the heap oracle reached from outside the registered
            // trees is unwalkable (no digest entry): leave it scriptless.
            let script = self
                .mem
                .read_u32(addr + lay.get(Field::functionJitInfoOrScript))?;
            if flags & basescript != 0 && self.reg.digest.script_gcthing_kinds.contains_key(&script)
            {
                let kind_script = lay.get(Field::traceKindScript) as u8;
                let sid = self.add(script, kind_script)?;
                self.source
                    .object_mut(SourceObjectId::new(id))
                    .as_object_mut()
                    .script = Some(SourceObjectId::new(sid));
            }
            let inferred = lay.get(Field::functionFlagsInferredName);
            let guessed = lay.get(Field::functionFlagsGuessedAtom);
            if flags & (inferred | guessed) == 0 {
                let slot = self.mem.read_u64(addr + lay.get(Field::functionAtom))?;
                let tag = (slot >> lay.get(Field::valueTagShift)) as u32;
                if tag == lay.get(Field::valueTagString) {
                    let atom = slot as u32;
                    let kind_string = lay.get(Field::traceKindString) as u8;
                    let nid = self.add(atom, kind_string)?;
                    self.source
                        .object_mut(SourceObjectId::new(id))
                        .as_object_mut()
                        .name = Some(SourceObjectId::new(nid));
                }
            }
        }

        let transcribed = self.visit_heap_entry(addr, id, clasp)?;
        if !is_function && !transcribed {
            // Objects the oracle does not cover stay opaque (the v1 policy,
            // and what every pre-heap-capture snapshot still gets).
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_object_mut()
                .non_native = true;
        }
        Ok(())
    }

    fn isd(&self, script: u32) -> Result<u32> {
        let lay = self.lay;
        let shared = self
            .mem
            .read_u32(script + lay.get(Field::baseScriptSharedData))?;
        if shared == 0 {
            bail!("script {script:#x} is lazy (no shared data)");
        }
        self.mem.read_u32(shared + lay.get(Field::sisdISD))
    }

    fn read_script(&mut self, addr: u32) -> Result<u32> {
        let lay = self.lay;
        let isd = self.isd(addr)?;
        let code_len = self.mem.read_u32(isd + lay.get(Field::isdCodeLength))?;
        let bytecode = self
            .mem
            .read_bytes(isd + lay.get(Field::isdCode), code_len)?
            .into_owned();

        let fun = self
            .mem
            .read_u32(addr + lay.get(Field::baseScriptFunction))?;
        let nargs = if fun != 0 {
            (self.fun_flags_and_argc(fun)? >> 16) as u16
        } else {
            0
        };
        // FunctionFlags kind field (low 3 bits): 3 = ClassConstructor.
        let is_class_ctor = fun != 0 && (self.fun_flags_and_argc(fun)? & 0x7) == 3;
        let iflags = self
            .mem
            .read_u32(addr + lay.get(Field::baseScriptImmutableFlags))?;
        let is_generator_or_async =
            iflags & (lay.get(Field::isfIsGenerator) | lay.get(Field::isfIsAsync)) != 0;
        let strict = iflags & lay.get(Field::isfStrict) != 0;
        let has_mapped_args = iflags & lay.get(Field::isfNeedsArgsObj) != 0
            && iflags & lay.get(Field::isfHasMappedArgsObj) != 0;

        Ok(self.push(SourceObject::Script(Script {
            bytecode,
            addr,
            gcthings: vec![],
            resume_offsets: vec![],
            try_notes: vec![],
            scope_notes: vec![],
            body_scope: None,
            nargs,
            is_generator_or_async,
            is_class_ctor,
            strict,
            has_mapped_args,
        })))
    }

    // ImmutableScriptData optional arrays: `optArrayOffset_` names the start
    // of the first array; 2-bit end indices in the flags byte (just before
    // the bytecode) select end offsets from a reverse-indexed offset table
    // ending at optArrayOffset_. Index 0 is (implicitly) optArrayOffset_.
    fn isd_optional_spans(&self, isd: u32) -> Result<(u32, u32, u32, u32)> {
        let lay = self.lay;
        let flags = self.mem.read_u8(isd + lay.get(Field::isdCode) - 1)?;
        let resume_end = (flags & 0b11) as i32;
        let scope_end = ((flags >> 2) & 0b11) as i32;
        let try_end = ((flags >> 4) & 0b11) as i32;
        let opt_base = self.mem.read_u32(isd + lay.get(Field::isdOptArrayOffset))?;
        let get = |index: i32| -> Result<u32> {
            if index == 0 {
                return Ok(opt_base);
            }
            self.mem.read_u32(isd + opt_base - 4 * index as u32)
        };
        Ok((opt_base, get(resume_end)?, get(scope_end)?, get(try_end)?))
    }

    fn visit_script(&mut self, addr: u32, id: u32) -> Result<()> {
        let lay = self.lay;
        let isd = self.isd(addr)?;
        let (resume_start, resume_end, scope_notes_end, try_notes_end) =
            self.isd_optional_spans(isd)?;

        // Resume offsets (C++ sets them only when non-empty; setting an
        // empty vec is identical).
        let mut resume = Vec::new();
        let mut off = resume_start;
        while off < resume_end {
            resume.push(Pc::new(self.mem.read_u32(isd + off)?));
            off += 4;
        }
        self.source
            .object_mut(SourceObjectId::new(id))
            .as_script_mut()
            .resume_offsets = resume;

        // GCThings, with trace kinds from the registration digest.
        let psd = self
            .mem
            .read_u32(addr + lay.get(Field::baseScriptPrivateData))?;
        let kinds = self
            .reg
            .digest
            .script_gcthing_kinds
            .get(&addr)
            .ok_or_else(|| anyhow!("script {addr:#x} missing from digest"))?
            .clone();
        let ngcthings = if psd != 0 {
            self.mem
                .read_u32(psd + lay.get(Field::privateScriptDataNGCThings))?
        } else {
            0
        };
        if ngcthings as usize != kinds.len() {
            bail!(
                "script {addr:#x}: digest has {} kinds, cell has {ngcthings}",
                kinds.len()
            );
        }
        let things_base = psd + lay.get(Field::privateScriptDataGCThings);
        let mut thing_addrs = Vec::with_capacity(kinds.len());
        for i in 0..kinds.len() as u32 {
            let word = self.mem.read_u32(things_base + 4 * i)?;
            thing_addrs.push(word & !lay.get(Field::gcCellPtrKindMask));
        }
        for (i, &kind) in kinds.iter().enumerate() {
            let tid = if kind == 0xff {
                SOURCE_OTHER
            } else {
                self.add(thing_addrs[i], kind)?
            };
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_script_mut()
                .gcthings
                .push(SourceObjectId::new(tid));
        }

        // Try notes, then scope notes (each 16 bytes).
        let mut off = scope_notes_end;
        while off < try_notes_end {
            let kind_raw = self.mem.read_u32(isd + off)?;
            let note = TryNote {
                kind: try_note_kind(kind_raw)?,
                stack_depth: self.mem.read_u32(isd + off + 4)?,
                start: Pc::new(self.mem.read_u32(isd + off + 8)?),
                length: self.mem.read_u32(isd + off + 12)?,
            };
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_script_mut()
                .try_notes
                .push(note);
            off += 16;
        }
        let mut off = resume_end;
        while off < scope_notes_end {
            let note = ScopeNote {
                gcthing_index: self.mem.read_u32(isd + off)?,
                start: Pc::new(self.mem.read_u32(isd + off + 4)?),
                length: self.mem.read_u32(isd + off + 8)?,
            };
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_script_mut()
                .scope_notes
                .push(note);
            off += 16;
        }

        // Body scope: gcthings[bodyScopeIndex], a Scope (dedup hit).
        let body_index = self.mem.read_u32(isd + lay.get(Field::isdBodyScopeIndex))?;
        let body_addr = *thing_addrs
            .get(body_index as usize)
            .context("bodyScopeIndex out of range")?;
        let kind_scope = lay.get(Field::traceKindScope) as u8;
        let bid = self.add(body_addr, kind_scope)?;
        self.source
            .object_mut(SourceObjectId::new(id))
            .as_script_mut()
            .body_scope = Some(SourceObjectId::new(bid));
        Ok(())
    }

    fn read_scope_shallow(&mut self, addr: u32) -> Result<u32> {
        let lay = self.lay;
        let kind = self.mem.read_u8(addr + lay.get(Field::scopeKind))?;
        let env_shape = self
            .mem
            .read_u32(addr + lay.get(Field::scopeEnvironmentShape))?;
        let always_env = [
            Field::scopeKindWith,
            Field::scopeKindGlobal,
            Field::scopeKindNonSyntactic,
        ]
        .iter()
        .any(|&f| lay.get(f) as u8 == kind);
        // The template shape's fixed-slot count: `Shape::immutableFlags`
        // (word 1 of the shape, the offset every emitted shape read in
        // `bbv/abi.rs` already bakes in) bits 6..11 (`FIXED_SLOTS_SHIFT` /
        // `FIXED_SLOTS_MASK`). Read at the fixed offset rather than through
        // a new descriptor field: a descriptor change invalidates every
        // recorded fixture and every baseline binary's snapshots.
        let env_nfixed = if env_shape != 0 {
            let flags = self.mem.read_u32(env_shape + 4)?;
            Some((flags >> 6) & 0x1f)
        } else {
            None
        };
        Ok(self.push(SourceObject::Scope(ScopeData {
            kind,
            has_environment: always_env || env_shape != 0,
            enclosing: None,
            bindings: vec![],
            env_slot_values: vec![],
            is_named_lambda: false,
            env_nfixed,
        })))
    }

    fn visit_scope(&mut self, addr: u32, id: u32) -> Result<()> {
        let lay = self.lay;
        let enclosing = self.mem.read_u32(addr + lay.get(Field::scopeEnclosing))?;
        if enclosing != 0 {
            let kind_scope = lay.get(Field::traceKindScope) as u8;
            let eid = self.add(enclosing, kind_scope)?;
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_scope_mut()
                .enclosing = Some(SourceObjectId::new(eid));
        }
        let bindings = self
            .reg
            .digest
            .scope_bindings
            .get(&addr)
            .ok_or_else(|| anyhow!("scope {addr:#x} missing from digest"))?
            .iter()
            .map(|b| (b.name_atom, b.is_var, b.env_slot))
            .collect::<Vec<_>>();
        for (name_atom, is_var, env_slot) in bindings {
            if name_atom == 0 {
                continue;
            }
            let kind_string = lay.get(Field::traceKindString) as u8;
            let nid = self.add(name_atom, kind_string)?;
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_scope_mut()
                .bindings
                .push((SourceObjectId::new(nid), is_var, env_slot));
        }
        // Live environment slot values (the closure-captured module handles),
        // when the snapshot caught an activation of this scope.
        if let Some(slots) = self.reg.env_slots.get(&addr).cloned() {
            for (slot, bits) in slots {
                let vid = self.read_value(bits)?;
                if vid == SOURCE_OTHER {
                    continue;
                }
                self.source
                    .object_mut(SourceObjectId::new(id))
                    .as_scope_mut()
                    .env_slot_values
                    .push((slot, SourceObjectId::new(vid)));
            }
        }
        let kind = self.mem.read_u8(addr + lay.get(Field::scopeKind))?;
        if lay.get(Field::scopeKindNamedLambda) as u8 == kind
            || lay.get(Field::scopeKindStrictNamedLambda) as u8 == kind
        {
            self.source
                .object_mut(SourceObjectId::new(id))
                .as_scope_mut()
                .is_named_lambda = true;
        }
        Ok(())
    }

    fn read_string(&mut self, addr: u32) -> Result<u32> {
        let lay = self.lay;
        let flags = self.mem.read_u32(addr + lay.get(Field::stringFlags))?;
        if flags & lay.get(Field::stringLinearBit) == 0 {
            bail!("string {addr:#x} is not linear");
        }
        let len = self.mem.read_u32(addr + lay.get(Field::stringLength))?;
        let latin1 = flags & lay.get(Field::stringLatin1CharsBit) != 0;
        let inline = flags & lay.get(Field::stringInlineCharsBit) != 0;
        let chars_addr = if inline {
            addr + lay.get(Field::stringInlineStorage)
        } else {
            self.mem
                .read_u32(addr + lay.get(Field::stringNonInlineChars))?
        };
        let chars: Vec<u16> = if latin1 {
            self.mem
                .read_bytes(chars_addr, len)?
                .iter()
                .map(|&b| u16::from(b))
                .collect()
        } else {
            let bytes = self.mem.read_bytes(chars_addr, len * 2)?;
            bytes
                .chunks_exact(2)
                .map(|c| u16::from_le_bytes([c[0], c[1]]))
                .collect()
        };
        Ok(self.push(SourceObject::String(
            night_compiler::ids::JsString::from_chars(chars),
        )))
    }
}

fn try_note_kind(raw: u32) -> Result<TryNoteKind> {
    Ok(match raw {
        0 => TryNoteKind::Catch,
        1 => TryNoteKind::Finally,
        2 => TryNoteKind::ForIn,
        3 => TryNoteKind::Destructuring,
        4 => TryNoteKind::ForOf,
        5 => TryNoteKind::ForOfIterClose,
        6 => TryNoteKind::Loop,
        _ => bail!("invalid TryNoteKind {raw}"),
    })
}
