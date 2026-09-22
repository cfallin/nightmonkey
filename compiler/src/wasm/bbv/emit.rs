/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The low-level wasm emission primitives -- constants, loads/stores,
//! calls, boxing and unboxing, and the deferred-spill diamond helpers.

use super::*;

// --- value construction / memory / call utilities ------------------------

impl<'a> Bbv<'a> {
    /// Left-fold a guard list with `i32.and` (None for an empty list): the
    /// shape every "all of these must hold" check wants, without each site
    /// naming its own intermediates.
    pub(super) fn and_all(&mut self, guards: &[Value]) -> Option<Value> {
        let (&first, rest) = guards.split_first()?;
        Some(rest.iter().fold(first, |acc, &g| {
            self.binop(Operator::I32And, acc, g, Type::I32)
        }))
    }

    pub(super) fn i32_const(&mut self, value: u32) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Const { value },
            Default::default(),
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn boxed_const(&mut self, value: u64) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let ty = self.body.single_type_list(Type::I64);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I64Const { value },
            Default::default(),
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn f64_const(&mut self, value: f64) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let ty = self.body.single_type_list(Type::F64);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::F64Const {
                value: value.to_bits(),
            },
            Default::default(),
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn unop(&mut self, op: Operator, a: Value, result: Type) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.single(a);
        let ty = self.body.single_type_list(result);
        let v = self.body.add_value(ValueDef::Operator(op, args, ty));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn binop(&mut self, op: Operator, a: Value, b: Value, result: Type) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.double(a, b);
        let ty = self.body.single_type_list(result);
        let v = self.body.add_value(ValueDef::Operator(op, args, ty));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn load_i64(&mut self, addr: Value, offset: u32) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::I64);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I64Load {
                memory: MemoryArg {
                    align: 3,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn load_i32(&mut self, addr: Value, offset: u32) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Load {
                memory: MemoryArg {
                    align: 2,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn store_i64(&mut self, addr: Value, offset: u32, value: Value) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.double(addr, value);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I64Store {
                memory: MemoryArg {
                    align: 3,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            Default::default(),
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    /// `memory.copy dst, src, len` within the module's own memory.
    pub(super) fn memory_copy(&mut self, dst: Value, src: Value, len: Value) {
        if self.mode == EmitMode::ContextOnly {
            return;
        }
        let args = self.body.arg_pool.from_iter([dst, src, len].into_iter());
        let v = self.body.add_value(ValueDef::Operator(
            Operator::MemoryCopy {
                dst_mem: self.mem,
                src_mem: self.mem,
            },
            args,
            Default::default(),
        ));
        self.body.append_to_block(self.cur, v);
    }

    pub(super) fn store_i32(&mut self, addr: Value, offset: u32, value: Value) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.double(addr, value);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Store {
                memory: MemoryArg {
                    align: 2,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            Default::default(),
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn load8_u(&mut self, addr: Value, offset: u32) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Load8U {
                memory: MemoryArg {
                    align: 0,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn load16_u(&mut self, addr: Value, offset: u32) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Load16U {
                memory: MemoryArg {
                    align: 1,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn load_f32(&mut self, addr: Value, offset: u32) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::F32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::F32Load {
                memory: MemoryArg {
                    align: 2,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn load_f64(&mut self, addr: Value, offset: u32) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::F64);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::F64Load {
                memory: MemoryArg {
                    align: 3,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn store8(&mut self, addr: Value, offset: u32, value: Value) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.double(addr, value);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Store8 {
                memory: MemoryArg {
                    align: 0,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            Default::default(),
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn store16(&mut self, addr: Value, offset: u32, value: Value) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.double(addr, value);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Store16 {
                memory: MemoryArg {
                    align: 1,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            Default::default(),
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn store_f32(&mut self, addr: Value, offset: u32, value: Value) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.double(addr, value);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::F32Store {
                memory: MemoryArg {
                    align: 2,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            Default::default(),
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn store_f64(&mut self, addr: Value, offset: u32, value: Value) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.double(addr, value);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::F64Store {
                memory: MemoryArg {
                    align: 3,
                    offset,
                    memory: self.mem,
                },
            },
            args,
            Default::default(),
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn canon_nan_f64(&mut self, f: Value) -> Value {
        translate::canon_nan_f64(self, f)
    }

    /// `addr + off`, reusing `addr` when off == 0.
    pub(super) fn add_offset(&mut self, addr: Value, off: u32) -> Value {
        if off == 0 {
            return addr;
        }
        let k = self.i32_const(off);
        self.binop(Operator::I32Add, addr, k, Type::I32)
    }

    pub(super) fn call_i32(&mut self, func: Func, args: &[Value]) -> Value {
        if self.depart_bracket(func) {
            self.emit_depart_tick(census::FRAME_PUSH);
        }
        let v = if self.mode == EmitMode::ContextOnly {
            self.virtual_value()
        } else {
            let arg_list = self.body.arg_pool.from_iter(args.iter().copied());
            let ty = self.body.single_type_list(Type::I32);
            let v = self.body.add_value(ValueDef::Operator(
                Operator::Call {
                    function_index: func,
                },
                arg_list,
                ty,
            ));
            self.body.append_to_block(self.cur, v);
            v
        };
        self.note_call_eff(v, func);
        v
    }

    /// A direct body call through the widened `(err, eff)` ABI: returns
    /// (raw call value -- what placement patches rewrite -- err half, eff
    /// half). The CallGc bookkeeping is identical to `call_i32`: the kills
    /// still run, and a participating site's flag fork restores the saved
    /// facts at its clean arm instead of skipping the kill.
    /// Emit one census tick (`Instrumentation::census`).
    ///
    /// Deliberately does NOT go through `note_call_eff`. A census must not
    /// perturb the thing it measures, and an unlisted helper would be treated
    /// as `Unknown` -- which would step the track to Dirty at every version
    /// entry and make the output a measurement of the instrument. The call is
    /// recorded as a pure read instead: it counts, and touches nothing the
    /// compiler models.
    ///
    /// `id` packs `(sid << 16) | pc`; both halves are truncated, which is
    /// fine for attribution on the benchmark corpus and would need widening
    /// for a bundle with more than 65535 scripts.
    pub(super) fn emit_census(&mut self, kind: u32, sid: ScriptId, pc: Pc) {
        if !self.opts.instrument.census || self.mode != EmitMode::Code {
            return;
        }
        self.emit_census_tick(kind, sid, pc);
    }

    /// Emit one guard-arm census tick (`Instrumentation::guards`).
    ///
    /// Keyed on the EVIDENCE pc, so the record joins directly against
    /// `--dump-clsfact` and the analysis fact tables: the question this
    /// instrument answers is "what did the analysis predict here, and did
    /// the receiver agree", and both halves have to name the same site.
    pub(super) fn emit_guard_census(&mut self, kind: u32, pc: Pc) {
        if !self.opts.instrument.guards || self.mode != EmitMode::Code {
            return;
        }
        // The track this arm's version runs on rides in the kind: +200 for
        // Side, +400 for Dirty. The whole point of the instrument is to say
        // which population of property sites the Dirty share of executed
        // version entries is made of, and that needs the two halves in the
        // same record.
        let bump = match self.cur_track {
            Track::Opt => 0,
            Track::Side => 200,
            Track::Dirty => 400,
        };
        let sid = self.source_id;
        let epc = self.evid_pc(pc);
        self.emit_census_tick(kind + bump, sid, epc);
    }

    /// A track-census (`Instrumentation::census`) tick whose KIND is a
    /// runtime value: the folded keep arm reports 48 (word clean) or 49
    /// (stamps-intact) through one tick.
    pub(super) fn emit_census_dyn(&mut self, kind: Value, sid: ScriptId, pc: Pc) {
        if !self.opts.instrument.census || self.mode != EmitMode::Code {
            return;
        }
        let Some(f) = self.helpers.census else {
            return;
        };
        let before = self.body.values.len();
        let id = (sid.get() << 16) | (pc.get() & 0xffff);
        let i = self.i32_const(id);
        let arg_list = self.body.arg_pool.from_iter([kind, i].into_iter());
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::Call { function_index: f },
            arg_list,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        self.effects.insert(v, Eff::CallPure);
        self.instrument_values += self.body.values.len() - before;
    }

    /// A guard-census tick whose KIND is computed at runtime: the caller
    /// hands a value holding `base + bucket`, so one arm can report *why*
    /// it was taken instead of only that it was. Used by the class-fact
    /// miss arms, where the receiver's own class word says whether the
    /// prediction named the wrong class, the right class without its stamp,
    /// or an object nobody ever stamped.
    pub(super) fn emit_guard_census_dyn(&mut self, kind: Value, pc: Pc) {
        if !self.opts.instrument.guards || self.mode != EmitMode::Code {
            return;
        }
        let Some(f) = self.helpers.census else {
            return;
        };
        let before = self.body.values.len();
        let id = (self.source_id.get() << 16) | (self.evid_pc(pc).get() & 0xffff);
        let i = self.i32_const(id);
        let arg_list = self.body.arg_pool.from_iter([kind, i].into_iter());
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::Call { function_index: f },
            arg_list,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        self.effects.insert(v, Eff::CallPure);
        self.instrument_values += self.body.values.len() - before;
    }

    /// A guard-census tick whose KIND and ID are both runtime values.
    /// Used to key a census on the receiver object instead of on the site.
    pub(super) fn emit_guard_census_dyn_id(&mut self, kind: Value, id: Value) {
        if !self.opts.instrument.guards || self.mode != EmitMode::Code {
            return;
        }
        let Some(f) = self.helpers.census else {
            return;
        };
        let before = self.body.values.len();
        let arg_list = self.body.arg_pool.from_iter([kind, id].into_iter());
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::Call { function_index: f },
            arg_list,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        self.effects.insert(v, Eff::CallPure);
        self.instrument_values += self.body.values.len() - before;
    }

    /// One reliance-census tick (`census::RELY_BASE` family grid): the
    /// fast form being emitted at the current pc rests on facts with this
    /// provenance.
    pub(super) fn emit_rely_census(&mut self, family: u32, prov: Prov) {
        if !self.opts.instrument.guards || self.mode != EmitMode::Code {
            return;
        }
        // The census id has no room for the bits; this static record joins
        // the dynamic counts by (sid, pc) and names the exact tables/tests
        // the site's facts rest on.
        if self.opts.diagnostics.ctxedge {
            crate::diag_line!(
                "night: relysite sid#{} pc {} fam {family} prov {:x} track {:?}",
                self.source_id,
                self.evid_pc(self.cur_pc),
                prov.0,
                self.cur_track,
            );
        }
        self.emit_guard_census(census::RELY_BASE + family * 4 + prov.class(), self.cur_pc);
    }

    /// True when the guard-arm census is on and emitting real code, i.e.
    /// when an instrument-only block is worth building.
    pub(super) fn guard_census_on(&self) -> bool {
        self.opts.instrument.guards && self.mode == EmitMode::Code
    }

    /// Load the low word of the stamp-invalidation epoch through the
    /// startup-published address slot (strlit block tail pad).
    /// The binding-write epoch (the strlit block publishes its address,
    /// like the stamp epoch's): bumped on every path that can change a
    /// global binding's value or retire its cell. Sampled before a call and
    /// compared after it, an unchanged word proves the carried per-binding
    /// value facts (`Ctx::gcells`) still hold.
    pub(super) fn emit_bind_epoch_read(&mut self) -> Value {
        let slot = self
            .i32_const(self.helpers.strlit_slot + crate::region_shape::STRLIT_BIND_EPOCH_ADDR_OFF);
        let addr = self.load_i32(slot, 0);
        self.eff(addr, Eff::Read(HeapKind::EngineTable));
        let v = self.load_i32(addr, 0);
        self.eff(v, Eff::Read(HeapKind::FuseCell));
        v
    }

    /// The pre-call binding-epoch sample a keep site owes its facts: None
    /// when the lineage carries no binding fact (nothing to keep, no load).
    pub(super) fn sample_bind_epoch(&mut self) -> Option<Value> {
        if self.gcells_ctx.is_empty() {
            None
        } else {
            Some(self.emit_bind_epoch_read())
        }
    }

    /// The inline `SetGName` store's bump of the binding-write epoch.
    pub(super) fn emit_bind_epoch_bump(&mut self) {
        let slot = self
            .i32_const(self.helpers.strlit_slot + crate::region_shape::STRLIT_BIND_EPOCH_ADDR_OFF);
        let addr = self.load_i32(slot, 0);
        self.eff(addr, Eff::Read(HeapKind::EngineTable));
        let v = self.load_i32(addr, 0);
        self.eff(v, Eff::Read(HeapKind::FuseCell));
        let one = self.i32_const(1);
        let nv = self.binop(Operator::I32Add, v, one, Type::I32);
        let st = self.store_i32(addr, 0, nv);
        self.tag_store(st, HeapKind::FuseCell);
    }

    pub(super) fn emit_epoch_read(&mut self) -> Value {
        let slot = self
            .i32_const(self.helpers.strlit_slot + crate::region_shape::STRLIT_STAMP_EPOCH_ADDR_OFF);
        let addr = self.load_i32(slot, 0);
        self.eff(addr, Eff::Read(HeapKind::EngineTable));
        // The VALUE read is tagged `FuseCell`, never `EngineTable`: LICM
        // hoists const-addressed EngineTable rows out of loops even across
        // may-GC calls, and a hoisted pre-call epoch sample is stale from
        // the loop's first bump on -- every keep arm in the loop then fails
        // forever.
        let v = self.load_i32(addr, 0);
        self.eff(v, Eff::Read(HeapKind::FuseCell));
        v
    }

    /// Bump the epoch by `delta` (a computed 0/1 word, or a const 1):
    /// emitted on the inline demote arms so a demotion inside compiled
    /// user code reached from a helper is visible to the caller's bridge.
    pub(super) fn emit_epoch_bump(&mut self, delta: Option<Value>) {
        let slot = self
            .i32_const(self.helpers.strlit_slot + crate::region_shape::STRLIT_STAMP_EPOCH_ADDR_OFF);
        let addr = self.load_i32(slot, 0);
        self.eff(addr, Eff::Read(HeapKind::EngineTable));
        let v = self.load_i32(addr, 0);
        self.eff(v, Eff::Read(HeapKind::EngineTable));
        let d = match delta {
            Some(d) => d,
            None => self.i32_const(1),
        };
        let nv = self.binop(Operator::I32Add, v, d, Type::I32);
        let st = self.store_i32(addr, 0, nv);
        self.effects.insert(st, Eff::Write(HeapKind::EngineTable));
    }

    /// True when a call to `func` gets the downstream-census frame bracket:
    /// exactly `note_call_eff`'s non-quiet `CallGc` classification, so every
    /// PUSH is paired with the POP emitted there.
    pub(super) fn depart_bracket(&self, func: Func) -> bool {
        if !self.guard_census_on() {
            return false;
        }
        let meta = self
            .helper_meta
            .get(&func)
            .copied()
            .unwrap_or(HelperMeta::UNLISTED);
        matches!(meta.effect, EffectClass::Alloc | EffectClass::Unknown) && !meta.quiet
    }

    /// One flat (un-bumped) census tick at the current site, for the
    /// FRAME_PUSH/FRAME_POP bracket.
    pub(super) fn emit_depart_tick(&mut self, kind: u32) {
        if !self.guard_census_on() {
            return;
        }
        let sid = self.source_id;
        let epc = self.evid_pc(self.cur_pc);
        self.emit_census_tick(kind, sid, epc);
    }

    fn emit_census_tick(&mut self, kind: u32, sid: ScriptId, pc: Pc) {
        let Some(f) = self.helpers.census else {
            return;
        };
        let before = self.body.values.len();
        let id = (sid.get() << 16) | (pc.get() & 0xffff);
        let k = self.i32_const(kind);
        let i = self.i32_const(id);
        let arg_list = self.body.arg_pool.from_iter([k, i].into_iter());
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::Call { function_index: f },
            arg_list,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        self.effects.insert(v, Eff::CallPure);
        self.instrument_values += self.body.values.len() - before;
    }

    /// A three-i32-result leaf call (`night_call_classify`). Same shape as
    /// `call_abi2`: one `Call` value, three `PickOutput`s off it.
    pub(super) fn call_i32x3(&mut self, func: Func, args: &[Value]) -> (Value, Value, Value) {
        if self.depart_bracket(func) {
            self.emit_depart_tick(census::FRAME_PUSH);
        }
        let (v, a, b, c) = if self.mode == EmitMode::ContextOnly {
            (
                self.virtual_value(),
                self.virtual_value(),
                self.virtual_value(),
                self.virtual_value(),
            )
        } else {
            let arg_list = self.body.arg_pool.from_iter(args.iter().copied());
            let tys = self
                .body
                .type_pool
                .from_iter([Type::I32, Type::I32, Type::I32].into_iter());
            let v = self.body.add_value(ValueDef::Operator(
                Operator::Call {
                    function_index: func,
                },
                arg_list,
                tys,
            ));
            self.body.append_to_block(self.cur, v);
            let mut out = [Value::invalid(); 3];
            for (i, o) in out.iter_mut().enumerate() {
                let p = self
                    .body
                    .add_value(ValueDef::PickOutput(v, i as u32, Type::I32));
                self.body.append_to_block(self.cur, p);
                *o = p;
            }
            (v, out[0], out[1], out[2])
        };
        self.note_call_eff(v, func);
        (a, b, c)
    }

    pub(super) fn call_abi2(&mut self, func: Func, args: &[Value]) -> (Value, Value, Value) {
        if self.depart_bracket(func) {
            self.emit_depart_tick(census::FRAME_PUSH);
        }
        let (v, err, eff) = if self.mode == EmitMode::ContextOnly {
            (
                self.virtual_value(),
                self.virtual_value(),
                self.virtual_value(),
            )
        } else {
            let arg_list = self.body.arg_pool.from_iter(args.iter().copied());
            let tys = self
                .body
                .type_pool
                .from_iter([Type::I32, Type::I32].into_iter());
            let v = self.body.add_value(ValueDef::Operator(
                Operator::Call {
                    function_index: func,
                },
                arg_list,
                tys,
            ));
            self.body.append_to_block(self.cur, v);
            let err = self.body.add_value(ValueDef::PickOutput(v, 0, Type::I32));
            self.body.append_to_block(self.cur, err);
            let eff = self.body.add_value(ValueDef::PickOutput(v, 1, Type::I32));
            self.body.append_to_block(self.cur, eff);
            (v, err, eff)
        };
        self.note_call_eff(v, func);
        (v, err, eff)
    }

    /// `call_indirect` through the widened ABI: a compiled callee's
    /// nightFuncIndex is its adapter's table slot; bodies precede the
    /// contiguous adapter block -- interleaving adapters with bodies
    /// measurably worsens instruction-cache behaviour -- so the body sits at
    /// `funcidx - N` where N is the compiled-script count -- a
    /// placeholder const `wasm/mod.rs` patches once the count is known.
    /// Compiled-to-compiled indirect calls thus skip the adapter hop
    /// entirely and get the eff flag.
    pub(super) fn call_indirect_abi2(
        &mut self,
        args: &[Value],
        funcidx: Value,
    ) -> (Value, Value, Value) {
        self.emit_depart_tick(census::FRAME_PUSH);
        let off = self.i32_const(u32::MAX);
        if self.mode == EmitMode::Code {
            self.body_off_patches.push(off);
        }
        let body_idx = self.binop(Operator::I32Sub, funcidx, off, Type::I32);
        let (v, err, eff) = if self.mode == EmitMode::ContextOnly {
            (
                self.virtual_value(),
                self.virtual_value(),
                self.virtual_value(),
            )
        } else {
            let arg_list = self
                .body
                .arg_pool
                .from_iter(args.iter().copied().chain(std::iter::once(body_idx)));
            let tys = self
                .body
                .type_pool
                .from_iter([Type::I32, Type::I32].into_iter());
            let v = self.body.add_value(ValueDef::Operator(
                Operator::CallIndirect {
                    sig_index: self.helpers.night_abi_sig2,
                    table_index: self.helpers.indirect_table,
                },
                arg_list,
                tys,
            ));
            self.body.append_to_block(self.cur, v);
            let err = self.body.add_value(ValueDef::PickOutput(v, 0, Type::I32));
            self.body.append_to_block(self.cur, err);
            let eff = self.body.add_value(ValueDef::PickOutput(v, 1, Type::I32));
            self.body.append_to_block(self.cur, eff);
            (v, err, eff)
        };
        self.emit_depart_tick(census::FRAME_POP);
        self.emit_guard_census(census::DIRTY_ENTER_IND, self.cur_pc);
        self.effects.insert(v, Eff::CallGc);
        self.post_call = true;
        self.kill_cls_facts();
        self.kill_carriers();
        (v, err, eff)
    }

    /// The effect-flag fork at a participating call site's static-target
    /// arm. The dirty side joins the ordinary merge (today's killed
    /// lineage); the clean side (err == 0 and flags == 0) restores the
    /// Pre-call emitter state -- facts, track, carriers, operand SSA, all
    /// proven intact by the callee's flags word -- pops the call operands,
    /// pushes the result (boxed; the ret-claim ladder stays on the dirty
    /// path for now), and continues at `next_pc` as its own lineage.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_flag_fork(
        &mut self,
        ok: Value,
        flags: Value,
        recv_bit: u32,
        pre: &ArmState,
        need: usize,
        top_off: u32,
        next_pc: Pc,
        merge: Block,
        pre_epoch: Option<Value>,
        pre_bind: Option<Value>,
        set_result: bool,
        summary_keep: bool,
    ) {
        let no_eff = self.unop(Operator::I32Eqz, flags, Type::I32);
        // ONE keep arm: the clean and keep-facts continuations differ only
        // in the OR'd word (zero when the word proved clean), so they share
        // one restore -- half the per-site code the two-arm form paid.
        // Admission: stamps clear in the word, OR the epoch unchanged
        // across the call (the ground truth that admits callees whose word
        // saturated at a helper site). Under a mapped arguments object only
        // the full word==0 proof admits: a callee holding `arguments` can
        // write this frame's formals without touching any stamp.
        // `summary_keep`: the identity-guarded callee's effect summary
        // already proved no carried fact can demote, so the keep arm
        // admits on `ok` alone -- no word test, no epoch compare. This is
        // the admission the runtime proofs cannot give an allocating
        // callee (fresh-object stamping moves the global epoch).
        let intact = if summary_keep {
            None
        } else if self.mapped_args_reachable() {
            Some(no_eff)
        } else {
            let sm = self.i32_const(FLAG_STAMPS);
            let sb = self.binop(Operator::I32And, flags, sm, Type::I32);
            let word_ok = self.unop(Operator::I32Eqz, sb, Type::I32);
            Some(match pre_epoch {
                Some(pre_e) => {
                    let post = self.emit_epoch_read();
                    let same = self.binop(Operator::I32Eq, pre_e, post, Type::I32);
                    self.binop(Operator::I32Or, word_ok, same, Type::I32)
                }
                None => word_ok,
            })
        };
        let keep = match intact {
            Some(i) => self.binop(Operator::I32And, ok, i, Type::I32),
            None => ok,
        };
        let keep_blk = self.body.add_block();
        let dirty_blk = self.body.add_block();
        self.cond_br(keep, keep_blk, dirty_blk);
        self.cur = keep_blk;
        // Census: kind 48 when the word itself was clean, 49 when only the
        // stamps proof admitted, 51 when the summary admitted -- one dyn
        // tick.
        if self.opts.instrument.census && self.mode == EmitMode::Code {
            let kv = if summary_keep {
                self.i32_const(51)
            } else {
                let k48 = self.i32_const(48);
                let k49 = self.i32_const(49);
                self.select(Type::I32, k48, k49, no_eff)
            };
            self.emit_census_dyn(kv, self.root_source_id, next_pc);
        }
        // The runtime arm PROVED stamps intact, so the word's FLAG_STAMPS
        // (a helper-site saturation artifact on this path) is cleared
        // before it propagates outward; a clean word passes through as
        // zero. The summary arm proved only that no CARRIED fact demotes,
        // so the word propagates raw -- outer frames judge their own
        // carried sets against the truthful word.
        let folded_raw = self.fold_callee_flags(flags, recv_bit);
        let folded_s = if summary_keep {
            folded_raw
        } else {
            let nsm = self.i32_const(!FLAG_STAMPS);
            self.binop(Operator::I32And, folded_raw, nsm, Type::I32)
        };
        self.emit_stamp_cont(pre, need, top_off, next_pc, folded_s, pre_bind, set_result);
        self.cur = dirty_blk;
        // Census kind 50: the flag fork's dirty arm ran -- the callee's word
        // said it wrote something, so this lineage really is dirty.
        self.emit_census(50, self.root_source_id, next_pc);
        // Accumulator OR on the DIRTY side only: the clean arm just proved
        // flags == 0, so its OR is an identity (the clean continuation
        // restores the pre-call state, cur_flags included). The callee's
        // word is folded into this frame's perspective first: its
        // MUT_THIS names the callee's `this`, ours only when the receiver
        // provably is our own.
        let saved = self.cur_flags;
        let folded = self.fold_callee_flags(flags, recv_bit);
        // WHY the clean arm could not take, from the folded word: bucket 0
        // (folded clean -- the raw word dirtied, the fold discharged it) is
        // the recoverable class this census exists to expose.
        if self.guard_census_on() {
            let before = self.body.values.len();
            let three = self.i32_const(3);
            let bits = self.binop(Operator::I32And, folded, three, Type::I32);
            let base = self.i32_const(census::FLAG_FORK_WHY);
            let bkind = self.binop(Operator::I32Add, base, bits, Type::I32);
            let errk = self.i32_const(census::FLAG_FORK_WHY + 4);
            let kind = self.select(Type::I32, bkind, errk, ok);
            self.instrument_values += self.body.values.len() - before;
            self.emit_guard_census_dyn(kind, self.cur_pc);
        }
        self.or_flags_word(folded);
        let margs = self.merge_args(ok);
        self.cur_flags = saved;
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: margs,
                },
            },
        );
    }

    /// Terminate the current block into the post-call clean continuation:
    /// restore the saved pre-call emitter state (every fact and carrier
    /// still true -- the arm proved no GC and no heap mutation), pop the
    /// call operands, push the result from its frame slot, and enter
    /// `next_pc` as its own lineage. Emitter state is put back afterwards
    /// so the caller can keep emitting sibling arms.
    /// `may_gc`: the flags word is mutation-only, so a clean word no
    /// longer implies the callee ran no GC (quiet allocs do not
    /// saturate). Facts survive a GC; raw addresses do not -- so the
    /// restore sweeps pointer carriers and reloads every operand that
    /// may hold a GC thing from its (GC-updated) frame slot. The
    /// call-free numeric builtin arms pass false: arm selection proves
    /// no helper and no GC, and their carriers stay live.
    pub(super) fn emit_clean_cont(
        &mut self,
        pre: &ArmState,
        need: usize,
        top_off: u32,
        next_pc: Pc,
        may_gc: bool,
    ) {
        let k_state = self.arm_state();
        self.arm_restore(pre.clone());
        for _ in 0..need {
            self.stack.pop();
        }
        if may_gc {
            self.reload_gc_values();
        }
        let result = self.load_i64(self.vp, top_off);
        self.push_call_result(result, next_pc);
        let target = self.cont(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.arm_restore(k_state);
    }

    /// The keep-facts continuation: like the clean cont's may-GC form --
    /// restore the pre-call facts and track, sweep pointer carriers,
    /// reload operands from their (GC-updated) frame slots -- but the
    /// callee DID write heap, so its folded word is OR'd into the restored
    /// accumulator: this frame keeps its facts, outer consumers still see
    /// the mutation. Sound because everything the restore keeps is either
    /// frame-resident (unaliased locals/args, operand values -- no callee
    /// can write them; aliased slots are re-read and re-checked at every
    /// access) or stamp-guarded (classes, prims, intervals, ranges), and
    /// FLAG_STAMPS clear proves no existing stamp moved.
    pub(super) fn emit_stamp_cont(
        &mut self,
        pre: &ArmState,
        need: usize,
        top_off: u32,
        next_pc: Pc,
        folded: Value,
        pre_bind: Option<Value>,
        set_result: bool,
    ) {
        let k_state = self.arm_state();
        self.arm_restore(pre.clone());
        if set_result {
            // Setter-call continuation: the op's result is the STORED
            // VALUE (the pre-call stack top), not the callee's return.
            // Reload FIRST (the sweep is positional), take the value
            // operand off the restored stack, then pop the call operands
            // -- the value comes back from its GC-updated spill slot with
            // its facts intact.
            self.reload_gc_values();
            let v = self
                .stack
                .last()
                .cloned()
                .expect("setter call carries a value operand");
            for _ in 0..need {
                self.stack.pop();
            }
            self.or_flags_word(folded);
            self.stack.push(v);
        } else {
            for _ in 0..need {
                self.stack.pop();
            }
            self.reload_gc_values();
            self.or_flags_word(folded);
            let result = self.load_i64(self.vp, top_off);
            self.push_call_result(result, next_pc);
        }
        self.gcells_keep(Some(folded), pre_bind, next_pc);
        let target = self.cont(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.arm_restore(k_state);
    }

    /// A call continuation's result: through the site's ret-claim ladder
    /// (`call_types`, exactly as the generic merge types it) so a clean or
    /// keep lineage joins `next_pc` with the same result fact as the merge
    /// path. A bottom-typed result there would box the ret claim for every
    /// lineage at the join, at compile time.
    pub(super) fn push_call_result(&mut self, result: Value, next_pc: Pc) {
        let claim = if self.gen_only {
            None
        } else {
            self.ctx
                .facts
                .call_types
                .get(&Site::new(self.source_id, self.evid_pc(self.cur_pc)))
                .copied()
        };
        match claim {
            Some(c) => self.push_load_typed(result, c, next_pc, Prov::C_CALLRET),
            None => self.push_boxed(result, bottom_ty()),
        }
    }

    /// The post-restore sweep: kill raw-pointer carriers and reload
    /// every restored stack operand that may hold a GC thing from its
    /// spilled frame slot (facts -- cls, masks, ivs, fresh -- stay on
    /// the operand; only the address is re-derived).
    pub(super) fn reload_gc_values(&mut self) {
        self.kill_carriers();
        for i in 0..self.stack.len() {
            if is_non_gc(&self.stack[i].ty) {
                continue;
            }
            let off = self.operand_base + 8 * u32::try_from(i).unwrap();
            let v = self.load_i64(self.vp, off);
            self.stack[i].val = v;
            self.stack[i].repr = Repr::Boxed;
        }
    }

    /// The construct clean fork's arms: `word` is the
    /// construct-local effect word (create_this path delta OR the ctor's
    /// returned word masked of MUT_THIS). word == 0 proves the alloc took
    /// the nursery-bump path, the ctor wrote nothing but its own fresh
    /// `this`, and no may-GC helper ran anywhere -- so the pre-call
    /// state (facts, carriers, track) is restored intact and the
    /// continuation runs as its own lineage; this is what hands the
    /// caller's downstream loop an Opt header, where the construct's track
    /// step would otherwise dirty every path through an allocating loop. The
    /// dirty side joins the ordinary construct merge.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_construct_clean_fork(
        &mut self,
        ok: Value,
        word: Value,
        pre: &ArmState,
        need: usize,
        top_off: u32,
        this_off: u32,
        pc: Pc,
        next_pc: Pc,
        mark_fresh: bool,
        merge: Block,
        margs: Vec<Value>,
        pre_epoch: Option<Value>,
        pre_bind: Option<Value>,
    ) {
        let no_eff = self.unop(Operator::I32Eqz, word, Type::I32);
        let clean = self.binop(Operator::I32And, ok, no_eff, Type::I32);
        let clean_blk = self.body.add_block();
        let dirty_blk = self.body.add_block();
        // Keep-facts arm, exactly as in `emit_flag_fork`: a ctor whose word
        // carries MUT bits but not FLAG_STAMPS rejoins Opt with the caller's
        // facts. The result is NOT marked fresh here -- a ctor that wrote
        // heap may have registered its `this` somewhere, so the fresh
        // classification (which lets later calls drop MUT_THIS) would be
        // unsound; only the word == 0 arm can prove freshness.
        if !self.mapped_args_reachable() {
            let rest_blk = self.body.add_block();
            self.cond_br(clean, clean_blk, rest_blk);
            self.cur = rest_blk;
            let sm = self.i32_const(FLAG_STAMPS);
            let sb = self.binop(Operator::I32And, word, sm, Type::I32);
            let word_ok = self.unop(Operator::I32Eqz, sb, Type::I32);
            let intact = match pre_epoch {
                Some(pre_e) => {
                    let post = self.emit_epoch_read();
                    let same = self.binop(Operator::I32Eq, pre_e, post, Type::I32);
                    self.binop(Operator::I32Or, word_ok, same, Type::I32)
                }
                None => word_ok,
            };
            let keep = self.binop(Operator::I32And, ok, intact, Type::I32);
            let stamp_blk = self.body.add_block();
            self.cond_br(keep, stamp_blk, dirty_blk);
            self.cur = stamp_blk;
            self.emit_guard_census(census::CTOR_FORK_STAMP, pc);
            let k_state = self.arm_state();
            self.arm_restore(pre.clone());
            for _ in 0..need {
                self.stack.pop();
            }
            self.reload_gc_values();
            let nsm = self.i32_const(!FLAG_STAMPS);
            let word_m = self.binop(Operator::I32And, word, nsm, Type::I32);
            self.or_flags_word(word_m);
            let result = self.load_i64(self.vp, top_off);
            let thisv = self.load_i64(self.vp, this_off);
            let is_obj = self.tag_eq(result, TAG_OBJECT as u32);
            let final_v = self.select(Type::I64, result, thisv, is_obj);
            self.push_boxed(final_v, self.def_type(pc, 0));
            self.gcells_keep(Some(word), pre_bind, next_pc);
            let target = self.cont(next_pc);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.arm_restore(k_state);
        } else {
            self.cond_br(clean, clean_blk, dirty_blk);
        }
        self.cur = dirty_blk;
        // Construct-fork arms, so "armed" and "taken clean" are separate
        // numbers: arming the fork at more sites is worth nothing if the
        // ctor's word is never zero there.
        self.emit_guard_census(census::CTOR_FORK_DIRTY, pc);
        if self.guard_census_on() {
            let before = self.body.values.len();
            let three = self.i32_const(3);
            let bits = self.binop(Operator::I32And, word, three, Type::I32);
            let base = self.i32_const(census::CTOR_FORK_WHY);
            let kind = self.binop(Operator::I32Add, base, bits, Type::I32);
            self.instrument_values += self.body.values.len() - before;
            self.emit_guard_census_dyn(kind, pc);
        }
        self.body.set_terminator(
            self.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: merge,
                    args: margs,
                },
            },
        );
        self.cur = clean_blk;
        self.emit_guard_census(census::CTOR_FORK_CLEAN, pc);
        let k_state = self.arm_state();
        self.arm_restore(pre.clone());
        for _ in 0..need {
            self.stack.pop();
        }
        // word == 0 does not imply no GC (the quiet bump/ctor
        // path cannot GC, but a quiet alloc inside the ctor can) --
        // sweep carriers and re-derive GC-thing addresses; facts stay.
        self.reload_gc_values();
        // The this-substitute, exactly as the merge does it.
        let result = self.load_i64(self.vp, top_off);
        let thisv = self.load_i64(self.vp, this_off);
        let is_obj = self.tag_eq(result, TAG_OBJECT as u32);
        let final_v = self.select(Type::I64, result, thisv, is_obj);
        self.push_boxed(final_v, self.def_type(pc, 0));
        if mark_fresh {
            if let Some(o) = self.stack.last_mut() {
                o.fresh = true;
            }
        }
        let target = self.cont(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.arm_restore(k_state);
    }

    /// Success exit of a call-free numeric builtin arm: enter the clean
    /// continuation when the site saved pre-call state, else join the
    /// generic merge as before.
    pub(super) fn builtin_success_exit(
        &mut self,
        pre: &Option<ArmState>,
        need: usize,
        top_off: u32,
        next_pc: Option<Pc>,
        merge: Block,
    ) {
        if let Some(pre) = pre {
            let next = next_pc.expect("builtin clean site implies next_pc");
            self.emit_clean_cont(pre, need, top_off, next, false);
        } else {
            if self.cur_track == Track::Opt {
                self.emit_guard_census(census::DIRTY_ENTER_BUILTIN_MERGE, self.cur_pc);
            }
            let one = self.i32_const(1);
            let margs = self.merge_args(one);
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: margs,
                    },
                },
            );
        }
    }

    /// `builtin_success_exit` for an arm that MUTATED its receiver: the
    /// keep continuation propagates the receiver's classified flag bit
    /// onward (`emit_stamp_cont` -- heap written, no stamps demoted, the
    /// value facts and the track survive), where the clean form would
    /// erase the mutation from the frame's word. The no-state fallback is
    /// the scoped-OR merge join, ticked as a fall-off.
    pub(super) fn builtin_mut_success_exit(
        &mut self,
        pre: &Option<ArmState>,
        need: usize,
        top_off: u32,
        next_pc: Option<Pc>,
        merge: Block,
        recv_bit: u32,
    ) {
        if let Some(pre) = pre {
            let next = next_pc.expect("builtin clean site implies next_pc");
            let w = self.i32_const(recv_bit);
            self.emit_stamp_cont(pre, need, top_off, next, w, None, false);
        } else {
            if self.cur_track == Track::Opt {
                self.emit_guard_census(census::DIRTY_ENTER_BUILTIN_MERGE, self.cur_pc);
            }
            let one = self.i32_const(1);
            let saved_flags = self.cur_flags;
            self.or_flags_const(recv_bit);
            let margs = self.merge_args(one);
            self.cur_flags = saved_flags;
            self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: merge,
                        args: margs,
                    },
                },
            );
        }
    }

    pub(super) fn call_i64(&mut self, func: Func, args: &[Value]) -> Value {
        if self.depart_bracket(func) {
            self.emit_depart_tick(census::FRAME_PUSH);
        }
        let v = if self.mode == EmitMode::ContextOnly {
            self.virtual_value()
        } else {
            let arg_list = self.body.arg_pool.from_iter(args.iter().copied());
            let ty = self.body.single_type_list(Type::I64);
            let v = self.body.add_value(ValueDef::Operator(
                Operator::Call {
                    function_index: func,
                },
                arg_list,
                ty,
            ));
            self.body.append_to_block(self.cur, v);
            v
        };
        self.note_call_eff(v, func);
        v
    }

    /// A leaf f64-returning helper call (`night_runtime_fmod`): no cx, no
    /// rooting handshake.
    pub(super) fn call_f64(&mut self, func: Func, args: &[Value]) -> Value {
        if self.depart_bracket(func) {
            self.emit_depart_tick(census::FRAME_PUSH);
        }
        let v = if self.mode == EmitMode::ContextOnly {
            self.virtual_value()
        } else {
            let arg_list = self.body.arg_pool.from_iter(args.iter().copied());
            let ty = self.body.single_type_list(Type::F64);
            let v = self.body.add_value(ValueDef::Operator(
                Operator::Call {
                    function_index: func,
                },
                arg_list,
                ty,
            ));
            self.body.append_to_block(self.cur, v);
            v
        };
        self.note_call_eff(v, func);
        v
    }

    pub(super) fn call_void(&mut self, func: Func, args: &[Value]) {
        if self.depart_bracket(func) {
            self.emit_depart_tick(census::FRAME_PUSH);
        }
        let v = if self.mode == EmitMode::ContextOnly {
            self.virtual_value()
        } else {
            let arg_list = self.body.arg_pool.from_iter(args.iter().copied());
            let v = self.body.add_value(ValueDef::Operator(
                Operator::Call {
                    function_index: func,
                },
                arg_list,
                Default::default(),
            ));
            self.body.append_to_block(self.cur, v);
            v
        };
        self.note_call_eff(v, func);
    }

    /// `cond != 0 ? a : b` (typed wasm select).
    pub(super) fn select(&mut self, ty: Type, a: Value, b: Value, cond: Value) -> Value {
        if self.mode == EmitMode::ContextOnly {
            return self.virtual_value();
        }
        let args = self.body.arg_pool.from_iter([a, b, cond].into_iter());
        let tys = self.body.single_type_list(ty);
        let v = self
            .body
            .add_value(ValueDef::Operator(Operator::TypedSelect { ty }, args, tys));
        self.body.append_to_block(self.cur, v);
        v
    }

    pub(super) fn tag_eq(&mut self, boxed: Value, tag: u32) -> Value {
        let shift = self.boxed_const(32);
        let hi64 = self.binop(Operator::I64ShrU, boxed, shift, Type::I64);
        let hi = self.unop(Operator::I32WrapI64, hi64, Type::I32);
        let t = self.i32_const(tag);
        self.binop(Operator::I32Eq, hi, t, Type::I32)
    }

    pub(super) fn is_number_tag(&mut self, boxed: Value) -> Value {
        let shift = self.boxed_const(32);
        let hi64 = self.binop(Operator::I64ShrU, boxed, shift, Type::I64);
        let hi = self.unop(Operator::I32WrapI64, hi64, Type::I32);
        let tag = self.i32_const(TAG_INT32 as u32);
        self.binop(Operator::I32LeU, hi, tag, Type::I32)
    }

    pub(super) fn is_double_tag(&mut self, boxed: Value) -> Value {
        let shift = self.boxed_const(32);
        let hi64 = self.binop(Operator::I64ShrU, boxed, shift, Type::I64);
        let hi = self.unop(Operator::I32WrapI64, hi64, Type::I32);
        let clear = self.i32_const(TAG_CLEAR);
        self.binop(Operator::I32LeU, hi, clear, Type::I32)
    }

    // --- box / unbox -----------------------------------------------------

    pub(super) fn to_i32(&mut self, o: &Operand) -> Value {
        match o.repr {
            // A ptr repr IS the low-32 payload -- exactly what the Boxed
            // wrap produces.
            Repr::I32 | Repr::Bool | Repr::StrPtr | Repr::ObjPtr => o.val,
            Repr::Boxed => self.unop(Operator::I32WrapI64, o.val, Type::I32),
            Repr::I64 => self.unop(Operator::I32WrapI64, o.val, Type::I32),
            Repr::F64 => self.unop(Operator::I32TruncF64S, o.val, Type::I32),
        }
    }

    /// Materialize an operand as an f64: exact for numeric-proven operands;
    /// a mixed Int32|Double boxed value takes the tag-select unbox.
    pub(super) fn to_f64(&mut self, o: &Operand) -> Value {
        match o.repr {
            Repr::F64 => o.val,
            Repr::I32 | Repr::Bool => self.unop(Operator::F64ConvertI32S, o.val, Type::F64),
            Repr::I64 => self.unop(Operator::F64ConvertI64S, o.val, Type::F64),
            Repr::Boxed => {
                if is_exact_int32(&o.ty) {
                    let i = self.unop(Operator::I32WrapI64, o.val, Type::I32);
                    self.unop(Operator::F64ConvertI32S, i, Type::F64)
                } else if !o.ty.prims.intersects(PRIM_INT32) {
                    self.unop(Operator::F64ReinterpretI64, o.val, Type::F64)
                } else {
                    self.unbox_number_f64(o.val)
                }
            }
            // Unreachable by proof (a ptr repr is never numeric); total for
            // safety via the boxed generic unbox.
            Repr::StrPtr | Repr::ObjPtr => {
                let b = self.to_boxed(o);
                self.unbox_number_f64(b)
            }
        }
    }

    /// Materialize an operand as an exact-integer i64. Only sound under an
    /// in-domain proof -- the caller checks `i64_arith_operand_ok`.
    pub(super) fn to_i64_exact(&mut self, o: &Operand) -> Value {
        match o.repr {
            Repr::I64 => o.val,
            Repr::I32 => self.unop(Operator::I64ExtendI32S, o.val, Type::I64),
            Repr::Bool => self.unop(Operator::I64ExtendI32U, o.val, Type::I64),
            Repr::F64 => self.unop(Operator::I64TruncSatF64S, o.val, Type::I64),
            Repr::Boxed => {
                if is_exact_int32(&o.ty) {
                    let w = self.unop(Operator::I32WrapI64, o.val, Type::I32);
                    self.unop(Operator::I64ExtendI32S, w, Type::I64)
                } else {
                    self.unbox_number_i64(o.val)
                }
            }
            // Unreachable by proof (never numeric); total for safety.
            Repr::StrPtr | Repr::ObjPtr => {
                let b = self.to_boxed(o);
                self.unbox_number_i64(b)
            }
        }
    }

    /// Unbox a boxed in-domain exact-integer number as an exact i64 (copied
    /// from translate.rs `unbox_number_i64`).
    pub(super) fn unbox_number_i64(&mut self, boxed: Value) -> Value {
        self.int32_chk_census("unbox_i64");
        let shift = self.boxed_const(32);
        let hi64 = self.binop(Operator::I64ShrU, boxed, shift, Type::I64);
        let hi = self.unop(Operator::I32WrapI64, hi64, Type::I32);
        let tag = self.i32_const(TAG_INT32 as u32);
        let is_int = self.binop(Operator::I32Eq, hi, tag, Type::I32);
        let i = self.unop(Operator::I32WrapI64, boxed, Type::I32);
        let v_int = self.unop(Operator::I64ExtendI32S, i, Type::I64);
        let f_dbl = self.unop(Operator::F64ReinterpretI64, boxed, Type::F64);
        let v_dbl = self.unop(Operator::I64TruncSatF64S, f_dbl, Type::I64);
        self.select(Type::I64, v_int, v_dbl, is_int)
    }

    /// `1` iff both boxed operands are JS numbers.
    pub(super) fn both_number_tags(&mut self, a_boxed: Value, b_boxed: Value) -> Value {
        let a_num = self.is_number_tag(a_boxed);
        let b_num = self.is_number_tag(b_boxed);
        self.binop(Operator::I32And, a_num, b_num, Type::I32)
    }

    /// `1` iff no script has been compiled from source text since the
    /// registered graph was recorded -- one load of the night-owned fuse
    /// word and one test. Tagged `FuseCell` so LICM will not lift it out of
    /// a loop that calls anything (the cell IS the guard, and a mid-loop
    /// call can blow it).
    pub(super) fn dyncode_fuse_intact(&mut self) -> Value {
        let addr = self.i32_const(self.helpers.dyncode_fuse_word);
        let w = self.load_i32(addr, 0);
        self.eff(w, Eff::ReadBits(HeapKind::FuseCell));
        self.unop(Operator::I32Eqz, w, Type::I32)
    }

    /// Type a numeric helper's just-returned result at a per-arm
    /// continuation. `mask` is what the result is when it cannot be a
    /// BigInt; the BigInt bit is what disqualifies every downstream
    /// `is_numeric` fast path, so the claim is worth a runtime test.
    ///
    /// The static scan settles the module's own text. What it cannot settle
    /// is source compiled at runtime, so when the text is clean this splits
    /// on the dynamic-code fuse: the intact edge keeps `mask` and falls
    /// through as the arm's result, while the blown edge continues at
    /// `succ_pc` in its own version carrying the BigInt bit -- the very
    /// lowering a module with static BigInt evidence gets throughout. A
    /// static type claim has no branchless runtime guard; a second typed
    /// continuation is the only sound recovery this tier has (there are no
    /// deopt landings), and it is exactly what versioning is for.
    pub(super) fn bigint_result(
        &mut self,
        r: Value,
        mask: Prims,
        riv: opsem::Iv,
        succ_pc: Pc,
    ) -> Operand {
        let weak = Operand::plain(r, Repr::Boxed, prim_desc(mask | PRIM_BIGINT)).with_iv(riv);
        if !self.bigint_free {
            return weak;
        }
        let intact = self.dyncode_fuse_intact();
        let strong_blk = self.body.add_block();
        let weak_blk = self.body.add_block();
        self.cond_br(intact, strong_blk, weak_blk);
        let st = self.arm_state();
        self.cur = weak_blk;
        self.stack.push(weak);
        let target = if self.post_call {
            self.dirty_edge_to(succ_pc)
        } else {
            self.edge_to(succ_pc)
        };
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.arm_restore(st);
        self.cur = strong_blk;
        Operand::plain(r, Repr::Boxed, prim_desc(mask)).with_iv(riv)
    }

    /// The body size every fuel/overflow decision must read. `ContextOnly`
    /// still allocates blocks and block params (so the terminator and
    /// param-layout logic is shared verbatim) but appends no operator
    /// values, so the two halves add up to what `Code` alone puts in
    /// `body.values` -- the lockstep invariant the whole map rests on.
    pub(super) fn value_count(&self) -> usize {
        self.body.values.len() + self.virtual_values - self.instrument_values
    }

    /// The `ContextOnly` stand-in for an appended operator value: nothing is
    /// built, the sentinel flows on (no lowering reads a Value back), and
    /// the count Code mode would have reached advances by one.
    pub(super) fn virtual_value(&mut self) -> Value {
        self.virtual_values += 1;
        Value::invalid()
    }

    pub(super) fn int32_chk_census(&self, site: &str) {
        if self.opts.diagnostics.bbv {
            crate::diag_line!(
                "night: bbv int32chk sid#{} pc {} op {:?} site {site}",
                self.source_id,
                self.cur_pc,
                self.cur_op
            );
        }
    }

    /// `1` iff both boxed operands carry the Int32 tag.
    /// The int32-or-boolean tag test of one operand, or `None` when its
    /// type proves int32 or boolean.
    pub(super) fn int32_or_bool_test(
        &mut self,
        o: &Operand,
        boxed: Option<Value>,
    ) -> Option<Value> {
        if is_exact_int32(&o.ty) || (!o.ty.outside && o.ty.prims.subset_of(PRIM_BOOLEAN)) {
            return None;
        }
        let v = self.box_of(o, boxed);
        let i = self.tag_eq(v, TAG_INT32 as u32);
        let b = self.tag_eq(v, TAG_BOOLEAN as u32);
        Some(self.binop(Operator::I32Or, i, b, Type::I32))
    }

    /// The int32-tag test of one operand of a two-operand ladder, or
    /// `None` when the operand's type already proves int32 -- a tag test
    /// on a value whose type is known is a constant, and the box it would
    /// have been read from is pure waste on the hot path.
    pub(super) fn int32_tag_test(&mut self, o: &Operand, boxed: Option<Value>) -> Option<Value> {
        if is_exact_int32(&o.ty) {
            None
        } else {
            let b = self.box_of(o, boxed);
            Some(self.tag_eq(b, TAG_INT32 as u32))
        }
    }

    /// The number-tag test of one operand, or `None` when its type proves
    /// numeric.
    pub(super) fn number_tag_test(&mut self, o: &Operand, boxed: Option<Value>) -> Option<Value> {
        if is_numeric(&o.ty) {
            None
        } else {
            let b = self.box_of(o, boxed);
            Some(self.is_number_tag(b))
        }
    }

    /// A ladder operand's box, built eagerly only when the operand's type
    /// does not prove int32: an exact operand's box is consumed by the slow
    /// arm alone, and building it in the entry block puts it on every hot
    /// path (Cranelift does not sink).
    pub(super) fn ladder_box(&mut self, o: &Operand) -> Option<Value> {
        if is_exact_int32(&o.ty) {
            None
        } else {
            Some(self.to_boxed(o))
        }
    }

    /// The operand's box, from the ladder's cache or built on the spot (in
    /// the arm that needs it).
    pub(super) fn box_of(&mut self, o: &Operand, cached: Option<Value>) -> Value {
        match cached {
            Some(b) => b,
            None => self.to_boxed(o),
        }
    }

    /// The operand as f64 on a number arm: a raw exact operand converts
    /// directly; a boxed one unboxes through the number-tag select.
    pub(super) fn f64_of(&mut self, o: &Operand, cached: Option<Value>) -> Value {
        if is_exact_int32(&o.ty) || (is_numeric(&o.ty) && o.repr != Repr::Boxed) {
            self.to_f64(o)
        } else {
            let b = self.box_of(o, cached);
            self.unbox_number_f64(b)
        }
    }

    /// Both tests of a ladder step folded: `None` means neither operand
    /// needs one (the caller falls through), one test stands alone, two
    /// are and-ed.
    pub(super) fn and_tests(&mut self, a: Option<Value>, b: Option<Value>) -> Option<Value> {
        match (a, b) {
            (Some(a), Some(b)) => Some(self.binop(Operator::I32And, a, b, Type::I32)),
            (Some(a), None) | (None, Some(a)) => Some(a),
            (None, None) => None,
        }
    }

    /// Branch on a folded ladder test; a `None` test is a constant true and
    /// emits a plain jump.
    pub(super) fn cond_br_opt(&mut self, cond: Option<Value>, if_true: Block, if_false: Block) {
        match cond {
            Some(c) => self.cond_br(c, if_true, if_false),
            None => self.body.set_terminator(
                self.cur,
                Terminator::Br {
                    target: BlockTarget {
                        block: if_true,
                        args: vec![],
                    },
                },
            ),
        }
    }

    /// The int32 payload of an operand on an arm that proved (or whose type
    /// proves) it int32: the raw I32 when the repr already is, else the low
    /// half of the box.
    pub(super) fn int32_payload(&mut self, o: &Operand, cached: Option<Value>) -> Value {
        match o.repr {
            Repr::I32 => o.val,
            Repr::I64 if is_exact_int32(&o.ty) => self.unop(Operator::I32WrapI64, o.val, Type::I32),
            Repr::F64 if is_exact_int32(&o.ty) => {
                self.unop(Operator::I32TruncSatF64S, o.val, Type::I32)
            }
            _ => {
                let b = self.box_of(o, cached);
                self.unop(Operator::I32WrapI64, b, Type::I32)
            }
        }
    }

    /// Inline JS `ToInt32` of any f64, no range precondition: reduce mod
    /// 2^32 in f64, then saturating-truncate. NaN/Inf correctly coerce to 0.
    pub(super) fn to_int32_js(&mut self, f: Value) -> Value {
        let dn = self.f64_const(2.0_f64.powi(-32));
        let scaled = self.binop(Operator::F64Mul, f, dn, Type::F64);
        let t = self.unop(Operator::F64Trunc, scaled, Type::F64);
        let up = self.f64_const(4294967296.0);
        let t32 = self.binop(Operator::F64Mul, t, up, Type::F64);
        let r = self.binop(Operator::F64Sub, f, t32, Type::F64);
        let i64v = self.unop(Operator::I64TruncSatF64S, r, Type::I64);
        self.unop(Operator::I32WrapI64, i64v, Type::I32)
    }

    pub(super) fn unbox_number_f64(&mut self, boxed: Value) -> Value {
        self.int32_chk_census("unbox_f64");
        let shift = self.boxed_const(32);
        let hi64 = self.binop(Operator::I64ShrU, boxed, shift, Type::I64);
        let hi = self.unop(Operator::I32WrapI64, hi64, Type::I32);
        let tag = self.i32_const(TAG_INT32 as u32);
        let is_int = self.binop(Operator::I32Eq, hi, tag, Type::I32);
        let i = self.unop(Operator::I32WrapI64, boxed, Type::I32);
        let f_int = self.unop(Operator::F64ConvertI32S, i, Type::F64);
        let f_dbl = self.unop(Operator::F64ReinterpretI64, boxed, Type::F64);
        self.select(Type::F64, f_int, f_dbl, is_int)
    }

    pub(super) fn box_i64_canonical(&mut self, v: Value) -> Value {
        let w = self.unop(Operator::I32WrapI64, v, Type::I32);
        let sext = self.unop(Operator::I64ExtendI32S, w, Type::I64);
        let fits = self.binop(Operator::I64Eq, sext, v, Type::I32);
        let payload = self.unop(Operator::I64ExtendI32U, w, Type::I64);
        let tag = self.boxed_const(TAG_INT32 << 32);
        let boxed_int = self.binop(Operator::I64Or, payload, tag, Type::I64);
        let f = self.unop(Operator::F64ConvertI64S, v, Type::F64);
        let bits = self.unop(Operator::I64ReinterpretF64, f, Type::I64);
        self.select(Type::I64, boxed_int, bits, fits)
    }

    pub(super) fn box_f64_canonical(&mut self, f: Value) -> Value {
        translate::box_f64_canonical(self, f)
    }

    pub(super) fn to_boxed(&mut self, o: &Operand) -> Value {
        match o.repr {
            Repr::Boxed => o.val,
            Repr::I32 => {
                let payload = self.unop(Operator::I64ExtendI32U, o.val, Type::I64);
                let tag = self.boxed_const(TAG_INT32 << 32);
                self.binop(Operator::I64Or, payload, tag, Type::I64)
            }
            Repr::Bool => {
                let payload = self.unop(Operator::I64ExtendI32U, o.val, Type::I64);
                let tag = self.boxed_const(TAG_BOOLEAN << 32);
                self.binop(Operator::I64Or, payload, tag, Type::I64)
            }
            // An exact-Double fact IS the licence to skip the int32
            // canonicalization: the boxed form the fact describes is the
            // f64 bits themselves.
            Repr::F64 if is_exact_double(&o.ty) => {
                self.unop(Operator::I64ReinterpretF64, o.val, Type::I64)
            }
            Repr::F64 => self.box_f64_canonical(o.val),
            Repr::I64 => self.box_i64_canonical(o.val),
            Repr::StrPtr => {
                let payload = self.unop(Operator::I64ExtendI32U, o.val, Type::I64);
                let tag = self.boxed_const(TAG_STRING << 32);
                self.binop(Operator::I64Or, payload, tag, Type::I64)
            }
            Repr::ObjPtr => {
                let payload = self.unop(Operator::I64ExtendI32U, o.val, Type::I64);
                let tag = self.boxed_const(TAG_OBJECT << 32);
                self.binop(Operator::I64Or, payload, tag, Type::I64)
            }
        }
    }

    /// The raw low-32 payload (JSString*/JSObject*) of a string/object
    /// operand: free for the ptr reprs (this is the repr's point -- the
    /// unbox is shared across consuming ops), one wrap otherwise.
    pub(super) fn to_ptr(&mut self, o: &Operand) -> Value {
        match o.repr {
            Repr::StrPtr | Repr::ObjPtr => o.val,
            _ => {
                let b = self.to_boxed(o);
                self.unop(Operator::I32WrapI64, b, Type::I32)
            }
        }
    }

    // --- operand stack ---------------------------------------------------

    /// Every ordinary push carries `bottom_ty` (no fact source: generic
    /// helper results). Facts enter only through literals, op semantics
    /// (`push_known`), and the version ctx.
    pub(super) fn push(&mut self, val: Value, repr: Repr, _ty: TypeDesc) {
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
            crate::diag_line!(
                "night: bbv bottompush sid#{} pc {} op {:?}",
                self.source_id,
                self.cur_pc,
                self.cur_op
            );
        }
        self.stack.push(Operand::plain(val, repr, bottom_ty()));
    }

    /// A literal's exact type is proven by the translator itself (the value
    /// IS the literal).
    pub(super) fn push_literal(&mut self, val: Value, repr: Repr, ty: TypeDesc) {
        self.stack.push(Operand::plain(val, repr, ty));
    }

    /// A type proven by the lowering's own semantics (e.g. a compare's
    /// boolean result).
    pub(super) fn push_known(&mut self, val: Value, repr: Repr, ty: TypeDesc) {
        self.stack.push(Operand::plain(val, repr, ty));
    }

    /// `push_known` with a range-bucket claim (e.g. an overflow arm's
    /// integral double, `>>>`'s u32 result).
    pub(super) fn push_ranged(&mut self, val: Value, repr: Repr, ty: TypeDesc, range: RangeBucket) {
        self.stack.push(Operand::ranged(val, repr, ty, range));
    }

    /// An int literal push: the value IS the constant, so it carries the
    /// exact one-point interval (the vocabulary's literal minting rule).
    pub(super) fn push_int_literal(&mut self, val: Value, imm: i64) {
        self.stack.push(
            Operand::plain(val, Repr::I32, prim_desc(PRIM_INT32)).with_iv(Some((imm, imm, false))),
        );
    }

    pub(super) fn push_boxed(&mut self, val: Value, ty: TypeDesc) {
        self.push(val, Repr::Boxed, ty);
    }

    pub(super) fn pop(&mut self) -> Result<Operand, String> {
        self.stack
            .pop()
            .ok_or_else(|| "operand stack underflow".to_string())
    }

    /// No per-pc analysis def types in the BBV lane; kept as the seam the
    /// copied lowerings read (`push` discards it anyway).
    pub(super) fn def_type(&self, _pc: Pc, _idx: usize) -> TypeDesc {
        TypeDesc::default()
    }

    /// A prim-only semantic result fact ("definitely one of these
    /// primitives"): exact, excludes objects.
    pub(super) fn result_ty_fact(&self, _pc: Pc, prims: Prims) -> TypeDesc {
        prim_desc(prims)
    }

    // --- rooting + error handshake ---------------------------------------

    /// Spill every live operand (boxed) into the frame spill region so the
    /// GC root tracer sees them across a may-GC call.
    pub(super) fn spill_all(&mut self) -> u32 {
        let base = self.operand_base;
        for i in 0..self.stack.len() {
            let o = self.stack[i].clone();
            let boxed = self.to_boxed(&o);
            self.store_i64(self.vp, base + 8 * i as u32, boxed);
        }
        u32::try_from(self.stack.len()).unwrap()
    }

    /// Reload the bottom `n` spilled operands (they may have moved in a GC).
    pub(super) fn reload(&mut self, n: u32) {
        let base = self.operand_base;
        for i in 0..n as usize {
            let v = self.load_i64(self.vp, base + 8 * i as u32);
            self.stack[i].val = v;
            self.stack[i].repr = Repr::Boxed;
        }
    }

    /// May-GC runtime-helper call with the rooting handshake: spill,
    /// `helper(cx, top, ...args) -> ok`, reload, route `ok == 0` to the
    /// enclosing handler. `top` is the GC scan limit and doubles as the
    /// boxed out-slot.
    pub(super) fn rt_call(
        &mut self,
        helper: Func,
        has_out: bool,
        build_args: impl FnOnce(&mut Self, u32) -> Vec<Value>,
    ) -> Option<Value> {
        let n = self.spill_all();
        let slot_off = self.operand_base + 8 * n;
        let top = self.add_offset(self.vp, slot_off);
        let mut full = vec![self.cx, top];
        full.extend(build_args(self, n));
        let ret = self.call_i32(helper, &full);
        self.reload(n);
        let result = if has_out {
            Some(self.load_i64(self.vp, slot_off))
        } else {
            None
        };
        self.branch_on_err(ret);
        result
    }

    /// `rt_call` for a boxed unary helper.
    pub(super) fn rt_unary_boxed(&mut self, helper: Func, arg: Value) -> Value {
        self.rt_call(helper, true, move |_, _| vec![arg]).unwrap()
    }

    /// `rt_call` for an unconditional main-line CallGc helper op, wrapped
    /// in the fork-site epoch compare (the apply-fwd tail's discipline,
    /// generalized): the epoch is sampled on the op's main line before the
    /// call -- the dominance-safe placement -- and an unchanged epoch
    /// across the helper proves every stamp-guarded fact still holds, so
    /// the keep arm restores the pre-call emitter state, sweeps carriers,
    /// ORs the MUT bits onward, pushes the helper's result under
    /// `result_ty`, and continues at `next_pc` as its own kept-track
    /// lineage. The fall-through remains the ordinary post-call Dirty
    /// continuation, which then pushes the result itself.
    ///
    /// Contract: the op's `need` consumed operands are still ON the stack
    /// (this pops them on both paths after the call, keeping them spilled
    /// and rooted across the helper).
    pub(super) fn rt_call_keep(
        &mut self,
        helper: Func,
        need: usize,
        next_pc: Option<Pc>,
        result_ty: &TypeDesc,
        args: Vec<Value>,
    ) -> Value {
        self.rt_call_keep_claim(helper, need, next_pc, result_ty, args, None)
    }

    /// `rt_call_keep` whose keep arm runs the site's typed-load ladder on
    /// the result (`claim`, with its table's provenance), so the kept
    /// lineage joins `next_pc` with the SAME result fact as the caller's
    /// fall-through -- the epoch_keep_tail_claim rule: a bottom result
    /// joining a typed one strips the fact for every lineage there.
    pub(super) fn rt_call_keep_claim(
        &mut self,
        helper: Func,
        need: usize,
        next_pc: Option<Pc>,
        result_ty: &TypeDesc,
        args: Vec<Value>,
        claim: Option<(Claim, Prov)>,
    ) -> Value {
        // No flags-threading requirement: a body that does not thread the
        // accumulator returns a saturated word regardless, so the OR below
        // is skipped and the keep arm's value is local -- the restored
        // facts and the kept track.
        let fork_ok = next_pc.is_some() && !self.gen_only && self.cur_track != Track::Dirty;
        let (pre_state, pre_e, pre_b) = if fork_ok {
            let p = self.arm_state();
            let e = self.emit_epoch_read();
            let b = self.sample_bind_epoch();
            (Some(p), Some(e), b)
        } else {
            (None, None, None)
        };
        let result = self.rt_call(helper, true, move |_, _| args).unwrap();
        if let (Some(pre), Some(pre_e), Some(fnext)) = (pre_state, pre_e, next_pc) {
            let post = self.emit_epoch_read();
            let same = self.binop(Operator::I32Eq, pre_e, post, Type::I32);
            let keep_blk = self.body.add_block();
            let cont_blk = self.body.add_block();
            self.cond_br(same, keep_blk, cont_blk);
            self.cur = keep_blk;
            self.emit_census(49, self.root_source_id, fnext);
            let k_state = self.arm_state();
            self.arm_restore(pre);
            for _ in 0..need {
                self.stack.pop();
            }
            self.reload_gc_values();
            if self.flags_threading() {
                self.or_flags_const(FLAG_MUT_THIS | FLAG_MUT_OTHER | FLAG_BIND);
            }
            match claim {
                Some((c, p)) => self.push_load_typed(result, c, fnext, p),
                None => self.push_boxed(result, *result_ty),
            }
            self.gcells_keep(None, pre_b, fnext);
            let target = self.cont(fnext);
            self.body
                .set_terminator(self.cur, Terminator::Br { target });
            self.arm_restore(k_state);
            self.cur = cont_blk;
        }
        for _ in 0..need {
            self.stack.pop();
        }
        result
    }

    /// `rt_call_keep`'s fork for a helper called through the diamond ABI
    /// (operands already popped and spilled by the caller, result already
    /// loaded): `pre` and `pre_e` were taken on the arm's entry before the
    /// call. The keep arm restores `pre`, pushes `result` and continues at
    /// `next_pc`; emission resumes in the fall-through block, where the
    /// caller joins its merge as before. Declined on a Dirty lineage, on
    /// GEN, and under a mapped arguments object (the helper may run user
    /// code that rewrites this frame's formals without moving a stamp).
    pub(super) fn epoch_keep_tail(
        &mut self,
        pre: ArmState,
        pre_e: Value,
        pre_bind: Option<Value>,
        ok: Value,
        result: Option<(Value, TypeDesc)>,
        next_pc: Pc,
    ) {
        self.epoch_keep_tail_claim(pre, pre_e, pre_bind, ok, result, None, next_pc);
    }

    /// `epoch_keep_tail` whose pushed result runs the site's typed-load
    /// ladder (`claim`) so the keep lineage joins `next_pc` with the SAME
    /// result fact as the fast arms: a bottom-typed result joining a typed
    /// one boxes the chain behind it at compile time.
    pub(super) fn epoch_keep_tail_claim(
        &mut self,
        pre: ArmState,
        pre_e: Value,
        pre_bind: Option<Value>,
        ok: Value,
        result: Option<(Value, TypeDesc)>,
        claim: Option<(Claim, Prov)>,
        next_pc: Pc,
    ) {
        if self.gen_only || pre.track == Track::Dirty || self.mapped_args_reachable() {
            return;
        }
        if self.opts.diagnostics.bbv && self.mode == EmitMode::Code {
            crate::diag_line!(
                "night: bbv keep-site sid#{} pc {} form tail",
                self.source_id,
                self.evid_pc(self.cur_pc)
            );
        }
        let post = self.emit_epoch_read();
        let same = self.binop(Operator::I32Eq, pre_e, post, Type::I32);
        let keep = self.binop(Operator::I32And, ok, same, Type::I32);
        let keep_blk = self.body.add_block();
        let cont_blk = self.body.add_block();
        self.cond_br(keep, keep_blk, cont_blk);
        self.cur = keep_blk;
        self.emit_census(49, self.root_source_id, next_pc);
        let k_state = self.arm_state();
        self.arm_restore(pre);
        self.reload_gc_values();
        if self.flags_threading() {
            self.or_flags_const(FLAG_MUT_THIS | FLAG_MUT_OTHER | FLAG_BIND);
        }
        match (result, claim) {
            (Some((v, _)), Some((c, p))) => self.push_load_typed(v, c, next_pc, p),
            (Some((v, ty)), None) => self.push_boxed(v, ty),
            (None, _) => {}
        }
        self.gcells_keep(None, pre_bind, next_pc);
        let target = self.cont(next_pc);
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
        self.arm_restore(k_state);
        self.cur = cont_blk;
    }

    /// `rt_call` for a void helper that unconditionally raises (Throw
    /// forms); branches to the enclosing handler, no success path.
    pub(super) fn rt_throw(&mut self, helper: Func, args: &[Value]) {
        let n = self.spill_all();
        let slot_off = self.operand_base + 8 * n;
        let top = self.add_offset(self.vp, slot_off);
        let mut full = vec![self.cx, top];
        full.extend_from_slice(args);
        self.call_void(helper, &full);
        self.reload(n);
        let target = self.exception_target();
        self.body
            .set_terminator(self.cur, Terminator::Br { target });
    }

    /// Replace the env head via a may-GC helper (Push*Env forms); copied
    /// from translate.rs `emit_env_replace`.
    pub(super) fn emit_env_replace(
        &mut self,
        helper: Func,
        build: impl FnOnce(&mut Self, Value) -> Vec<Value>,
    ) {
        let env = self.load_i64(self.vp, self.env_slot_off);
        let args = build(self, env);
        let result = self.rt_call(helper, true, move |_, _| args).unwrap();
        self.store_i64(self.vp, self.env_slot_off, result);
    }

    /// The shared error epilogue (`return err=1`). A generator body takes
    /// the closing form instead: a surviving JS_GENERATOR_CLOSING magic is
    /// a completed forced `.return()`, which returns normally.
    pub(super) fn error_block(&mut self) -> Block {
        if let Some(b) = self.error_blk {
            return b;
        }
        let b = self.body.add_block();
        let saved_cur = self.cur;
        if self.is_generator {
            self.emit_gen_error_epilogue(b);
            self.cur = saved_cur;
            self.error_blk = Some(b);
            return b;
        }
        self.cur = b;
        let one = self.i32_const(1);
        let flags = self.i32_const(FLAGS_ALL);
        self.body.set_terminator(
            b,
            Terminator::Return {
                values: vec![one, flags],
            },
        );
        self.cur = saved_cur;
        self.error_blk = Some(b);
        b
    }

    /// On `ret == 0` branch to the exception target; else continue in a
    /// fresh block.
    pub(super) fn branch_on_err(&mut self, ret: Value) {
        let err_target = self.exception_target();
        let success = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond: ret,
                if_true: BlockTarget {
                    block: success,
                    args: vec![],
                },
                if_false: err_target,
            },
        );
        self.cur = success;
    }

    // --- deferred-spill diamonds -----------------------------------------

    pub(super) fn diamond_snapshot(&self) -> (Vec<Repr>, Vec<Value>) {
        (
            self.stack.iter().map(|o| o.repr).collect(),
            self.stack.iter().map(|o| o.val).collect(),
        )
    }

    pub(super) fn diamond_params(&mut self, merge: Block, reprs: &[Repr]) -> Vec<Value> {
        // The viz wants to know what a merge's params hold, which the
        // emitter knows and the IR does not: they are the operand stack,
        // in order, in the reprs the arms agreed on.
        if self.opts.diagnostics.viz_lower && self.mode == EmitMode::Code {
            let rs: Vec<String> = reprs.iter().map(|r| format!("{r:?}")).collect();
            crate::diag_line!(
                "night: viz lowerp sid#{} blk b{} kind stack reprs [{}]",
                self.root_source_id,
                merge.index(),
                rs.join(",")
            );
        }
        reprs
            .iter()
            .map(|r| {
                let ty = match r {
                    Repr::Boxed | Repr::I64 => Type::I64,
                    Repr::F64 => Type::F64,
                    Repr::I32 | Repr::Bool | Repr::StrPtr | Repr::ObjPtr => Type::I32,
                };
                self.body.add_blockparam(merge, ty)
            })
            .collect()
    }

    pub(super) fn diamond_slow_args(&mut self, reprs: &[Repr]) -> Vec<Value> {
        let base = self.operand_base;
        reprs
            .iter()
            .enumerate()
            .map(|(i, r)| {
                let v = self.load_i64(self.vp, base + 8 * i as u32);
                match r {
                    Repr::Boxed => v,
                    // Frame slots hold boxes (spill_all re-boxes); the ptr
                    // reprs reload as the low-32 payload.
                    Repr::I32 | Repr::Bool | Repr::StrPtr | Repr::ObjPtr => {
                        self.unop(Operator::I32WrapI64, v, Type::I32)
                    }
                    Repr::F64 => self.unbox_number_f64(v),
                    Repr::I64 => self.unbox_number_i64(v),
                }
            })
            .collect()
    }

    pub(super) fn diamond_rebind(&mut self, params: &[Value]) {
        for (i, &p) in params.iter().enumerate() {
            self.stack[i].val = p;
        }
    }

    pub(super) fn diamond_begin(&mut self) -> DiamondPre {
        let (reprs, vals) = self.diamond_snapshot();
        let top_off = self.operand_base + 8 * u32::try_from(reprs.len()).unwrap();
        DiamondPre {
            reprs,
            vals,
            top_off,
        }
    }

    pub(super) fn diamond_merge(&mut self, pre: DiamondPre, res_ty: Option<Type>) -> Diamond {
        let merge = self.body.add_block();
        let op_params = self.diamond_params(merge, &pre.reprs);
        let res_param = res_ty.map(|t| self.body.add_blockparam(merge, t));
        let ok_param = Some(self.body.add_blockparam(merge, Type::I32));
        Diamond {
            reprs: pre.reprs,
            vals: pre.vals,
            top_off: pre.top_off,
            merge,
            op_params,
            ok_param,
            res_param,
        }
    }

    pub(super) fn diamond_slow_br(&mut self, d: &Diamond, extras: &[Value]) {
        let mut args = self.diamond_slow_args(&d.reprs);
        args.extend_from_slice(extras);
        let blk = self.cur;
        self.body.set_terminator(
            blk,
            Terminator::Br {
                target: BlockTarget {
                    block: d.merge,
                    args,
                },
            },
        );
    }

    pub(super) fn diamond_join(&mut self, d: &Diamond) {
        self.cur = d.merge;
        self.diamond_rebind(&d.op_params);
        for (i, &r) in d.reprs.iter().enumerate() {
            self.stack[i].repr = r;
        }
        if let Some(ok) = d.ok_param {
            self.branch_on_err(ok);
        }
    }
}

/// Live-operand snapshot at diamond entry.
pub(super) struct DiamondPre {
    pub(super) reprs: Vec<Repr>,
    pub(super) vals: Vec<Value>,
    pub(super) top_off: u32,
}

pub(super) struct Diamond {
    pub(super) reprs: Vec<Repr>,
    pub(super) vals: Vec<Value>,
    pub(super) top_off: u32,
    pub(super) merge: Block,
    pub(super) op_params: Vec<Value>,
    pub(super) ok_param: Option<Value>,
    pub(super) res_param: Option<Value>,
}

impl<'a> translate::BoxEmit for Bbv<'a> {
    fn emit_un(&mut self, op: Operator, a: Value, result: Type) -> Value {
        self.unop(op, a, result)
    }
    fn emit_bin(&mut self, op: Operator, a: Value, b: Value, result: Type) -> Value {
        self.binop(op, a, b, result)
    }
    fn emit_i64c(&mut self, value: u64) -> Value {
        self.boxed_const(value)
    }
    fn emit_sel(&mut self, ty: Type, a: Value, b: Value, cond: Value) -> Value {
        self.select(ty, a, b, cond)
    }
}
