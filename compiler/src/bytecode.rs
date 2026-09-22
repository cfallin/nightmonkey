/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

use crate::ids::Pc;
use crate::source::SourceObjectId;

mod opcodes {
    include!(concat!(env!("OUT_DIR"), "/opcodes.rs"));
}
pub use opcodes::JSOp;

/// Mirrors C++ `TryNoteKind` (js/src/vm/StencilEnums.h).
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TryNoteKind {
    Catch = 0,
    Finally = 1,
    ForIn = 2,
    Destructuring = 3,
    ForOf = 4,
    ForOfIterClose = 5,
    Loop = 6,
}

#[derive(Clone, Copy, Debug)]
pub struct TryNote {
    pub kind: TryNoteKind,
    pub stack_depth: u32,
    pub start: Pc,
    pub length: u32,
}

/// Mirrors C++ `ScopeNote` (js/src/vm/SharedStencil.h): the static
/// scope covering a bytecode range.
#[derive(Clone, Copy, Debug)]
pub struct ScopeNote {
    /// Index of the scope in the script's gcthings, or u32::MAX for
    /// "no block scope in this range" (the body scope applies).
    pub gcthing_index: u32,
    pub start: Pc,
    pub length: u32,
}

#[derive(Debug)]
pub struct Script {
    pub bytecode: Vec<u8>,
    /// Runtime `JSScript*` cell address (0 when unavailable, e.g. sources
    /// built without a live heap). Stable once read: compaction is disabled.
    pub addr: u32,
    pub gcthings: Vec<SourceObjectId>,
    pub resume_offsets: Vec<Pc>,
    pub try_notes: Vec<TryNote>,
    pub scope_notes: Vec<ScopeNote>,
    /// The script's outermost (body) scope: the static scope at any
    /// PC not covered by a scope note.
    pub body_scope: Option<SourceObjectId>,
    /// Declared formal-argument count (0 for non-function scripts).
    pub nargs: u16,
    /// Whether the script is a generator or async function: calling
    /// it returns a VM-created generator/promise object, not its Ret
    /// value.
    pub is_generator_or_async: bool,
    /// Whether the script is a class constructor body: it has no `[[Call]]`
    /// (a call must throw, only constructs run it), so call-site direct
    /// dispatch (splice / fuse arm) must exclude it.
    pub is_class_ctor: bool,
    /// Whether the script is strict-mode code. Sloppy scripts need the
    /// `FunctionThis` boxing diamond (null/undefined -> global,
    /// primitives -> wrappers).
    pub strict: bool,
    /// Whether the script gets a mapped arguments object (sloppy, simple
    /// formals, uses `arguments`): writes through `arguments[i]` alias the
    /// formals. The lazy-args machinery builds only the unmapped flavor,
    /// so such scripts stay interpreted (capability gate).
    pub has_mapped_args: bool,
}

impl Script {
    pub fn parser(&self) -> BytecodeParser<'_> {
        // Try notes are stored in emission-completion order (inner
        // notes first), not by start offset; sort so the parser can
        // surface them as their start PC is reached.
        let mut try_notes = self.try_notes.clone();
        try_notes.sort_by_key(|n| n.start);
        BytecodeParser {
            pc: Pc::new(0),
            data: &self.bytecode[..],
            try_notes,
            try_note_idx: 0,
            resume_offsets: &self.resume_offsets[..],
        }
    }
}

pub struct BytecodeParser<'a> {
    pc: Pc,
    data: &'a [u8],
    try_notes: Vec<TryNote>,
    try_note_idx: usize,
    resume_offsets: &'a [Pc],
}

impl<'a> BytecodeParser<'a> {
    /// Number of unconsumed bytes remaining (used to measure how many bytes
    /// an op consumed).
    pub fn remaining(&self) -> usize {
        self.data.len()
    }

    pub fn read_byte(&mut self) -> Option<u8> {
        if self.data.is_empty() {
            return None;
        }
        let byte = self.data[0];
        self.data = &self.data[1..];
        self.pc += 1;
        Some(byte)
    }

    pub fn next_op(&mut self) -> Option<JSOp> {
        let byte = self.read_byte()?;
        Some(JSOp::from_byte(byte).expect("Invalid bytecode"))
    }

    pub fn try_note_at_pc(&mut self) -> Option<TryNote> {
        // Multiple notes can start at the same PC (e.g. a for-of
        // loop's ForOf and iterator-close ranges); callers loop until
        // None.
        if self.try_note_idx < self.try_notes.len()
            && self.try_notes[self.try_note_idx].start <= self.pc
        {
            let ret = self.try_notes[self.try_note_idx];
            self.try_note_idx += 1;
            Some(ret)
        } else {
            None
        }
    }

    pub fn next_uint8(&mut self) -> Option<u8> {
        self.read_byte()
    }

    pub fn next_uint16(&mut self) -> Option<u16> {
        let a = u16::from(self.read_byte()?);
        let b = u16::from(self.read_byte()?);
        Some(a | (b << 8))
    }

    pub fn peek_uint16(&self) -> Option<u16> {
        if self.data.len() < 2 {
            None
        } else {
            Some(u16::from_le_bytes([self.data[0], self.data[1]]))
        }
    }

    pub fn next_uint24(&mut self) -> Option<u32> {
        let a = u32::from(self.read_byte()?);
        let b = u32::from(self.read_byte()?);
        let c = u32::from(self.read_byte()?);
        Some(a | (b << 8) | (c << 16))
    }

    pub fn next_uint32(&mut self) -> Option<u32> {
        let a = u32::from(self.read_byte()?);
        let b = u32::from(self.read_byte()?);
        let c = u32::from(self.read_byte()?);
        let d = u32::from(self.read_byte()?);
        Some(a | (b << 8) | (c << 16) | (d << 24))
    }

    pub fn next_uint64(&mut self) -> Option<u64> {
        let a = u64::from(self.next_uint32()?);
        let b = u64::from(self.next_uint32()?);
        Some(a | (b << 32))
    }

    pub fn advance(&mut self, len: usize) -> Option<()> {
        if len > self.data.len() {
            return None;
        }
        self.data = &self.data[len..];
        self.pc += u32::try_from(len).unwrap();
        Some(())
    }

    pub fn opcodes<'b>(&'b mut self) -> impl Iterator<Item = JSOp> + 'b
    where
        'b: 'a,
    {
        std::iter::from_fn(|| {
            let op = self.next_op()?;
            self.advance(usize::try_from(op.len()).unwrap() - 1)?;
            Some(op)
        })
    }

    pub fn next_int8(&mut self) -> Option<i8> {
        Some(self.read_byte()? as i8)
    }

    pub fn next_int32(&mut self) -> Option<i32> {
        Some(self.next_uint32()? as i32)
    }

    pub fn visit<V: OpcodeVisitor>(mut self, mut visitor: V) -> V {
        let mut pc = 0u32;
        loop {
            let before = self.data.len();
            let Some(op) = self.next_op() else { break };
            let nuses = match op {
                // Call and variants: callee, this, args[0..argc]
                JSOp::Call
                | JSOp::CallContent
                | JSOp::CallIter
                | JSOp::CallContentIter
                | JSOp::CallIgnoresRv
                | JSOp::Eval
                | JSOp::StrictEval => u32::from(self.peek_uint16().unwrap()) + 2,
                // New and variants: callee, isConstructing, args[0..argc], newTarget
                JSOp::New | JSOp::NewContent | JSOp::SuperCall => {
                    u32::from(self.peek_uint16().unwrap()) + 3
                }
                // PopN: discarded[0..n]
                JSOp::PopN => u32::from(self.peek_uint16().unwrap()),
                // All others are fixed-use-count.
                _ => op.nuses().unwrap(),
            };
            let ndefs = op.ndefs();
            visitor.before_op(
                Pc::new(pc),
                op,
                usize::try_from(nuses).unwrap(),
                usize::try_from(ndefs).unwrap(),
            );
            match op {
                JSOp::Undefined => visitor.undefined(),
                JSOp::Null => visitor.null(),
                JSOp::False => visitor.false_(),
                JSOp::True => visitor.true_(),
                JSOp::Int32 => {
                    let value = self.next_uint32().unwrap();
                    visitor.int32(value);
                }
                JSOp::Zero => visitor.zero(),
                JSOp::One => visitor.one(),
                JSOp::Int8 => {
                    let value = self.next_uint8().unwrap();
                    visitor.int8(value);
                }
                JSOp::Uint16 => {
                    let value = self.next_uint16().unwrap();
                    visitor.uint16(value);
                }
                JSOp::Uint24 => {
                    let value = self.next_uint24().unwrap();
                    visitor.uint24(value);
                }
                JSOp::Double => {
                    let value = self.next_uint64().unwrap();
                    visitor.double(value);
                }
                JSOp::BigInt => {
                    let bigint_index = self.next_uint32().unwrap();
                    visitor.bigint(bigint_index);
                }
                JSOp::String => {
                    let atom_index = self.next_uint32().unwrap();
                    visitor.string(atom_index);
                }
                JSOp::Symbol => {
                    let code = self.next_uint8().unwrap();
                    visitor.symbol(code);
                }
                JSOp::Void => visitor.void(),
                JSOp::Typeof => visitor.typeof_(),
                JSOp::TypeofExpr => visitor.typeof_expr(),
                JSOp::TypeofEq => {
                    let operand = self.next_uint8().unwrap();
                    visitor.typeof_eq(operand);
                }
                JSOp::Pos => visitor.pos(),
                JSOp::Neg => visitor.neg(),
                JSOp::BitNot => visitor.bit_not(),
                JSOp::Not => visitor.not_(),
                JSOp::BitOr => visitor.bit_or(),
                JSOp::BitXor => visitor.bit_xor(),
                JSOp::BitAnd => visitor.bit_and(),
                JSOp::Eq => visitor.eq(),
                JSOp::Ne => visitor.ne(),
                JSOp::StrictEq => visitor.strict_eq(),
                JSOp::StrictNe => visitor.strict_ne(),
                JSOp::StrictConstantEq => {
                    let operand = self.next_uint16().unwrap();
                    visitor.strict_constant_eq(operand);
                }
                JSOp::StrictConstantNe => {
                    let operand = self.next_uint16().unwrap();
                    visitor.strict_constant_ne(operand);
                }
                JSOp::Lt => visitor.lt(),
                JSOp::Gt => visitor.gt(),
                JSOp::Le => visitor.le(),
                JSOp::Ge => visitor.ge(),
                JSOp::Instanceof => visitor.instanceof(),
                JSOp::In => visitor.in_(),
                JSOp::Lsh => visitor.lsh(),
                JSOp::Rsh => visitor.rsh(),
                JSOp::Ursh => visitor.ursh(),
                JSOp::Add => visitor.add(),
                JSOp::Sub => visitor.sub(),
                JSOp::Inc => visitor.inc(),
                JSOp::Dec => visitor.dec(),
                JSOp::Mul => visitor.mul(),
                JSOp::Div => visitor.div(),
                JSOp::Mod => visitor.mod_(),
                JSOp::Pow => visitor.pow(),
                JSOp::NopIsAssignOp => visitor.nop_is_assign_op(),
                JSOp::ToPropertyKey => visitor.to_property_key(),
                JSOp::ToNumeric => visitor.to_numeric(),
                JSOp::ToString => visitor.to_string(),
                JSOp::IsNullOrUndefined => visitor.is_null_or_undefined(),
                JSOp::GlobalThis => visitor.global_this(),
                JSOp::NonSyntacticGlobalThis => visitor.non_syntactic_global_this(),
                JSOp::NewTarget => visitor.new_target(),
                JSOp::DynamicImport => visitor.dynamic_import(),
                JSOp::ImportMeta => visitor.import_meta(),
                JSOp::NewInit => {
                    let property_count = self.next_uint8().unwrap();
                    visitor.new_init(property_count);
                }
                JSOp::NewObject => {
                    let shape_index = self.next_uint32().unwrap();
                    visitor.new_object(shape_index);
                }
                JSOp::Object => {
                    let object_index = self.next_uint32().unwrap();
                    visitor.object(object_index);
                }
                JSOp::ObjWithProto => visitor.obj_with_proto(),
                JSOp::InitProp => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.init_prop(name_index);
                }
                JSOp::InitHiddenProp => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.init_hidden_prop(name_index);
                }
                JSOp::InitLockedProp => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.init_locked_prop(name_index);
                }
                JSOp::InitElem => visitor.init_elem(),
                JSOp::InitHiddenElem => visitor.init_hidden_elem(),
                JSOp::InitLockedElem => visitor.init_locked_elem(),
                JSOp::InitPropGetter => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.init_prop_getter(name_index);
                }
                JSOp::InitHiddenPropGetter => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.init_hidden_prop_getter(name_index);
                }
                JSOp::InitElemGetter => visitor.init_elem_getter(),
                JSOp::InitHiddenElemGetter => visitor.init_hidden_elem_getter(),
                JSOp::InitPropSetter => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.init_prop_setter(name_index);
                }
                JSOp::InitHiddenPropSetter => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.init_hidden_prop_setter(name_index);
                }
                JSOp::InitElemSetter => visitor.init_elem_setter(),
                JSOp::InitHiddenElemSetter => visitor.init_hidden_elem_setter(),
                JSOp::GetProp => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.get_prop(name_index);
                }
                JSOp::GetElem => visitor.get_elem(),
                JSOp::SetProp => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.set_prop(name_index);
                }
                JSOp::StrictSetProp => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.strict_set_prop(name_index);
                }
                JSOp::SetElem => visitor.set_elem(),
                JSOp::StrictSetElem => visitor.strict_set_elem(),
                JSOp::DelProp => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.del_prop(name_index);
                }
                JSOp::StrictDelProp => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.strict_del_prop(name_index);
                }
                JSOp::DelElem => visitor.del_elem(),
                JSOp::StrictDelElem => visitor.strict_del_elem(),
                JSOp::HasOwn => visitor.has_own(),
                JSOp::CheckPrivateField => {
                    let throw_condition = self.next_uint8().unwrap();
                    let msg_kind = self.next_uint8().unwrap();
                    visitor.check_private_field(throw_condition, msg_kind);
                }
                JSOp::NewPrivateName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.new_private_name(name_index);
                }
                JSOp::SuperBase => visitor.super_base(),
                JSOp::GetPropSuper => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.get_prop_super(name_index);
                }
                JSOp::GetElemSuper => visitor.get_elem_super(),
                JSOp::SetPropSuper => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.set_prop_super(name_index);
                }
                JSOp::StrictSetPropSuper => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.strict_set_prop_super(name_index);
                }
                JSOp::SetElemSuper => visitor.set_elem_super(),
                JSOp::StrictSetElemSuper => visitor.strict_set_elem_super(),
                JSOp::Iter => visitor.iter(),
                JSOp::MoreIter => visitor.more_iter(),
                JSOp::IsNoIter => visitor.is_no_iter(),
                JSOp::EndIter => visitor.end_iter(),
                JSOp::CloseIter => {
                    let kind = self.next_uint8().unwrap();
                    visitor.close_iter(kind);
                }
                JSOp::OptimizeGetIterator => visitor.optimize_get_iterator(),
                JSOp::CheckIsObj => {
                    let kind = self.next_uint8().unwrap();
                    visitor.check_is_obj(kind);
                }
                JSOp::CheckObjCoercible => visitor.check_obj_coercible(),
                JSOp::ToAsyncIter => visitor.to_async_iter(),
                JSOp::MutateProto => visitor.mutate_proto(),
                JSOp::NewArray => {
                    let length = self.next_uint32().unwrap();
                    visitor.new_array(length);
                }
                JSOp::InitElemArray => {
                    let index = self.next_uint32().unwrap();
                    visitor.init_elem_array(index);
                }
                JSOp::InitElemInc => visitor.init_elem_inc(),
                JSOp::Hole => visitor.hole(),
                JSOp::RegExp => {
                    let regexp_index = self.next_uint32().unwrap();
                    visitor.reg_exp(regexp_index);
                }
                JSOp::Lambda => {
                    let func_index = self.next_uint32().unwrap();
                    visitor.lambda(func_index);
                }
                JSOp::SetFunName => {
                    let prefix_kind = self.next_uint8().unwrap();
                    visitor.set_fun_name(prefix_kind);
                }
                JSOp::InitHomeObject => visitor.init_home_object(),
                JSOp::CheckClassHeritage => visitor.check_class_heritage(),
                JSOp::FunWithProto => {
                    let func_index = self.next_uint32().unwrap();
                    visitor.fun_with_proto(func_index);
                }
                JSOp::BuiltinObject => {
                    let kind = self.next_uint8().unwrap();
                    visitor.builtin_object(kind);
                }
                JSOp::Call => {
                    let argc = self.next_uint16().unwrap();
                    visitor.call(argc);
                }
                JSOp::CallContent => {
                    let argc = self.next_uint16().unwrap();
                    visitor.call_content(argc);
                }
                JSOp::CallIter => {
                    let argc = self.next_uint16().unwrap();
                    visitor.call_iter(argc);
                }
                JSOp::CallContentIter => {
                    let argc = self.next_uint16().unwrap();
                    visitor.call_content_iter(argc);
                }
                JSOp::CallIgnoresRv => {
                    let argc = self.next_uint16().unwrap();
                    visitor.call_ignores_rv(argc);
                }
                JSOp::SpreadCall => visitor.spread_call(),
                JSOp::OptimizeSpreadCall => visitor.optimize_spread_call(),
                JSOp::Eval => {
                    let argc = self.next_uint16().unwrap();
                    visitor.eval(argc);
                }
                JSOp::SpreadEval => visitor.spread_eval(),
                JSOp::StrictEval => {
                    let argc = self.next_uint16().unwrap();
                    visitor.strict_eval(argc);
                }
                JSOp::StrictSpreadEval => visitor.strict_spread_eval(),
                JSOp::ImplicitThis => visitor.implicit_this(),
                JSOp::CallSiteObj => {
                    let object_index = self.next_uint32().unwrap();
                    visitor.call_site_obj(object_index);
                }
                JSOp::IsConstructing => visitor.is_constructing(),
                JSOp::New => {
                    let argc = self.next_uint16().unwrap();
                    visitor.new_(argc);
                }
                JSOp::NewContent => {
                    let argc = self.next_uint16().unwrap();
                    visitor.new_content(argc);
                }
                JSOp::SuperCall => {
                    let argc = self.next_uint16().unwrap();
                    visitor.super_call(argc);
                }
                JSOp::SpreadNew => visitor.spread_new(),
                JSOp::SpreadSuperCall => visitor.spread_super_call(),
                JSOp::SuperFun => visitor.super_fun(),
                JSOp::CheckThisReinit => visitor.check_this_reinit(),
                JSOp::Generator => visitor.generator(),
                JSOp::InitialYield => {
                    let resume_index = self.next_uint24().unwrap();
                    visitor.initial_yield(resume_index);
                }
                JSOp::AfterYield => {
                    let ic_index = self.next_uint32().unwrap();
                    visitor.after_yield(ic_index);
                }
                JSOp::FinalYieldRval => visitor.final_yield_rval(),
                JSOp::Yield => {
                    let resume_index = self.next_uint24().unwrap();
                    visitor.yield_(resume_index);
                }
                JSOp::IsGenClosing => visitor.is_gen_closing(),
                JSOp::AsyncAwait => visitor.async_await(),
                JSOp::AsyncResolve => visitor.async_resolve(),
                JSOp::AsyncReject => visitor.async_reject(),
                JSOp::Await => {
                    let resume_index = self.next_uint24().unwrap();
                    visitor.await_(resume_index);
                }
                JSOp::CanSkipAwait => visitor.can_skip_await(),
                JSOp::MaybeExtractAwaitValue => visitor.maybe_extract_await_value(),
                JSOp::ResumeKind => {
                    let resume_kind = self.next_uint8().unwrap();
                    visitor.resume_kind(resume_kind);
                }
                JSOp::CheckResumeKind => visitor.check_resume_kind(),
                JSOp::Resume => visitor.resume(),
                JSOp::JumpTarget => {
                    let ic_index = self.next_uint32().unwrap();
                    visitor.jump_target(ic_index);
                }
                JSOp::LoopHead => {
                    let ic_index = self.next_uint32().unwrap();
                    let depth_hint = self.next_uint8().unwrap();
                    visitor.loop_head(ic_index, depth_hint);
                }
                JSOp::Goto => {
                    let offset = self.next_int32().unwrap();
                    visitor.goto_(offset);
                }
                JSOp::JumpIfFalse => {
                    let forward_offset = self.next_int32().unwrap();
                    visitor.jump_if_false(forward_offset);
                }
                JSOp::JumpIfTrue => {
                    let offset = self.next_int32().unwrap();
                    visitor.jump_if_true(offset);
                }
                JSOp::And => {
                    let forward_offset = self.next_int32().unwrap();
                    visitor.and_(forward_offset);
                }
                JSOp::Or => {
                    let forward_offset = self.next_int32().unwrap();
                    visitor.or_(forward_offset);
                }
                JSOp::Coalesce => {
                    let forward_offset = self.next_int32().unwrap();
                    visitor.coalesce(forward_offset);
                }
                JSOp::Case => {
                    let forward_offset = self.next_int32().unwrap();
                    visitor.case_(forward_offset);
                }
                JSOp::Default => {
                    let forward_offset = self.next_int32().unwrap();
                    visitor.default_(forward_offset);
                }
                JSOp::TableSwitch => {
                    let default_offset = self.next_int32().unwrap();
                    let low = self.next_int32().unwrap();
                    let high = self.next_int32().unwrap();
                    let first_resume_index = usize::try_from(self.next_uint24().unwrap()).unwrap();
                    let count = usize::try_from(i64::from(high) - i64::from(low) + 1).unwrap();
                    let offsets =
                        &self.resume_offsets[first_resume_index..first_resume_index + count];
                    visitor.table_switch(default_offset, low, high, offsets);
                }
                JSOp::Return => visitor.return_(),
                JSOp::GetRval => visitor.get_rval(),
                JSOp::SetRval => visitor.set_rval(),
                JSOp::RetRval => visitor.ret_rval(),
                JSOp::CheckReturn => visitor.check_return(),
                JSOp::Throw => visitor.throw_(),
                JSOp::ThrowWithStack => visitor.throw_with_stack(),
                JSOp::CreateSuppressedError => visitor.create_suppressed_error(),
                JSOp::ThrowMsg => {
                    let msg_number = self.next_uint8().unwrap();
                    visitor.throw_msg(msg_number);
                }
                JSOp::ThrowSetConst => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.throw_set_const(name_index);
                }
                JSOp::Try => visitor.try_(),
                JSOp::TryDestructuring => visitor.try_destructuring(),
                JSOp::Exception => visitor.exception(),
                JSOp::ExceptionAndStack => visitor.exception_and_stack(),
                JSOp::Finally => visitor.finally(),
                JSOp::Uninitialized => visitor.uninitialized(),
                JSOp::InitLexical => {
                    let localno = self.next_uint24().unwrap();
                    visitor.init_lexical(localno);
                }
                JSOp::InitGLexical => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.init_g_lexical(name_index);
                }
                JSOp::InitAliasedLexical => {
                    let hops = self.next_uint16().unwrap();
                    let slot = self.next_uint24().unwrap();
                    visitor.init_aliased_lexical(hops, slot);
                }
                JSOp::CheckLexical => {
                    let localno = self.next_uint24().unwrap();
                    visitor.check_lexical(localno);
                }
                JSOp::CheckAliasedLexical => {
                    let hops = self.next_uint16().unwrap();
                    let slot = self.next_uint24().unwrap();
                    visitor.check_aliased_lexical(hops, slot);
                }
                JSOp::CheckThis => visitor.check_this(),
                JSOp::BindUnqualifiedGName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.bind_unqualified_g_name(name_index);
                }
                JSOp::BindUnqualifiedName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.bind_unqualified_name(name_index);
                }
                JSOp::BindName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.bind_name(name_index);
                }
                JSOp::GetName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.get_name(name_index);
                }
                JSOp::GetGName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.get_g_name(name_index);
                }
                JSOp::GetArg => {
                    let argno = self.next_uint16().unwrap();
                    visitor.get_arg(argno);
                }
                JSOp::GetFrameArg => {
                    let argno = self.next_uint16().unwrap();
                    visitor.get_frame_arg(argno);
                }
                JSOp::GetLocal => {
                    let localno = self.next_uint24().unwrap();
                    visitor.get_local(localno);
                }
                JSOp::ArgumentsLength => visitor.arguments_length(),
                JSOp::GetActualArg => visitor.get_actual_arg(),
                JSOp::GetAliasedVar => {
                    let hops = self.next_uint16().unwrap();
                    let slot = self.next_uint24().unwrap();
                    visitor.get_aliased_var(hops, slot);
                }
                JSOp::GetAliasedDebugVar => {
                    let hops = self.next_uint16().unwrap();
                    let slot = self.next_uint24().unwrap();
                    visitor.get_aliased_debug_var(hops, slot);
                }
                JSOp::GetImport => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.get_import(name_index);
                }
                JSOp::GetBoundName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.get_bound_name(name_index);
                }
                JSOp::GetIntrinsic => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.get_intrinsic(name_index);
                }
                JSOp::Callee => visitor.callee(),
                JSOp::EnvCallee => {
                    let num_hops = self.next_uint16().unwrap();
                    visitor.env_callee(num_hops);
                }
                JSOp::SetName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.set_name(name_index);
                }
                JSOp::StrictSetName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.strict_set_name(name_index);
                }
                JSOp::SetGName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.set_g_name(name_index);
                }
                JSOp::StrictSetGName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.strict_set_g_name(name_index);
                }
                JSOp::SetArg => {
                    let argno = self.next_uint16().unwrap();
                    visitor.set_arg(argno);
                }
                JSOp::SetLocal => {
                    let localno = self.next_uint24().unwrap();
                    visitor.set_local(localno);
                }
                JSOp::SetAliasedVar => {
                    let hops = self.next_uint16().unwrap();
                    let slot = self.next_uint24().unwrap();
                    visitor.set_aliased_var(hops, slot);
                }
                JSOp::SetIntrinsic => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.set_intrinsic(name_index);
                }
                JSOp::PushLexicalEnv => {
                    let lexical_scope_index = self.next_uint32().unwrap();
                    visitor.push_lexical_env(lexical_scope_index);
                }
                JSOp::PopLexicalEnv => visitor.pop_lexical_env(),
                JSOp::DebugLeaveLexicalEnv => visitor.debug_leave_lexical_env(),
                JSOp::RecreateLexicalEnv => {
                    let lexical_scope_index = self.next_uint32().unwrap();
                    visitor.recreate_lexical_env(lexical_scope_index);
                }
                JSOp::FreshenLexicalEnv => {
                    let lexical_scope_index = self.next_uint32().unwrap();
                    visitor.freshen_lexical_env(lexical_scope_index);
                }
                JSOp::PushClassBodyEnv => {
                    let lexical_scope_index = self.next_uint32().unwrap();
                    visitor.push_class_body_env(lexical_scope_index);
                }
                JSOp::PushVarEnv => {
                    let scope_index = self.next_uint32().unwrap();
                    visitor.push_var_env(scope_index);
                }
                JSOp::EnterWith => {
                    let static_with_index = self.next_uint32().unwrap();
                    visitor.enter_with(static_with_index);
                }
                JSOp::LeaveWith => visitor.leave_with(),
                JSOp::AddDisposable => {
                    let hint = self.next_uint8().unwrap();
                    visitor.add_disposable(hint);
                }
                JSOp::TakeDisposeCapability => visitor.take_dispose_capability(),
                JSOp::BindVar => visitor.bind_var(),
                JSOp::GlobalOrEvalDeclInstantiation => {
                    let last_fun = self.next_uint32().unwrap();
                    visitor.global_or_eval_decl_instantiation(last_fun);
                }
                JSOp::DelName => {
                    let name_index = self.next_uint32().unwrap();
                    visitor.del_name(name_index);
                }
                JSOp::Arguments => visitor.arguments(),
                JSOp::Rest => visitor.rest(),
                JSOp::FunctionThis => visitor.function_this(),
                JSOp::Pop => visitor.pop(),
                JSOp::PopN => {
                    let n = self.next_uint16().unwrap();
                    visitor.pop_n(n);
                }
                JSOp::Dup => visitor.dup(),
                JSOp::Dup2 => visitor.dup2(),
                JSOp::DupAt => {
                    let n = self.next_uint24().unwrap();
                    visitor.dup_at(n);
                }
                JSOp::Swap => visitor.swap(),
                JSOp::Pick => {
                    let n = self.next_uint8().unwrap();
                    visitor.pick(n);
                }
                JSOp::Unpick => {
                    let n = self.next_uint8().unwrap();
                    visitor.unpick(n);
                }
                JSOp::Nop => visitor.nop(),
                JSOp::Lineno => {
                    let lineno = self.next_uint32().unwrap();
                    visitor.lineno(lineno);
                }
                JSOp::NopDestructuring => visitor.nop_destructuring(),
                JSOp::ForceInterpreter => visitor.force_interpreter(),
                JSOp::DebugCheckSelfHosted => visitor.debug_check_self_hosted(),
                JSOp::Debugger => visitor.debugger(),
            }
            let consumed = u32::try_from(before - self.data.len()).unwrap();
            assert_eq!(consumed, op.len(), "bytecode length mismatch for {op:?}");
            pc += consumed;

            while let Some(note) = self.try_note_at_pc() {
                visitor.try_note(Pc::new(pc), &note);
            }
        }
        visitor
    }
}

pub trait OpcodeVisitor {
    fn before_op(&mut self, _pc: Pc, _op: JSOp, _nuses: usize, _ndefs: usize) {}
    fn try_note(&mut self, _pc: Pc, _note: &TryNote) {}
    fn undefined(&mut self) {}
    fn null(&mut self) {}
    fn false_(&mut self) {}
    fn true_(&mut self) {}
    fn int32(&mut self, _value: u32) {}
    fn zero(&mut self) {}
    fn one(&mut self) {}
    fn int8(&mut self, _value: u8) {}
    fn uint16(&mut self, _value: u16) {}
    fn uint24(&mut self, _value: u32) {}
    fn double(&mut self, _value: u64) {}
    fn bigint(&mut self, _bigint_index: u32) {}
    fn string(&mut self, _atom_index: u32) {}
    fn symbol(&mut self, _code: u8) {}
    fn void(&mut self) {}
    fn typeof_(&mut self) {}
    fn typeof_expr(&mut self) {}
    fn typeof_eq(&mut self, _operand: u8) {}
    fn pos(&mut self) {}
    fn neg(&mut self) {}
    fn bit_not(&mut self) {}
    fn not_(&mut self) {}
    fn bit_or(&mut self) {}
    fn bit_xor(&mut self) {}
    fn bit_and(&mut self) {}
    fn eq(&mut self) {}
    fn ne(&mut self) {}
    fn strict_eq(&mut self) {}
    fn strict_ne(&mut self) {}
    fn strict_constant_eq(&mut self, _operand: u16) {}
    fn strict_constant_ne(&mut self, _operand: u16) {}
    fn lt(&mut self) {}
    fn gt(&mut self) {}
    fn le(&mut self) {}
    fn ge(&mut self) {}
    fn instanceof(&mut self) {}
    fn in_(&mut self) {}
    fn lsh(&mut self) {}
    fn rsh(&mut self) {}
    fn ursh(&mut self) {}
    fn add(&mut self) {}
    fn sub(&mut self) {}
    fn inc(&mut self) {}
    fn dec(&mut self) {}
    fn mul(&mut self) {}
    fn div(&mut self) {}
    fn mod_(&mut self) {}
    fn pow(&mut self) {}
    fn nop_is_assign_op(&mut self) {}
    fn to_property_key(&mut self) {}
    fn to_numeric(&mut self) {}
    fn to_string(&mut self) {}
    fn is_null_or_undefined(&mut self) {}
    fn global_this(&mut self) {}
    fn non_syntactic_global_this(&mut self) {}
    fn new_target(&mut self) {}
    fn dynamic_import(&mut self) {}
    fn import_meta(&mut self) {}
    fn new_init(&mut self, _property_count: u8) {}
    fn new_object(&mut self, _shape_index: u32) {}
    fn object(&mut self, _object_index: u32) {}
    fn obj_with_proto(&mut self) {}
    fn init_prop(&mut self, _name_index: u32) {}
    fn init_hidden_prop(&mut self, _name_index: u32) {}
    fn init_locked_prop(&mut self, _name_index: u32) {}
    fn init_elem(&mut self) {}
    fn init_hidden_elem(&mut self) {}
    fn init_locked_elem(&mut self) {}
    fn init_prop_getter(&mut self, _name_index: u32) {}
    fn init_hidden_prop_getter(&mut self, _name_index: u32) {}
    fn init_elem_getter(&mut self) {}
    fn init_hidden_elem_getter(&mut self) {}
    fn init_prop_setter(&mut self, _name_index: u32) {}
    fn init_hidden_prop_setter(&mut self, _name_index: u32) {}
    fn init_elem_setter(&mut self) {}
    fn init_hidden_elem_setter(&mut self) {}
    fn get_prop(&mut self, _name_index: u32) {}
    fn get_elem(&mut self) {}
    fn set_prop(&mut self, _name_index: u32) {}
    fn strict_set_prop(&mut self, _name_index: u32) {}
    fn set_elem(&mut self) {}
    fn strict_set_elem(&mut self) {}
    fn del_prop(&mut self, _name_index: u32) {}
    fn strict_del_prop(&mut self, _name_index: u32) {}
    fn del_elem(&mut self) {}
    fn strict_del_elem(&mut self) {}
    fn has_own(&mut self) {}
    fn check_private_field(&mut self, _throw_condition: u8, _msg_kind: u8) {}
    fn new_private_name(&mut self, _name_index: u32) {}
    fn super_base(&mut self) {}
    fn get_prop_super(&mut self, _name_index: u32) {}
    fn get_elem_super(&mut self) {}
    fn set_prop_super(&mut self, _name_index: u32) {}
    fn strict_set_prop_super(&mut self, _name_index: u32) {}
    fn set_elem_super(&mut self) {}
    fn strict_set_elem_super(&mut self) {}
    fn iter(&mut self) {}
    fn more_iter(&mut self) {}
    fn is_no_iter(&mut self) {}
    fn end_iter(&mut self) {}
    fn close_iter(&mut self, _kind: u8) {}
    fn optimize_get_iterator(&mut self) {}
    fn check_is_obj(&mut self, _kind: u8) {}
    fn check_obj_coercible(&mut self) {}
    fn to_async_iter(&mut self) {}
    fn mutate_proto(&mut self) {}
    fn new_array(&mut self, _length: u32) {}
    fn init_elem_array(&mut self, _index: u32) {}
    fn init_elem_inc(&mut self) {}
    fn hole(&mut self) {}
    fn reg_exp(&mut self, _regexp_index: u32) {}
    fn lambda(&mut self, _func_index: u32) {}
    fn set_fun_name(&mut self, _prefix_kind: u8) {}
    fn init_home_object(&mut self) {}
    fn check_class_heritage(&mut self) {}
    fn fun_with_proto(&mut self, _func_index: u32) {}
    fn builtin_object(&mut self, _kind: u8) {}
    fn call(&mut self, _argc: u16) {}
    fn call_content(&mut self, _argc: u16) {}
    fn call_iter(&mut self, _argc: u16) {}
    fn call_content_iter(&mut self, _argc: u16) {}
    fn call_ignores_rv(&mut self, _argc: u16) {}
    fn spread_call(&mut self) {}
    fn optimize_spread_call(&mut self) {}
    fn eval(&mut self, _argc: u16) {}
    fn spread_eval(&mut self) {}
    fn strict_eval(&mut self, _argc: u16) {}
    fn strict_spread_eval(&mut self) {}
    fn implicit_this(&mut self) {}
    fn call_site_obj(&mut self, _object_index: u32) {}
    fn is_constructing(&mut self) {}
    fn new_(&mut self, _argc: u16) {}
    fn new_content(&mut self, _argc: u16) {}
    fn super_call(&mut self, _argc: u16) {}
    fn spread_new(&mut self) {}
    fn spread_super_call(&mut self) {}
    fn super_fun(&mut self) {}
    fn check_this_reinit(&mut self) {}
    fn generator(&mut self) {}
    fn initial_yield(&mut self, _resume_index: u32) {}
    fn after_yield(&mut self, _ic_index: u32) {}
    fn final_yield_rval(&mut self) {}
    fn yield_(&mut self, _resume_index: u32) {}
    fn is_gen_closing(&mut self) {}
    fn async_await(&mut self) {}
    fn async_resolve(&mut self) {}
    fn async_reject(&mut self) {}
    fn await_(&mut self, _resume_index: u32) {}
    fn can_skip_await(&mut self) {}
    fn maybe_extract_await_value(&mut self) {}
    fn resume_kind(&mut self, _resume_kind: u8) {}
    fn check_resume_kind(&mut self) {}
    fn resume(&mut self) {}
    fn jump_target(&mut self, _ic_index: u32) {}
    fn loop_head(&mut self, _ic_index: u32, _depth_hint: u8) {}
    fn goto_(&mut self, _offset: i32) {}
    fn jump_if_false(&mut self, _forward_offset: i32) {}
    fn jump_if_true(&mut self, _offset: i32) {}
    fn and_(&mut self, _forward_offset: i32) {}
    fn or_(&mut self, _forward_offset: i32) {}
    fn coalesce(&mut self, _forward_offset: i32) {}
    fn case_(&mut self, _forward_offset: i32) {}
    fn default_(&mut self, _forward_offset: i32) {}
    fn table_switch(&mut self, _default_offset: i32, _low: i32, _high: i32, _offsets: &[Pc]) {}
    fn return_(&mut self) {}
    fn get_rval(&mut self) {}
    fn set_rval(&mut self) {}
    fn ret_rval(&mut self) {}
    fn check_return(&mut self) {}
    fn throw_(&mut self) {}
    fn throw_with_stack(&mut self) {}
    fn create_suppressed_error(&mut self) {}
    fn throw_msg(&mut self, _msg_number: u8) {}
    fn throw_set_const(&mut self, _name_index: u32) {}
    fn try_(&mut self) {}
    fn try_destructuring(&mut self) {}
    fn exception(&mut self) {}
    fn exception_and_stack(&mut self) {}
    fn finally(&mut self) {}
    fn uninitialized(&mut self) {}
    fn init_lexical(&mut self, _localno: u32) {}
    fn init_g_lexical(&mut self, _name_index: u32) {}
    fn init_aliased_lexical(&mut self, _hops: u16, _slot: u32) {}
    fn check_lexical(&mut self, _localno: u32) {}
    fn check_aliased_lexical(&mut self, _hops: u16, _slot: u32) {}
    fn check_this(&mut self) {}
    fn bind_unqualified_g_name(&mut self, _name_index: u32) {}
    fn bind_unqualified_name(&mut self, _name_index: u32) {}
    fn bind_name(&mut self, _name_index: u32) {}
    fn get_name(&mut self, _name_index: u32) {}
    fn get_g_name(&mut self, _name_index: u32) {}
    fn get_arg(&mut self, _argno: u16) {}
    fn get_frame_arg(&mut self, _argno: u16) {}
    fn get_local(&mut self, _localno: u32) {}
    fn arguments_length(&mut self) {}
    fn get_actual_arg(&mut self) {}
    fn get_aliased_var(&mut self, _hops: u16, _slot: u32) {}
    fn get_aliased_debug_var(&mut self, _hops: u16, _slot: u32) {}
    fn get_import(&mut self, _name_index: u32) {}
    fn get_bound_name(&mut self, _name_index: u32) {}
    fn get_intrinsic(&mut self, _name_index: u32) {}
    fn callee(&mut self) {}
    fn env_callee(&mut self, _num_hops: u16) {}
    fn set_name(&mut self, _name_index: u32) {}
    fn strict_set_name(&mut self, _name_index: u32) {}
    fn set_g_name(&mut self, _name_index: u32) {}
    fn strict_set_g_name(&mut self, _name_index: u32) {}
    fn set_arg(&mut self, _argno: u16) {}
    fn set_local(&mut self, _localno: u32) {}
    fn set_aliased_var(&mut self, _hops: u16, _slot: u32) {}
    fn set_intrinsic(&mut self, _name_index: u32) {}
    fn push_lexical_env(&mut self, _lexical_scope_index: u32) {}
    fn pop_lexical_env(&mut self) {}
    fn debug_leave_lexical_env(&mut self) {}
    fn recreate_lexical_env(&mut self, _lexical_scope_index: u32) {}
    fn freshen_lexical_env(&mut self, _lexical_scope_index: u32) {}
    fn push_class_body_env(&mut self, _lexical_scope_index: u32) {}
    fn push_var_env(&mut self, _scope_index: u32) {}
    fn enter_with(&mut self, _static_with_index: u32) {}
    fn leave_with(&mut self) {}
    fn add_disposable(&mut self, _hint: u8) {}
    fn take_dispose_capability(&mut self) {}
    fn bind_var(&mut self) {}
    fn global_or_eval_decl_instantiation(&mut self, _last_fun: u32) {}
    fn del_name(&mut self, _name_index: u32) {}
    fn arguments(&mut self) {}
    fn rest(&mut self) {}
    fn function_this(&mut self) {}
    fn pop(&mut self) {}
    fn pop_n(&mut self, _n: u16) {}
    fn dup(&mut self) {}
    fn dup2(&mut self) {}
    fn dup_at(&mut self, _n: u32) {}
    fn swap(&mut self) {}
    fn pick(&mut self, _n: u8) {}
    fn unpick(&mut self, _n: u8) {}
    fn nop(&mut self) {}
    fn lineno(&mut self, _lineno: u32) {}
    fn nop_destructuring(&mut self) {}
    fn force_interpreter(&mut self) {}
    fn debug_check_self_hosted(&mut self) {}
    fn debugger(&mut self) {}
}
