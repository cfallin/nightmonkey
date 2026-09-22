/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! irregexp-bytecode -> Wasm translator.
//!
//! Translates one irregexp bytecode program (the interpreter isa in
//! `js/src/irregexp/imported/regexp-bytecodes.h`) into a standalone Wasm
//! function equivalent to one `RawMatch<Char>` activation: single-match,
//! against a flat subject already resident in linear memory. The engine-side
//! global-match loop, string flattening, and interrupt handling stay in C++.
//!
//! Execution-model mapping:
//! - bytecode pc        -> CFG blocks (labels are absolute byte offsets)
//! - current / current_char / registers / backtrack sp / backtrack count
//!                      -> SSA state threaded as blockparams on every label
//! - backtrack stack    -> caller-provided i32 buffer in linear memory; the
//!   values PUSH_BT pushes are *dense label ids* (not byte offsets); POP_BT
//!   branches to a Select (br_table) dispatcher over those ids. PUSH_CP /
//!   PUSH_REGISTER values pass through untouched, so stack-pointer
//!   save/restore via registers is oblivious to the substitution.
//!
//! Fallback contract: any construct we cannot translate returns Err (the
//! regex is simply dropped from the AOT table), and the compiled matcher
//! returns retry (-2) on backtrack-budget or stack exhaustion so the caller
//! reruns the match in the bytecode interpreter. Never a miscompile.
//!
//! ABI (all i32, single i32 result; see the night runtime's RegexFn):
//!   (input_ptr, input_len_chars, start_pos, output_regs_ptr,
//!    bt_stack_base, bt_stack_capacity_elems) -> status
//! status: 0 = failure (no match), 1 = success (output regs filled),
//! -2 = retry (rerun in the interpreter).

use crate::constants::{BT_BUDGET, MAX_BT_LABELS, MAX_BYTECODE_LEN};
use std::collections::HashMap;

use waffle::{
    Block, BlockTarget, Func, FunctionBody, Memory, MemoryArg, Module, Operator, Signature,
    Terminator, Type, Value, ValueDef,
};

pub const REGEX_STATUS_FAILURE: u32 = 0;
pub const REGEX_STATUS_SUCCESS: u32 = 1;
pub const REGEX_STATUS_RETRY: u32 = 0xFFFF_FFFE; // -2

const MAX_REGISTERS: u32 = 128;

// Bytecode opcodes (regexp-bytecodes.h BYTECODE_ITERATOR).
const BC_BREAK: u8 = 0;
const BC_PUSH_CP: u8 = 1;
const BC_PUSH_BT: u8 = 2;
const BC_SET_REGISTER_TO_CP: u8 = 3;
const BC_SET_CP_TO_REGISTER: u8 = 4;
const BC_SET_REGISTER_TO_SP: u8 = 5;
const BC_SET_SP_TO_REGISTER: u8 = 6;
const BC_SET_REGISTER: u8 = 7;
const BC_ADVANCE_REGISTER: u8 = 8;
const BC_POP_CP: u8 = 9;
const BC_POP_BT: u8 = 10;
const BC_POP_REGISTER: u8 = 11;
const BC_FAIL: u8 = 12;
const BC_SUCCEED: u8 = 13;
const BC_ADVANCE_CP: u8 = 14;
const BC_GOTO: u8 = 15;
const BC_LOAD_CURRENT_CHAR: u8 = 16;
const BC_CHECK_CHAR: u8 = 17;
const BC_CHECK_NOT_CHAR: u8 = 18;
const BC_AND_CHECK_CHAR: u8 = 19;
const BC_AND_CHECK_NOT_CHAR: u8 = 20;
const BC_MINUS_AND_CHECK_NOT_CHAR: u8 = 21;
const BC_CHECK_CHAR_IN_RANGE: u8 = 22;
const BC_CHECK_CHAR_NOT_IN_RANGE: u8 = 23;
const BC_CHECK_LT: u8 = 24;
const BC_CHECK_GT: u8 = 25;
const BC_CHECK_NOT_BACK_REF: u8 = 26;
const BC_CHECK_NOT_BACK_REF_NO_CASE: u8 = 27;
const BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE: u8 = 28;
const BC_CHECK_NOT_BACK_REF_BACKWARD: u8 = 29;
const BC_CHECK_NOT_BACK_REF_NO_CASE_BACKWARD: u8 = 30;
const BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE_BACKWARD: u8 = 31;
const BC_CHECK_NOT_REGS_EQUAL: u8 = 32;
const BC_CHECK_REGISTER_LT: u8 = 33;
const BC_CHECK_REGISTER_GE: u8 = 34;
const BC_CHECK_REGISTER_EQ_POS: u8 = 35;
const BC_CHECK_AT_START: u8 = 36;
const BC_CHECK_NOT_AT_START: u8 = 37;
const BC_CHECK_FIXED_LENGTH: u8 = 38;
const BC_SET_CURRENT_POSITION_FROM_END: u8 = 39;
const BC_PUSH_REGISTER: u8 = 40;
const BC_LOAD_CURRENT_CHAR_UNCHECKED: u8 = 41;
const BC_CHECK_BIT_IN_TABLE: u8 = 42;
const BC_LOAD_2_CURRENT_CHARS: u8 = 43;
const BC_LOAD_2_CURRENT_CHARS_UNCHECKED: u8 = 44;
const BC_LOAD_4_CURRENT_CHARS: u8 = 45;
const BC_LOAD_4_CURRENT_CHARS_UNCHECKED: u8 = 46;
const BC_CHECK_4_CHARS: u8 = 47;
const BC_CHECK_NOT_4_CHARS: u8 = 48;
const BC_AND_CHECK_4_CHARS: u8 = 49;
const BC_AND_CHECK_NOT_4_CHARS: u8 = 50;
const BC_ADVANCE_CP_AND_GOTO: u8 = 51;
const BC_CHECK_CURRENT_POSITION: u8 = 52;
const BC_SKIP_UNTIL_BIT_IN_TABLE: u8 = 53;
const BC_SKIP_UNTIL_CHAR_AND: u8 = 54;
const BC_SKIP_UNTIL_CHAR: u8 = 55;
const BC_SKIP_UNTIL_CHAR_POS_CHECKED: u8 = 56;
const BC_SKIP_UNTIL_CHAR_OR_CHAR: u8 = 57;
const BC_SKIP_UNTIL_GT_OR_NOT_BIT_IN_TABLE: u8 = 58;

const BC_COUNT: u8 = 59;

const BC_LENGTHS: [usize; BC_COUNT as usize] = [
    4,  // BREAK
    4,  // PUSH_CP
    8,  // PUSH_BT
    8,  // SET_REGISTER_TO_CP
    4,  // SET_CP_TO_REGISTER
    4,  // SET_REGISTER_TO_SP
    4,  // SET_SP_TO_REGISTER
    8,  // SET_REGISTER
    8,  // ADVANCE_REGISTER
    4,  // POP_CP
    4,  // POP_BT
    4,  // POP_REGISTER
    4,  // FAIL
    4,  // SUCCEED
    4,  // ADVANCE_CP
    8,  // GOTO
    8,  // LOAD_CURRENT_CHAR
    8,  // CHECK_CHAR
    8,  // CHECK_NOT_CHAR
    12, // AND_CHECK_CHAR
    12, // AND_CHECK_NOT_CHAR
    12, // MINUS_AND_CHECK_NOT_CHAR
    12, // CHECK_CHAR_IN_RANGE
    12, // CHECK_CHAR_NOT_IN_RANGE
    8,  // CHECK_LT
    8,  // CHECK_GT
    8,  // CHECK_NOT_BACK_REF
    8,  // CHECK_NOT_BACK_REF_NO_CASE
    8,  // CHECK_NOT_BACK_REF_NO_CASE_UNICODE
    8,  // CHECK_NOT_BACK_REF_BACKWARD
    8,  // CHECK_NOT_BACK_REF_NO_CASE_BACKWARD
    8,  // CHECK_NOT_BACK_REF_NO_CASE_UNICODE_BACKWARD
    12, // CHECK_NOT_REGS_EQUAL
    12, // CHECK_REGISTER_LT
    12, // CHECK_REGISTER_GE
    8,  // CHECK_REGISTER_EQ_POS
    8,  // CHECK_AT_START
    8,  // CHECK_NOT_AT_START
    8,  // CHECK_FIXED_LENGTH
    4,  // SET_CURRENT_POSITION_FROM_END
    4,  // PUSH_REGISTER
    4,  // LOAD_CURRENT_CHAR_UNCHECKED
    24, // CHECK_BIT_IN_TABLE
    8,  // LOAD_2_CURRENT_CHARS
    4,  // LOAD_2_CURRENT_CHARS_UNCHECKED
    8,  // LOAD_4_CURRENT_CHARS
    4,  // LOAD_4_CURRENT_CHARS_UNCHECKED
    12, // CHECK_4_CHARS
    12, // CHECK_NOT_4_CHARS
    16, // AND_CHECK_4_CHARS
    16, // AND_CHECK_NOT_4_CHARS
    8,  // ADVANCE_CP_AND_GOTO
    8,  // CHECK_CURRENT_POSITION
    32, // SKIP_UNTIL_BIT_IN_TABLE
    24, // SKIP_UNTIL_CHAR_AND
    16, // SKIP_UNTIL_CHAR
    20, // SKIP_UNTIL_CHAR_POS_CHECKED
    20, // SKIP_UNTIL_CHAR_OR_CHAR
    32, // SKIP_UNTIL_GT_OR_NOT_BIT_IN_TABLE
];

pub struct RegexTranslateInput<'a> {
    pub bytecode: &'a [u8],
    /// Two-byte (UC16) subject variant.
    pub wide: bool,
    /// Total register file size (RegExpShared::getMaxRegisters()).
    pub total_regs: u32,
    /// Output register count = 2 * pairCount (whole match + captures).
    pub output_regs: u32,
}

struct Insn {
    op: u8,
    /// First 32-bit word (opcode byte + packed 24-bit arg).
    w0: u32,
    off: usize,
}

fn rd32(bc: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([bc[off], bc[off + 1], bc[off + 2], bc[off + 3]])
}
fn rd16(bc: &[u8], off: usize) -> u32 {
    u16::from_le_bytes([bc[off], bc[off + 1]]) as u32
}
fn packed_s(w0: u32) -> i32 {
    (w0 as i32) >> 8
}
fn packed_u(w0: u32) -> u32 {
    w0 >> 8
}

/// The byte offsets of every Label operand of `insn` within the encoding,
/// split into (jump_targets, pushed_bt_targets).
fn label_operand_offsets(op: u8) -> (&'static [usize], bool) {
    // (offsets of Label operands relative to insn start, is_push_bt)
    match op {
        BC_PUSH_BT => (&[4], true),
        BC_GOTO | BC_ADVANCE_CP_AND_GOTO => (&[4], false),
        BC_LOAD_CURRENT_CHAR
        | BC_CHECK_CHAR
        | BC_CHECK_NOT_CHAR
        | BC_CHECK_LT
        | BC_CHECK_GT
        | BC_CHECK_NOT_BACK_REF
        | BC_CHECK_NOT_BACK_REF_NO_CASE
        | BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE
        | BC_CHECK_NOT_BACK_REF_BACKWARD
        | BC_CHECK_NOT_BACK_REF_NO_CASE_BACKWARD
        | BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE_BACKWARD
        | BC_CHECK_REGISTER_EQ_POS
        | BC_CHECK_AT_START
        | BC_CHECK_NOT_AT_START
        | BC_CHECK_FIXED_LENGTH
        | BC_CHECK_BIT_IN_TABLE
        | BC_LOAD_2_CURRENT_CHARS
        | BC_LOAD_4_CURRENT_CHARS
        | BC_CHECK_CURRENT_POSITION => (&[4], false),
        BC_AND_CHECK_CHAR
        | BC_AND_CHECK_NOT_CHAR
        | BC_MINUS_AND_CHECK_NOT_CHAR
        | BC_CHECK_CHAR_IN_RANGE
        | BC_CHECK_CHAR_NOT_IN_RANGE
        | BC_CHECK_NOT_REGS_EQUAL
        | BC_CHECK_REGISTER_LT
        | BC_CHECK_REGISTER_GE
        | BC_CHECK_4_CHARS
        | BC_CHECK_NOT_4_CHARS => (&[8], false),
        BC_AND_CHECK_4_CHARS | BC_AND_CHECK_NOT_4_CHARS => (&[12], false),
        BC_SKIP_UNTIL_CHAR => (&[8, 12], false),
        BC_SKIP_UNTIL_CHAR_AND => (&[16, 20], false),
        BC_SKIP_UNTIL_CHAR_POS_CHECKED => (&[12, 16], false),
        BC_SKIP_UNTIL_CHAR_OR_CHAR => (&[12, 16], false),
        BC_SKIP_UNTIL_BIT_IN_TABLE | BC_SKIP_UNTIL_GT_OR_NOT_BIT_IN_TABLE => (&[24, 28], false),
        _ => (&[], false),
    }
}

/// Ends the linear flow (everything after it, up to the next leader, is
/// unreachable).
fn is_unconditional(op: u8) -> bool {
    matches!(
        op,
        BC_BREAK
            | BC_POP_BT
            | BC_FAIL
            | BC_SUCCEED
            | BC_GOTO
            | BC_ADVANCE_CP_AND_GOTO
            | BC_SKIP_UNTIL_BIT_IN_TABLE
            | BC_SKIP_UNTIL_CHAR_AND
            | BC_SKIP_UNTIL_CHAR
            | BC_SKIP_UNTIL_CHAR_POS_CHECKED
            | BC_SKIP_UNTIL_CHAR_OR_CHAR
            | BC_SKIP_UNTIL_GT_OR_NOT_BIT_IN_TABLE
    )
}

/// State vector layout: [current, current_char, sp, bt_count, reg0..regN-1].
struct Ctx {
    body: FunctionBody,
    cur: Block,
    mem: Memory,
    wide: bool,
    nregs: u32,
    output_regs: u32,
    ci_helper: Option<Func>,
    // Immutable entry params.
    input: Value,
    len: Value,
    start: Value,
    out_ptr: Value,
    bt_base: Value,
    bt_cap: Value,
    // Current SSA state.
    st: Vec<Value>,
    // Leader blocks (offset -> block); each has 4 + nregs i32 params.
    blocks: HashMap<u32, Block>,
    // PUSH_BT target offset -> dense id, and the reverse.
    bt_ids: HashMap<u32, u32>,
    bt_targets: Vec<u32>,
    // Backtrack dispatcher, created lazily: (block, id param, state params).
    dispatch: Option<(Block, Value, Vec<Value>)>,
    retry_blk: Option<Block>,
}

impl Ctx {
    // ---- value construction ------------------------------------------

    fn i32c(&mut self, value: u32) -> Value {
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Const { value },
            Default::default(),
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    fn i64c(&mut self, value: u64) -> Value {
        let ty = self.body.single_type_list(Type::I64);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I64Const { value },
            Default::default(),
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    fn unop(&mut self, op: Operator, a: Value, ty: Type) -> Value {
        let args = self.body.arg_pool.single(a);
        let tys = self.body.single_type_list(ty);
        let v = self.body.add_value(ValueDef::Operator(op, args, tys));
        self.body.append_to_block(self.cur, v);
        v
    }

    fn binop(&mut self, op: Operator, a: Value, b: Value, ty: Type) -> Value {
        let args = self.body.arg_pool.double(a, b);
        let tys = self.body.single_type_list(ty);
        let v = self.body.add_value(ValueDef::Operator(op, args, tys));
        self.body.append_to_block(self.cur, v);
        v
    }

    fn add(&mut self, a: Value, b: Value) -> Value {
        self.binop(Operator::I32Add, a, b, Type::I32)
    }

    fn addk(&mut self, a: Value, k: i32) -> Value {
        if k == 0 {
            return a;
        }
        let kv = self.i32c(k as u32);
        self.add(a, kv)
    }

    /// Out-of-bounds test for an `n`-char span starting at `pos`:
    /// `pos + n > len || pos < 0` (signed), returning the combined flag.
    fn oob_span(&mut self, pos: Value, n: i32) -> Value {
        let posn = self.addk(pos, n);
        let over = self.binop(Operator::I32GtS, posn, self.len, Type::I32);
        let z = self.i32c(0);
        let neg = self.binop(Operator::I32LtS, pos, z, Type::I32);
        self.binop(Operator::I32Or, over, neg, Type::I32)
    }

    fn call_i32(&mut self, func: Func, args: &[Value]) -> Value {
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
    }

    fn mem_arg(&self, align: u32, offset: u32) -> MemoryArg {
        MemoryArg {
            align,
            offset,
            memory: self.mem,
        }
    }

    fn load_i32(&mut self, addr: Value, offset: u32) -> Value {
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Load {
                memory: self.mem_arg(2, offset),
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    fn store_i32(&mut self, addr: Value, offset: u32, value: Value) {
        let args = self.body.arg_pool.double(addr, value);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Store {
                memory: self.mem_arg(2, offset),
            },
            args,
            Default::default(),
        ));
        self.body.append_to_block(self.cur, v);
    }

    fn load8(&mut self, addr: Value) -> Value {
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Load8U {
                memory: self.mem_arg(0, 0),
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    fn load16(&mut self, addr: Value) -> Value {
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Load16U {
                memory: self.mem_arg(0, 0),
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    fn load32_raw(&mut self, addr: Value) -> Value {
        let args = self.body.arg_pool.single(addr);
        let ty = self.body.single_type_list(Type::I32);
        let v = self.body.add_value(ValueDef::Operator(
            Operator::I32Load {
                memory: self.mem_arg(0, 0),
            },
            args,
            ty,
        ));
        self.body.append_to_block(self.cur, v);
        v
    }

    // ---- subject access ------------------------------------------------

    /// Address of subject char at position `pos` (a char index).
    fn char_addr(&mut self, pos: Value) -> Value {
        if self.wide {
            let two = self.i32c(2);
            let byte_off = self.binop(Operator::I32Mul, pos, two, Type::I32);
            self.add(self.input_v(), byte_off)
        } else {
            self.add(self.input_v(), pos)
        }
    }

    fn input_v(&self) -> Value {
        self.input
    }

    /// Load one subject char at `pos`.
    fn load_char(&mut self, pos: Value) -> Value {
        let a = self.char_addr(pos);
        if self.wide {
            self.load16(a)
        } else {
            self.load8(a)
        }
    }

    /// Load 2 subject chars at `pos` packed little-endian (matches the
    /// interpreter's `c | next << (8*sizeof(Char))`).
    fn load_2_chars(&mut self, pos: Value) -> Value {
        let a = self.char_addr(pos);
        if self.wide {
            self.load32_raw(a)
        } else {
            self.load16(a)
        }
    }

    /// Load 4 subject chars (latin1 only) packed little-endian.
    fn load_4_chars(&mut self, pos: Value) -> Value {
        let a = self.char_addr(pos);
        self.load32_raw(a)
    }

    // ---- state helpers ---------------------------------------------------

    fn cur_pos(&self) -> Value {
        self.st[0]
    }
    fn cur_char(&self) -> Value {
        self.st[1]
    }
    fn sp(&self) -> Value {
        self.st[2]
    }
    fn btcnt(&self) -> Value {
        self.st[3]
    }
    fn reg(&self, i: u32) -> Value {
        self.st[4 + i as usize]
    }
    fn set_pos(&mut self, v: Value) {
        self.st[0] = v;
    }
    fn set_char(&mut self, v: Value) {
        self.st[1] = v;
    }
    fn set_sp(&mut self, v: Value) {
        self.st[2] = v;
    }
    fn set_btcnt(&mut self, v: Value) {
        self.st[3] = v;
    }
    fn set_reg(&mut self, i: u32, v: Value) {
        self.st[4 + i as usize] = v;
    }

    fn check_reg(&self, i: u32) -> Result<(), String> {
        if i >= self.nregs {
            Err(format!("register index {} out of range", i))
        } else {
            Ok(())
        }
    }

    // ---- control flow ----------------------------------------------------

    fn target(&self, off: u32) -> Result<BlockTarget, String> {
        let block = *self
            .blocks
            .get(&off)
            .ok_or_else(|| format!("jump to non-leader offset {}", off))?;
        Ok(BlockTarget {
            block,
            args: self.st.clone(),
        })
    }

    /// `CondBr(cond) ? goto label(off) : fall through` (the universal
    /// check-op shape). Continues emission in a fresh anonymous block.
    fn cond_jump(&mut self, cond: Value, off: u32) -> Result<(), String> {
        let t = self.target(off)?;
        let f = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond,
                if_true: t,
                if_false: BlockTarget {
                    block: f,
                    args: vec![],
                },
            },
        );
        self.cur = f;
        Ok(())
    }

    /// Same but the *false* edge jumps and the true edge falls through.
    fn cond_jump_inv(&mut self, cond: Value, off: u32) -> Result<(), String> {
        let t = self.target(off)?;
        let f = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond,
                if_true: BlockTarget {
                    block: f,
                    args: vec![],
                },
                if_false: t,
            },
        );
        self.cur = f;
        Ok(())
    }

    /// Branch to `off` on the check `cond` for a paired positive/negative
    /// bytecode: the positive op jumps when `cond` holds, the negative op
    /// when it does not.
    fn cond_jump_polar(&mut self, positive: bool, cond: Value, off: u32) -> Result<(), String> {
        if positive {
            self.cond_jump(cond, off)
        } else {
            self.cond_jump_inv(cond, off)
        }
    }

    fn goto(&mut self, off: u32) -> Result<(), String> {
        let t = self.target(off)?;
        self.body
            .set_terminator(self.cur, Terminator::Br { target: t });
        Ok(())
    }

    fn ret(&mut self, code: u32) {
        let v = self.i32c(code);
        self.body
            .set_terminator(self.cur, Terminator::Return { values: vec![v] });
    }

    fn retry_target(&mut self) -> BlockTarget {
        let blk = match self.retry_blk {
            Some(b) => b,
            None => {
                let b = self.body.add_block();
                let saved = self.cur;
                self.cur = b;
                self.ret(REGEX_STATUS_RETRY);
                self.cur = saved;
                self.retry_blk = Some(b);
                b
            }
        };
        BlockTarget {
            block: blk,
            args: vec![],
        }
    }

    /// Branch to `retry` when `cond` holds; else continue.
    fn retry_if(&mut self, cond: Value) {
        let t = self.retry_target();
        let f = self.body.add_block();
        self.body.set_terminator(
            self.cur,
            Terminator::CondBr {
                cond,
                if_true: t,
                if_false: BlockTarget {
                    block: f,
                    args: vec![],
                },
            },
        );
        self.cur = f;
    }

    // ---- backtrack stack ---------------------------------------------------

    /// Push `v` (an arbitrary i32) onto the backtrack stack.
    fn bt_push(&mut self, v: Value) {
        let ovf = self.binop(Operator::I32GeU, self.sp(), self.bt_cap, Type::I32);
        self.retry_if(ovf);
        let four = self.i32c(4);
        let off = self.binop(Operator::I32Mul, self.sp(), four, Type::I32);
        let addr = self.add(self.bt_base, off);
        self.store_i32(addr, 0, v);
        let sp1 = self.addk(self.sp(), 1);
        self.set_sp(sp1);
    }

    /// Pop the top of the backtrack stack.
    fn bt_pop(&mut self) -> Value {
        let sp1 = self.addk(self.sp(), -1);
        self.set_sp(sp1);
        let four = self.i32c(4);
        let off = self.binop(Operator::I32Mul, sp1, four, Type::I32);
        let addr = self.add(self.bt_base, off);
        self.load_i32(addr, 0)
    }

    fn bt_peek(&mut self) -> Value {
        let sp1 = self.addk(self.sp(), -1);
        let four = self.i32c(4);
        let off = self.binop(Operator::I32Mul, sp1, four, Type::I32);
        let addr = self.add(self.bt_base, off);
        self.load_i32(addr, 0)
    }

    // ---- bit tables ----------------------------------------------------------

    /// Test bit `current_char & 127` of the inline 16-byte table (branch-free).
    fn bit_in_table(&mut self, table: &[u8]) -> Value {
        let lo = u64::from_le_bytes(table[0..8].try_into().unwrap());
        let hi = u64::from_le_bytes(table[8..16].try_into().unwrap());
        let c127 = self.i32c(127);
        let idx = self.binop(Operator::I32And, self.cur_char(), c127, Type::I32);
        let c63 = self.i32c(63);
        let sh32 = self.binop(Operator::I32And, idx, c63, Type::I32);
        let sh = self.unop(Operator::I64ExtendI32U, sh32, Type::I64);
        let lo_v = self.i64c(lo);
        let hi_v = self.i64c(hi);
        let slo = self.binop(Operator::I64ShrU, lo_v, sh, Type::I64);
        let shi = self.binop(Operator::I64ShrU, hi_v, sh, Type::I64);
        // use_hi = (idx >> 6) & 1; mask = 0 - use_hi (all-ones if hi).
        let c6 = self.i32c(6);
        let use_hi32 = self.binop(Operator::I32ShrU, idx, c6, Type::I32);
        let use_hi = self.unop(Operator::I64ExtendI32U, use_hi32, Type::I64);
        let zero = self.i64c(0);
        let mask = self.binop(Operator::I64Sub, zero, use_hi, Type::I64);
        let ones = self.i64c(u64::MAX);
        let nmask = self.binop(Operator::I64Xor, mask, ones, Type::I64);
        let a = self.binop(Operator::I64And, shi, mask, Type::I64);
        let b = self.binop(Operator::I64And, slo, nmask, Type::I64);
        let word = self.binop(Operator::I64Or, a, b, Type::I64);
        let w32 = self.unop(Operator::I32WrapI64, word, Type::I32);
        let one = self.i32c(1);
        self.binop(Operator::I32And, w32, one, Type::I32)
    }
}

/// Translate one program. On success, returns the finished body for the
/// 6-i32-param -> i32 regex ABI signature.
pub fn translate(
    module: &Module,
    sig: Signature,
    mem: Memory,
    ci_helper: Option<Func>,
    inp: &RegexTranslateInput,
) -> Result<FunctionBody, String> {
    let bc = inp.bytecode;
    if bc.len() > MAX_BYTECODE_LEN || bc.len() < 4 || bc.len() % 4 != 0 {
        return Err(format!("bytecode length {} unsupported", bc.len()));
    }
    if inp.total_regs > MAX_REGISTERS {
        return Err(format!("register count {} too large", inp.total_regs));
    }
    if inp.output_regs > inp.total_regs {
        return Err("output regs exceed total".to_string());
    }

    // ---- pass 1: decode instruction stream, collect leaders + BT labels.
    let mut insns: Vec<Insn> = Vec::new();
    let mut leaders: Vec<u32> = vec![0];
    let mut bt_ids: HashMap<u32, u32> = HashMap::new();
    let mut bt_targets: Vec<u32> = Vec::new();
    {
        let mut off = 0usize;
        while off < bc.len() {
            if off + 4 > bc.len() {
                return Err("truncated instruction".to_string());
            }
            let w0 = rd32(bc, off);
            let op = (w0 & 0xff) as u8;
            if op >= BC_COUNT {
                return Err(format!("invalid opcode {} at {}", op, off));
            }
            let len = BC_LENGTHS[op as usize];
            if off + len > bc.len() {
                return Err("instruction overruns buffer".to_string());
            }
            let (labels, is_push) = label_operand_offsets(op);
            for &lo in labels {
                let t = rd32(bc, off + lo);
                if t as usize >= bc.len() || t % 4 != 0 {
                    return Err(format!("label target {} out of range", t));
                }
                leaders.push(t);
                if is_push && !bt_ids.contains_key(&t) {
                    let id = bt_targets.len() as u32;
                    bt_ids.insert(t, id);
                    bt_targets.push(t);
                }
            }
            insns.push(Insn { op, w0, off });
            off += len;
        }
    }
    if bt_targets.len() > MAX_BT_LABELS {
        return Err("too many backtrack labels".to_string());
    }
    leaders.sort_unstable();
    leaders.dedup();
    // Leaders must fall on instruction boundaries.
    {
        let starts: std::collections::HashSet<u32> = insns.iter().map(|i| i.off as u32).collect();
        for &l in &leaders {
            if !starts.contains(&l) {
                return Err(format!("leader {} not at instruction boundary", l));
            }
        }
    }

    // ---- set up function body & blocks.
    let mut body = FunctionBody::new(module, sig);
    let entry = body.entry;
    let input = body.blocks[entry].params[0].1;
    let len = body.blocks[entry].params[1].1;
    let start = body.blocks[entry].params[2].1;
    let out_ptr = body.blocks[entry].params[3].1;
    let bt_base = body.blocks[entry].params[4].1;
    let bt_cap = body.blocks[entry].params[5].1;

    let nstate = 4 + inp.total_regs as usize;
    let mut blocks: HashMap<u32, Block> = HashMap::new();
    for &l in &leaders {
        let b = body.add_block();
        for _ in 0..nstate {
            body.add_blockparam(b, Type::I32);
        }
        blocks.insert(l, b);
    }

    let mut cx = Ctx {
        body,
        cur: entry,
        mem,
        wide: inp.wide,
        nregs: inp.total_regs,
        output_regs: inp.output_regs,
        ci_helper,
        input,
        len,
        start,
        out_ptr,
        bt_base,
        bt_cap,
        st: vec![],
        blocks,
        bt_ids,
        bt_targets,
        dispatch: None,
        retry_blk: None,
    };

    // ---- entry: initial state, current_char = subject[start-1] or '\n'.
    {
        let zero = cx.i32c(0);
        let minus1 = cx.i32c(u32::MAX);
        let mut init: Vec<Value> = Vec::with_capacity(nstate);
        init.push(cx.start); // current
        init.push(zero); // current_char placeholder, patched per-arm below
        init.push(zero); // sp
        init.push(zero); // bt count
        for i in 0..inp.total_regs {
            init.push(if i < inp.output_regs { minus1 } else { zero });
        }
        let first = cx.blocks[&0];
        let have_prev = cx.binop(Operator::I32GtS, cx.start, zero, Type::I32);
        let ld_blk = cx.body.add_block();
        let nl_blk = cx.body.add_block();
        cx.body.set_terminator(
            cx.cur,
            Terminator::CondBr {
                cond: have_prev,
                if_true: BlockTarget {
                    block: ld_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: nl_blk,
                    args: vec![],
                },
            },
        );
        cx.cur = ld_blk;
        let prev_pos = cx.addk(cx.start, -1);
        let prev = cx.load_char(prev_pos);
        let mut st_ld = init.clone();
        st_ld[1] = prev;
        cx.body.set_terminator(
            ld_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: first,
                    args: st_ld,
                },
            },
        );
        cx.cur = nl_blk;
        let nl = cx.i32c('\n' as u32);
        let mut st_nl = init;
        st_nl[1] = nl;
        cx.body.set_terminator(
            nl_blk,
            Terminator::Br {
                target: BlockTarget {
                    block: first,
                    args: st_nl,
                },
            },
        );
    }

    // ---- pass 2: translate instructions linearly.
    let mut dead = true; // until we enter block 0
    for &Insn { op, w0, off } in &insns {
        let off32 = off as u32;
        if let Some(&blk) = cx.blocks.get(&off32) {
            if !dead {
                // Fall through into the leader.
                let t = cx.target(off32)?;
                cx.body.set_terminator(cx.cur, Terminator::Br { target: t });
            }
            cx.cur = blk;
            cx.st = cx.body.blocks[blk].params.iter().map(|&(_, v)| v).collect();
            dead = false;
        } else if dead {
            continue;
        }

        match op {
            BC_BREAK => {
                cx.ret(REGEX_STATUS_RETRY);
                dead = true;
            }
            BC_PUSH_CP => {
                let v = cx.cur_pos();
                cx.bt_push(v);
            }
            BC_PUSH_BT => {
                let lbl = rd32(bc, off + 4);
                let id = *cx.bt_ids.get(&lbl).unwrap();
                let idv = cx.i32c(id);
                cx.bt_push(idv);
            }
            BC_PUSH_REGISTER => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let v = cx.reg(r);
                cx.bt_push(v);
            }
            BC_SET_REGISTER => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let v = cx.i32c(rd32(bc, off + 4));
                cx.set_reg(r, v);
            }
            BC_ADVANCE_REGISTER => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let v = cx.addk(cx.reg(r), rd32(bc, off + 4) as i32);
                cx.set_reg(r, v);
            }
            BC_SET_REGISTER_TO_CP => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let v = cx.addk(cx.cur_pos(), rd32(bc, off + 4) as i32);
                cx.set_reg(r, v);
            }
            BC_SET_CP_TO_REGISTER => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let v = cx.reg(r);
                cx.set_pos(v);
            }
            BC_SET_REGISTER_TO_SP => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let v = cx.sp();
                cx.set_reg(r, v);
            }
            BC_SET_SP_TO_REGISTER => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let v = cx.reg(r);
                cx.set_sp(v);
            }
            BC_POP_CP => {
                let v = cx.bt_pop();
                cx.set_pos(v);
            }
            BC_POP_REGISTER => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let v = cx.bt_pop();
                cx.set_reg(r, v);
            }
            BC_POP_BT => {
                // Backtrack budget: give up to the interpreter past it.
                let cnt = cx.addk(cx.btcnt(), 1);
                cx.set_btcnt(cnt);
                let budget = cx.i32c(BT_BUDGET);
                let over = cx.binop(Operator::I32GeU, cnt, budget, Type::I32);
                cx.retry_if(over);
                let id = cx.bt_pop();
                // Branch to the dispatcher with [id, state...].
                if cx.dispatch.is_none() {
                    let b = cx.body.add_block();
                    let idp = cx.body.add_blockparam(b, Type::I32);
                    let mut ps = Vec::with_capacity(nstate);
                    for _ in 0..nstate {
                        ps.push(cx.body.add_blockparam(b, Type::I32));
                    }
                    cx.dispatch = Some((b, idp, ps));
                }
                let dblk = cx.dispatch.as_ref().unwrap().0;
                let mut args = vec![id];
                args.extend(cx.st.iter().copied());
                cx.body.set_terminator(
                    cx.cur,
                    Terminator::Br {
                        target: BlockTarget { block: dblk, args },
                    },
                );
                dead = true;
            }
            BC_FAIL => {
                cx.ret(REGEX_STATUS_FAILURE);
                dead = true;
            }
            BC_SUCCEED => {
                for k in 0..cx.output_regs {
                    let v = cx.reg(k);
                    cx.store_i32(cx.out_ptr, 4 * k, v);
                }
                cx.ret(REGEX_STATUS_SUCCESS);
                dead = true;
            }
            BC_ADVANCE_CP => {
                let v = cx.addk(cx.cur_pos(), packed_s(w0));
                cx.set_pos(v);
            }
            BC_GOTO => {
                cx.goto(rd32(bc, off + 4))?;
                dead = true;
            }
            BC_ADVANCE_CP_AND_GOTO => {
                let v = cx.addk(cx.cur_pos(), packed_s(w0));
                cx.set_pos(v);
                cx.goto(rd32(bc, off + 4))?;
                dead = true;
            }
            BC_CHECK_FIXED_LENGTH => {
                // If current == tos: pop and jump; else fall through.
                let tos = cx.bt_peek();
                let eq = cx.binop(Operator::I32Eq, cx.cur_pos(), tos, Type::I32);
                let sp1 = cx.addk(cx.sp(), -1);
                let saved_sp = cx.sp();
                cx.set_sp(sp1);
                cx.cond_jump(eq, rd32(bc, off + 4))?;
                cx.set_sp(saved_sp);
            }
            BC_LOAD_CURRENT_CHAR => {
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                let oob = cx.binop(Operator::I32GeU, pos, cx.len, Type::I32);
                cx.cond_jump(oob, rd32(bc, off + 4))?;
                let c = cx.load_char(pos);
                cx.set_char(c);
            }
            BC_LOAD_CURRENT_CHAR_UNCHECKED => {
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                let c = cx.load_char(pos);
                cx.set_char(c);
            }
            BC_LOAD_2_CURRENT_CHARS => {
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                // pos + 2 > len || pos < 0, computed in 32-bit signed-safe
                // space (guards len < 2 too).
                let oob = cx.oob_span(pos, 2);
                cx.cond_jump(oob, rd32(bc, off + 4))?;
                let c = cx.load_2_chars(pos);
                cx.set_char(c);
            }
            BC_LOAD_2_CURRENT_CHARS_UNCHECKED => {
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                let c = cx.load_2_chars(pos);
                cx.set_char(c);
            }
            BC_LOAD_4_CURRENT_CHARS => {
                if inp.wide {
                    return Err("LOAD_4_CURRENT_CHARS in wide program".to_string());
                }
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                let oob = cx.oob_span(pos, 4);
                cx.cond_jump(oob, rd32(bc, off + 4))?;
                let c = cx.load_4_chars(pos);
                cx.set_char(c);
            }
            BC_LOAD_4_CURRENT_CHARS_UNCHECKED => {
                if inp.wide {
                    return Err("LOAD_4_CURRENT_CHARS_UNCHECKED in wide program".to_string());
                }
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                let c = cx.load_4_chars(pos);
                cx.set_char(c);
            }
            BC_CHECK_CHAR | BC_CHECK_NOT_CHAR => {
                let c = cx.i32c(packed_u(w0));
                let eq = cx.binop(Operator::I32Eq, c, cx.cur_char(), Type::I32);
                cx.cond_jump_polar(op == BC_CHECK_CHAR, eq, rd32(bc, off + 4))?;
            }
            BC_CHECK_4_CHARS | BC_CHECK_NOT_4_CHARS => {
                let c = cx.i32c(rd32(bc, off + 4));
                let eq = cx.binop(Operator::I32Eq, c, cx.cur_char(), Type::I32);
                cx.cond_jump_polar(op == BC_CHECK_4_CHARS, eq, rd32(bc, off + 8))?;
            }
            BC_AND_CHECK_CHAR | BC_AND_CHECK_NOT_CHAR => {
                let c = cx.i32c(packed_u(w0));
                let mask = cx.i32c(rd32(bc, off + 4));
                let masked = cx.binop(Operator::I32And, cx.cur_char(), mask, Type::I32);
                let eq = cx.binop(Operator::I32Eq, c, masked, Type::I32);
                cx.cond_jump_polar(op == BC_AND_CHECK_CHAR, eq, rd32(bc, off + 8))?;
            }
            BC_AND_CHECK_4_CHARS | BC_AND_CHECK_NOT_4_CHARS => {
                let c = cx.i32c(rd32(bc, off + 4));
                let mask = cx.i32c(rd32(bc, off + 8));
                let masked = cx.binop(Operator::I32And, cx.cur_char(), mask, Type::I32);
                let eq = cx.binop(Operator::I32Eq, c, masked, Type::I32);
                cx.cond_jump_polar(op == BC_AND_CHECK_4_CHARS, eq, rd32(bc, off + 12))?;
            }
            BC_MINUS_AND_CHECK_NOT_CHAR => {
                let c = cx.i32c(packed_u(w0));
                let minus = cx.i32c(rd16(bc, off + 4));
                let mask = cx.i32c(rd16(bc, off + 6));
                let sub = cx.binop(Operator::I32Sub, cx.cur_char(), minus, Type::I32);
                let masked = cx.binop(Operator::I32And, sub, mask, Type::I32);
                let ne = cx.binop(Operator::I32Ne, c, masked, Type::I32);
                cx.cond_jump(ne, rd32(bc, off + 8))?;
            }
            BC_CHECK_CHAR_IN_RANGE | BC_CHECK_CHAR_NOT_IN_RANGE => {
                let from = cx.i32c(rd16(bc, off + 4));
                let to = cx.i32c(rd16(bc, off + 6));
                let ge = cx.binop(Operator::I32GeU, cx.cur_char(), from, Type::I32);
                let le = cx.binop(Operator::I32LeU, cx.cur_char(), to, Type::I32);
                let inr = cx.binop(Operator::I32And, ge, le, Type::I32);
                cx.cond_jump_polar(op == BC_CHECK_CHAR_IN_RANGE, inr, rd32(bc, off + 8))?;
            }
            BC_CHECK_BIT_IN_TABLE => {
                let bit = cx.bit_in_table(&bc[off + 8..off + 24]);
                cx.cond_jump(bit, rd32(bc, off + 4))?;
            }
            BC_CHECK_LT => {
                let limit = cx.i32c(packed_u(w0));
                let lt = cx.binop(Operator::I32LtU, cx.cur_char(), limit, Type::I32);
                cx.cond_jump(lt, rd32(bc, off + 4))?;
            }
            BC_CHECK_GT => {
                let limit = cx.i32c(packed_u(w0));
                let gt = cx.binop(Operator::I32GtU, cx.cur_char(), limit, Type::I32);
                cx.cond_jump(gt, rd32(bc, off + 4))?;
            }
            BC_CHECK_REGISTER_LT => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let c = cx.i32c(rd32(bc, off + 4));
                let lt = cx.binop(Operator::I32LtS, cx.reg(r), c, Type::I32);
                cx.cond_jump(lt, rd32(bc, off + 8))?;
            }
            BC_CHECK_REGISTER_GE => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let c = cx.i32c(rd32(bc, off + 4));
                let ge = cx.binop(Operator::I32GeS, cx.reg(r), c, Type::I32);
                cx.cond_jump(ge, rd32(bc, off + 8))?;
            }
            BC_CHECK_REGISTER_EQ_POS => {
                let r = packed_u(w0);
                cx.check_reg(r)?;
                let eq = cx.binop(Operator::I32Eq, cx.reg(r), cx.cur_pos(), Type::I32);
                cx.cond_jump(eq, rd32(bc, off + 4))?;
            }
            BC_CHECK_NOT_REGS_EQUAL => {
                let r1 = packed_u(w0);
                let r2 = rd32(bc, off + 4);
                cx.check_reg(r1)?;
                cx.check_reg(r2)?;
                let eq = cx.binop(Operator::I32Eq, cx.reg(r1), cx.reg(r2), Type::I32);
                cx.cond_jump_inv(eq, rd32(bc, off + 8))?;
            }
            BC_CHECK_AT_START => {
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                let z = cx.i32c(0);
                let at = cx.binop(Operator::I32Eq, pos, z, Type::I32);
                cx.cond_jump(at, rd32(bc, off + 4))?;
            }
            BC_CHECK_NOT_AT_START => {
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                let z = cx.i32c(0);
                let at = cx.binop(Operator::I32Eq, pos, z, Type::I32);
                cx.cond_jump_inv(at, rd32(bc, off + 4))?;
            }
            BC_SET_CURRENT_POSITION_FROM_END => {
                let by = packed_u(w0) as i32;
                // if (len - current > by) { current = len - by;
                //                           current_char = subject[current-1]; }
                let diff = cx.binop(Operator::I32Sub, cx.len, cx.cur_pos(), Type::I32);
                let byv = cx.i32c(by as u32);
                let cond = cx.binop(Operator::I32GtS, diff, byv, Type::I32);
                let upd = cx.body.add_block();
                let join = cx.body.add_block();
                let jp_pos = cx.body.add_blockparam(join, Type::I32);
                let jp_char = cx.body.add_blockparam(join, Type::I32);
                cx.body.set_terminator(
                    cx.cur,
                    Terminator::CondBr {
                        cond,
                        if_true: BlockTarget {
                            block: upd,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: join,
                            args: vec![cx.cur_pos(), cx.cur_char()],
                        },
                    },
                );
                cx.cur = upd;
                let new_pos = cx.binop(Operator::I32Sub, cx.len, byv, Type::I32);
                let prev_pos = cx.addk(new_pos, -1);
                let new_char = cx.load_char(prev_pos);
                cx.body.set_terminator(
                    upd,
                    Terminator::Br {
                        target: BlockTarget {
                            block: join,
                            args: vec![new_pos, new_char],
                        },
                    },
                );
                cx.cur = join;
                cx.set_pos(jp_pos);
                cx.set_char(jp_char);
            }
            BC_CHECK_CURRENT_POSITION => {
                let pos = cx.addk(cx.cur_pos(), packed_s(w0));
                // pos > len || pos < 0  ==  (u32)pos > (u32)len.
                let oob = cx.binop(Operator::I32GtU, pos, cx.len, Type::I32);
                cx.cond_jump(oob, rd32(bc, off + 4))?;
            }
            BC_CHECK_NOT_BACK_REF
            | BC_CHECK_NOT_BACK_REF_BACKWARD
            | BC_CHECK_NOT_BACK_REF_NO_CASE
            | BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE
            | BC_CHECK_NOT_BACK_REF_NO_CASE_BACKWARD
            | BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE_BACKWARD => {
                emit_backref(&mut cx, op, w0, rd32(bc, off + 4))?;
            }
            BC_SKIP_UNTIL_CHAR => {
                let load_off = packed_s(w0);
                let advance = rd16(bc, off + 4) as u16 as i16 as i32;
                let c = rd16(bc, off + 6);
                emit_skip_loop(
                    &mut cx,
                    load_off,
                    advance,
                    SkipBound::InBounds,
                    rd32(bc, off + 8),
                    rd32(bc, off + 12),
                    |cx, ch| {
                        let cv = cx.i32c(c);
                        cx.binop(Operator::I32Eq, cv, ch, Type::I32)
                    },
                )?;
            }
            BC_SKIP_UNTIL_CHAR_AND => {
                let load_off = packed_s(w0);
                let advance = rd16(bc, off + 4) as u16 as i16 as i32;
                let c = rd16(bc, off + 6);
                let mask = rd32(bc, off + 8);
                let max_off = rd32(bc, off + 12) as i32;
                emit_skip_loop(
                    &mut cx,
                    load_off,
                    advance,
                    SkipBound::MaxOffset(max_off),
                    rd32(bc, off + 16),
                    rd32(bc, off + 20),
                    |cx, ch| {
                        let mv = cx.i32c(mask);
                        let masked = cx.binop(Operator::I32And, ch, mv, Type::I32);
                        let cv = cx.i32c(c);
                        cx.binop(Operator::I32Eq, cv, masked, Type::I32)
                    },
                )?;
            }
            BC_SKIP_UNTIL_CHAR_POS_CHECKED => {
                let load_off = packed_s(w0);
                let advance = rd16(bc, off + 4) as u16 as i16 as i32;
                let c = rd16(bc, off + 6);
                let max_off = rd32(bc, off + 8) as i32;
                emit_skip_loop(
                    &mut cx,
                    load_off,
                    advance,
                    SkipBound::MaxOffset(max_off),
                    rd32(bc, off + 12),
                    rd32(bc, off + 16),
                    |cx, ch| {
                        let cv = cx.i32c(c);
                        cx.binop(Operator::I32Eq, cv, ch, Type::I32)
                    },
                )?;
            }
            BC_SKIP_UNTIL_CHAR_OR_CHAR => {
                let load_off = packed_s(w0);
                let advance = rd32(bc, off + 4) as i32;
                let c1 = rd16(bc, off + 8);
                let c2 = rd16(bc, off + 10);
                emit_skip_loop(
                    &mut cx,
                    load_off,
                    advance,
                    SkipBound::InBounds,
                    rd32(bc, off + 12),
                    rd32(bc, off + 16),
                    |cx, ch| {
                        let cv1 = cx.i32c(c1);
                        let cv2 = cx.i32c(c2);
                        let e1 = cx.binop(Operator::I32Eq, cv1, ch, Type::I32);
                        let e2 = cx.binop(Operator::I32Eq, cv2, ch, Type::I32);
                        cx.binop(Operator::I32Or, e1, e2, Type::I32)
                    },
                )?;
            }
            BC_SKIP_UNTIL_BIT_IN_TABLE => {
                let load_off = packed_s(w0);
                let advance = rd32(bc, off + 4) as i32;
                let table: Vec<u8> = bc[off + 8..off + 24].to_vec();
                emit_skip_loop(
                    &mut cx,
                    load_off,
                    advance,
                    SkipBound::InBounds,
                    rd32(bc, off + 24),
                    rd32(bc, off + 28),
                    move |cx, ch| {
                        let saved = cx.st[1];
                        cx.st[1] = ch;
                        let bit = cx.bit_in_table(&table);
                        cx.st[1] = saved;
                        bit
                    },
                )?;
            }
            BC_SKIP_UNTIL_GT_OR_NOT_BIT_IN_TABLE => {
                let load_off = packed_s(w0);
                let advance = rd16(bc, off + 4) as u16 as i16 as i32;
                let limit = rd16(bc, off + 6);
                let table: Vec<u8> = bc[off + 8..off + 24].to_vec();
                emit_skip_loop(
                    &mut cx,
                    load_off,
                    advance,
                    SkipBound::InBounds,
                    rd32(bc, off + 24),
                    rd32(bc, off + 28),
                    move |cx, ch| {
                        let lv = cx.i32c(limit);
                        let gt = cx.binop(Operator::I32GtU, ch, lv, Type::I32);
                        let saved = cx.st[1];
                        cx.st[1] = ch;
                        let bit = cx.bit_in_table(&table);
                        cx.st[1] = saved;
                        let one = cx.i32c(1);
                        let nbit = cx.binop(Operator::I32Xor, bit, one, Type::I32);
                        cx.binop(Operator::I32Or, gt, nbit, Type::I32)
                    },
                )?;
            }
            _ => {
                return Err(format!("unhandled opcode {}", op));
            }
        }
        if is_unconditional(op) {
            dead = true;
        }
    }

    // A body that runs off the end would be malformed bytecode.
    if !dead {
        cx.ret(REGEX_STATUS_RETRY);
    }

    // ---- finalize the backtrack dispatcher.
    if let Some((dblk, idp, ps)) = cx.dispatch.take() {
        let default = cx.retry_target();
        let mut targets: Vec<BlockTarget> = Vec::with_capacity(cx.bt_targets.len());
        for k in 0..cx.bt_targets.len() {
            let offt = cx.bt_targets[k];
            let block = cx.blocks[&offt];
            targets.push(BlockTarget {
                block,
                args: ps.clone(),
            });
        }
        if targets.is_empty() {
            cx.body
                .set_terminator(dblk, Terminator::Br { target: default });
        } else {
            cx.body.set_terminator(
                dblk,
                Terminator::Select {
                    value: idp,
                    targets,
                    default,
                },
            );
        }
    }

    Ok(cx.body)
}

enum SkipBound {
    /// while (0 <= current+load_off < len)
    InBounds,
    /// while ((u32)(current + max_off) <= (u32)len)
    MaxOffset(i32),
}

/// Shared shape of the SKIP_UNTIL_* fused scan loops.
fn emit_skip_loop(
    cx: &mut Ctx,
    load_off: i32,
    advance: i32,
    bound: SkipBound,
    on_match: u32,
    on_no_match: u32,
    mut test: impl FnMut(&mut Ctx, Value) -> Value,
) -> Result<(), String> {
    // Loop header carries (current, current_char); everything else is
    // invariant across the scan.
    let hdr = cx.body.add_block();
    let h_pos = cx.body.add_blockparam(hdr, Type::I32);
    let h_char = cx.body.add_blockparam(hdr, Type::I32);
    cx.body.set_terminator(
        cx.cur,
        Terminator::Br {
            target: BlockTarget {
                block: hdr,
                args: vec![cx.cur_pos(), cx.cur_char()],
            },
        },
    );
    cx.cur = hdr;
    cx.set_pos(h_pos);
    cx.set_char(h_char);

    let in_bounds = match bound {
        SkipBound::InBounds => {
            let pos = cx.addk(h_pos, load_off);
            cx.binop(Operator::I32LtU, pos, cx.len, Type::I32)
        }
        SkipBound::MaxOffset(mo) => {
            let pos = cx.addk(h_pos, mo);
            cx.binop(Operator::I32LeU, pos, cx.len, Type::I32)
        }
    };
    // Out of bounds -> on_no_match with the (advanced) current position.
    cx.cond_jump_inv(in_bounds, on_no_match)?;

    let load_pos = cx.addk(h_pos, load_off);
    let ch = cx.load_char(load_pos);
    cx.set_char(ch);
    let hit = test(cx, ch);
    cx.cond_jump(hit, on_match)?;

    // Advance and continue the scan.
    let next = cx.addk(h_pos, advance);
    cx.body.set_terminator(
        cx.cur,
        Terminator::Br {
            target: BlockTarget {
                block: hdr,
                args: vec![next, ch],
            },
        },
    );
    // Emission continues nowhere: the loop is closed. Mark by switching to a
    // fresh unreachable-free path: the caller sets `dead` for skip ops.
    Ok(())
}

/// CHECK_NOT_BACK_REF family. `target` is the on-mismatch label.
fn emit_backref(cx: &mut Ctx, op: u8, w0: u32, target_off: u32) -> Result<(), String> {
    let backward = matches!(
        op,
        BC_CHECK_NOT_BACK_REF_BACKWARD
            | BC_CHECK_NOT_BACK_REF_NO_CASE_BACKWARD
            | BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE_BACKWARD
    );
    let no_case = op != BC_CHECK_NOT_BACK_REF && op != BC_CHECK_NOT_BACK_REF_BACKWARD;
    let unicode = matches!(
        op,
        BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE | BC_CHECK_NOT_BACK_REF_NO_CASE_UNICODE_BACKWARD
    );

    let r = packed_u(w0);
    cx.check_reg(r)?;
    cx.check_reg(r + 1)?;
    let from = cx.reg(r);
    let to = cx.reg(r + 1);
    let len_ = cx.binop(Operator::I32Sub, to, from, Type::I32);

    // Join block carries the (possibly advanced) current position.
    let join = cx.body.add_block();
    let jp_pos = cx.body.add_blockparam(join, Type::I32);

    let z = cx.i32c(0);
    let from_ok = cx.binop(Operator::I32GeS, from, z, Type::I32);
    let len_ok = cx.binop(Operator::I32GtS, len_, z, Type::I32);
    let active = cx.binop(Operator::I32And, from_ok, len_ok, Type::I32);
    let chk = cx.body.add_block();
    cx.body.set_terminator(
        cx.cur,
        Terminator::CondBr {
            cond: active,
            if_true: BlockTarget {
                block: chk,
                args: vec![],
            },
            if_false: BlockTarget {
                block: join,
                args: vec![cx.cur_pos()],
            },
        },
    );
    cx.cur = chk;

    // Bounds check + comparison base.
    let cmp_base;
    let new_pos;
    if backward {
        // current - len < 0 -> mismatch target.
        let base = cx.binop(Operator::I32Sub, cx.cur_pos(), len_, Type::I32);
        let oob = cx.binop(Operator::I32LtS, base, z, Type::I32);
        cx.cond_jump(oob, target_off)?;
        cmp_base = base;
        new_pos = base;
    } else {
        // current + len > subject.length -> mismatch target.
        let end = cx.add(cx.cur_pos(), len_);
        let oob = cx.binop(Operator::I32GtS, end, cx.len, Type::I32);
        cx.cond_jump(oob, target_off)?;
        cmp_base = cx.cur_pos();
        new_pos = end;
    }

    if no_case && cx.wide {
        // Two-byte case-insensitive compare: engine helper (icu tables).
        let helper = cx
            .ci_helper
            .ok_or_else(|| "no case-insensitive helper available".to_string())?;
        let a = cx.char_addr(from);
        let b = cx.char_addr(cmp_base);
        let two = cx.i32c(2);
        let bytes = cx.binop(Operator::I32Mul, len_, two, Type::I32);
        let uni = cx.i32c(unicode as u32);
        let res = cx.call_i32(helper, &[a, b, bytes, uni]);
        let one = cx.i32c(1);
        let ne = cx.binop(Operator::I32Ne, res, one, Type::I32);
        cx.cond_jump(ne, target_off)?;
    } else {
        // Inline compare loop over i in [0, len_).
        let hdr = cx.body.add_block();
        let iv = cx.body.add_blockparam(hdr, Type::I32);
        cx.body.set_terminator(
            cx.cur,
            Terminator::Br {
                target: BlockTarget {
                    block: hdr,
                    args: vec![z],
                },
            },
        );
        cx.cur = hdr;
        let done = cx.binop(Operator::I32GeS, iv, len_, Type::I32);
        let body_blk = cx.body.add_block();
        let done_blk = cx.body.add_block();
        cx.body.set_terminator(
            hdr,
            Terminator::CondBr {
                cond: done,
                if_true: BlockTarget {
                    block: done_blk,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: body_blk,
                    args: vec![],
                },
            },
        );
        cx.cur = body_blk;
        let pa = cx.add(from, iv);
        let pb = cx.add(cmp_base, iv);
        let a = cx.load_char(pa);
        let b = cx.load_char(pb);
        let i1 = cx.addk(iv, 1);
        let cont = BlockTarget {
            block: hdr,
            args: vec![i1],
        };
        if !no_case {
            let ne = cx.binop(Operator::I32Ne, a, b, Type::I32);
            cx.cond_jump(ne, target_off)?;
            cx.body
                .set_terminator(cx.cur, Terminator::Br { target: cont });
        } else {
            // Latin1 no-case fold (also used for latin1 'unicode' variants:
            // for Latin1 characters the unicode flag makes no difference).
            let eq = cx.binop(Operator::I32Eq, a, b, Type::I32);
            let fold_blk = cx.body.add_block();
            cx.body.set_terminator(
                cx.cur,
                Terminator::CondBr {
                    cond: eq,
                    if_true: cont.clone(),
                    if_false: BlockTarget {
                        block: fold_blk,
                        args: vec![],
                    },
                },
            );
            cx.cur = fold_blk;
            let x20 = cx.i32c(0x20);
            let af = cx.binop(Operator::I32Or, a, x20, Type::I32);
            let bf = cx.binop(Operator::I32Or, b, x20, Type::I32);
            let ne = cx.binop(Operator::I32Ne, af, bf, Type::I32);
            cx.cond_jump(ne, target_off)?;
            // Letter test: (af - 'a') <= 25 || ((af - 224) <= 30 && af != 247).
            let ca = cx.i32c('a' as u32);
            let d1 = cx.binop(Operator::I32Sub, af, ca, Type::I32);
            let k25 = cx.i32c(25);
            let is_ascii = cx.binop(Operator::I32LeU, d1, k25, Type::I32);
            let c224 = cx.i32c(224);
            let d2 = cx.binop(Operator::I32Sub, af, c224, Type::I32);
            let k30 = cx.i32c(30);
            let in_hi = cx.binop(Operator::I32LeU, d2, k30, Type::I32);
            let c247 = cx.i32c(247);
            let not247 = cx.binop(Operator::I32Ne, af, c247, Type::I32);
            let hi_ok = cx.binop(Operator::I32And, in_hi, not247, Type::I32);
            let is_letter = cx.binop(Operator::I32Or, is_ascii, hi_ok, Type::I32);
            cx.cond_jump_inv(is_letter, target_off)?;
            cx.body
                .set_terminator(cx.cur, Terminator::Br { target: cont });
        }
        cx.cur = done_blk;
    }

    // Matched: advance current and rejoin the fall-through.
    cx.body.set_terminator(
        cx.cur,
        Terminator::Br {
            target: BlockTarget {
                block: join,
                args: vec![new_pos],
            },
        },
    );
    cx.cur = join;
    cx.set_pos(jp_pos);
    Ok(())
}
