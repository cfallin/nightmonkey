/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

use crate::bytecode::{JSOp, OpcodeVisitor};
use crate::ids::Pc;

/// Buffers one instruction's text so each line reaches the diagnostic
/// stream whole (`before_op` writes the opcode, the per-op arm appends its
/// operands and flushes).
#[derive(Default)]
pub struct Disassembler {
    line: String,
}

impl Disassembler {
    fn flush(&mut self) {
        crate::diag_line!("{}", self.line);
        self.line.clear();
    }
}

macro_rules! impl_disassembler {
    (
        noargs: [$($noarg:ident),* $(,)?],
        args: [$($op:ident($($arg:ident: $ty:ty),*)),* $(,)?] $(,)?
        custom: $($custom:tt)*
    ) => {
        impl OpcodeVisitor for Disassembler {
            fn before_op(&mut self, pc: Pc, op: JSOp, _nuses: usize, _ndefs: usize) {
                self.line = format!("{pc:>6}: {op:?}");
            }

            $(
                fn $noarg(&mut self) {
                    self.flush();
                }
            )*

            $(
                fn $op(&mut self, $($arg: $ty),*) {
                    use std::fmt::Write as _;
                    $(let _ = write!(self.line, " {}", $arg);)*
                    self.flush();
                }
            )*

            $($custom)*
        }
    };
}

impl_disassembler! {
    noargs: [
        undefined, null, false_, true_,
        zero, one, void, typeof_,
        typeof_expr, pos, neg, bit_not,
        not_, bit_or, bit_xor, bit_and,
        eq, ne, strict_eq, strict_ne,
        lt, gt, le,
        ge, instanceof, in_, lsh,
        rsh, ursh, add, sub,
        inc, dec, mul, div,
        mod_, pow, nop_is_assign_op, to_property_key,
        to_numeric, to_string, is_null_or_undefined, global_this,
        non_syntactic_global_this, new_target, dynamic_import, import_meta,
        obj_with_proto, init_elem, init_hidden_elem, init_locked_elem,
        init_elem_getter, init_hidden_elem_getter,
        init_elem_setter, init_hidden_elem_setter, get_elem, set_elem,
        strict_set_elem, del_elem, strict_del_elem, has_own,
        super_base, get_elem_super, set_elem_super, strict_set_elem_super,
        iter, more_iter, is_no_iter, end_iter,
        optimize_get_iterator, check_obj_coercible, to_async_iter, mutate_proto,
        init_elem_inc, hole, init_home_object, check_class_heritage,
        spread_call, optimize_spread_call, spread_eval, strict_spread_eval,
        implicit_this, is_constructing,
        spread_new, spread_super_call, super_fun, check_this_reinit,
        generator, final_yield_rval, is_gen_closing, async_await,
        async_resolve, async_reject, can_skip_await, maybe_extract_await_value,
        check_resume_kind, resume, return_, get_rval,
        set_rval, ret_rval, check_return, throw_,
        throw_with_stack, create_suppressed_error, try_, try_destructuring,
        exception, exception_and_stack, finally, uninitialized,
        check_this, arguments_length, get_actual_arg, callee,
        pop_lexical_env, debug_leave_lexical_env, leave_with, take_dispose_capability,
        bind_var, arguments, rest, function_this,
        pop, dup, dup2, swap,
        nop, nop_destructuring, force_interpreter, debug_check_self_hosted,
        debugger,
    ],
    args: [
        int32(value: u32),
        int8(value: u8),
        uint16(value: u16),
        uint24(value: u32),
        double(value: u64),
        bigint(bigint_index: u32),
        string(atom_index: u32),
        symbol(code: u8),
        typeof_eq(operand: u8),
        strict_constant_eq(operand: u16),
        strict_constant_ne(operand: u16),
        new_init(property_count: u8),
        new_object(shape_index: u32),
        object(object_index: u32),
        init_prop(name_index: u32),
        init_hidden_prop(name_index: u32),
        init_locked_prop(name_index: u32),
        init_prop_getter(name_index: u32),
        init_prop_setter(name_index: u32),
        init_hidden_prop_getter(name_index: u32),
        init_hidden_prop_setter(name_index: u32),
        get_prop(name_index: u32),
        set_prop(name_index: u32),
        strict_set_prop(name_index: u32),
        del_prop(name_index: u32),
        strict_del_prop(name_index: u32),
        check_private_field(throw_condition: u8, msg_kind: u8),
        new_private_name(name_index: u32),
        get_prop_super(name_index: u32),
        set_prop_super(name_index: u32),
        strict_set_prop_super(name_index: u32),
        close_iter(kind: u8),
        check_is_obj(kind: u8),
        new_array(length: u32),
        init_elem_array(index: u32),
        reg_exp(regexp_index: u32),
        lambda(func_index: u32),
        set_fun_name(prefix_kind: u8),
        fun_with_proto(func_index: u32),
        builtin_object(kind: u8),
        call(argc: u16),
        call_content(argc: u16),
        call_iter(argc: u16),
        call_content_iter(argc: u16),
        call_ignores_rv(argc: u16),
        eval(argc: u16),
        strict_eval(argc: u16),
        call_site_obj(object_index: u32),
        new_(argc: u16),
        new_content(argc: u16),
        super_call(argc: u16),
        initial_yield(resume_index: u32),
        after_yield(ic_index: u32),
        yield_(resume_index: u32),
        await_(resume_index: u32),
        resume_kind(resume_kind: u8),
        jump_target(ic_index: u32),
        loop_head(ic_index: u32, depth_hint: u8),
        goto_(offset: i32),
        jump_if_false(forward_offset: i32),
        jump_if_true(offset: i32),
        and_(forward_offset: i32),
        or_(forward_offset: i32),
        coalesce(forward_offset: i32),
        case_(forward_offset: i32),
        default_(forward_offset: i32),
        throw_msg(msg_number: u8),
        throw_set_const(name_index: u32),
        init_lexical(localno: u32),
        init_g_lexical(name_index: u32),
        init_aliased_lexical(hops: u16, slot: u32),
        check_lexical(localno: u32),
        check_aliased_lexical(hops: u16, slot: u32),
        bind_unqualified_g_name(name_index: u32),
        bind_unqualified_name(name_index: u32),
        bind_name(name_index: u32),
        get_name(name_index: u32),
        get_g_name(name_index: u32),
        get_arg(argno: u16),
        get_frame_arg(argno: u16),
        get_local(localno: u32),
        get_aliased_var(hops: u16, slot: u32),
        get_aliased_debug_var(hops: u16, slot: u32),
        get_import(name_index: u32),
        get_bound_name(name_index: u32),
        get_intrinsic(name_index: u32),
        env_callee(num_hops: u16),
        set_name(name_index: u32),
        strict_set_name(name_index: u32),
        set_g_name(name_index: u32),
        strict_set_g_name(name_index: u32),
        set_arg(argno: u16),
        set_local(localno: u32),
        set_aliased_var(hops: u16, slot: u32),
        set_intrinsic(name_index: u32),
        push_lexical_env(lexical_scope_index: u32),
        recreate_lexical_env(lexical_scope_index: u32),
        freshen_lexical_env(lexical_scope_index: u32),
        push_class_body_env(lexical_scope_index: u32),
        push_var_env(scope_index: u32),
        enter_with(static_with_index: u32),
        add_disposable(hint: u8),
        global_or_eval_decl_instantiation(last_fun: u32),
        del_name(name_index: u32),
        pop_n(n: u16),
        dup_at(n: u32),
        pick(n: u8),
        unpick(n: u8),
        lineno(lineno: u32),
    ],

    custom:

    fn table_switch(&mut self, default_offset: i32, low: i32, high: i32, offsets: &[Pc]) {
        use std::fmt::Write as _;
        let _ = write!(
            self.line,
            " {} {} {} {:?}",
            default_offset, low, high, offsets
        );
        self.flush();
    }
}
