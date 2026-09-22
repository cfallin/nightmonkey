/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// X-macro list of the night_runtime_* helpers the night-compiler translator
// resolves: the resolve_helpers list in js/src/night/compiler/src/wasm/mod.rs
// (in order), plus night_runtime_regex_ci_compare (resolved separately in
// translate_all). The in-process driver expands it into the {name, funcptr,
// sig} import table passed to night_inproc_build; the signature string is
// derived from the helper's real C++ type (see NightHelperSig), so the table
// can never drift from the declarations in NightRuntime.h.

#ifndef night_runtime_NightHelperList_h
#define night_runtime_NightHelperList_h

#include <array>
#include <stddef.h>
#include <stdint.h>

#include "runtime/NightRuntime.h"

#define FOR_EACH_NIGHT_RUNTIME_HELPER(NIGHT_RUNTIME_HELPER)       \
  NIGHT_RUNTIME_HELPER(night_runtime_callee_night_target)         \
  NIGHT_RUNTIME_HELPER(night_runtime_add)                         \
  NIGHT_RUNTIME_HELPER(night_runtime_concat)                      \
  NIGHT_RUNTIME_HELPER(night_runtime_call)                        \
  NIGHT_RUNTIME_HELPER(night_runtime_call_iter)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_native_dispatch)             \
  NIGHT_RUNTIME_HELPER(night_runtime_apply_fwd)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_construct)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_get_property)                \
  NIGHT_RUNTIME_HELPER(night_runtime_set_property)                \
  NIGHT_RUNTIME_HELPER(night_runtime_get_prop_ic_miss)            \
  NIGHT_RUNTIME_HELPER(night_runtime_set_prop_ic_miss)            \
  NIGHT_RUNTIME_HELPER(night_runtime_get_gname)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_get_element)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_set_element)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_binop)                       \
  NIGHT_RUNTIME_HELPER(night_runtime_compare)                     \
  NIGHT_RUNTIME_HELPER(night_runtime_string)                      \
  NIGHT_RUNTIME_HELPER(night_runtime_get_intrinsic)               \
  NIGHT_RUNTIME_HELPER(night_runtime_get_intrinsic_cell)          \
  NIGHT_RUNTIME_HELPER(night_runtime_census)                      \
  NIGHT_RUNTIME_HELPER(night_runtime_strlit_verify)               \
  NIGHT_RUNTIME_HELPER(night_runtime_str_chars_eq)                \
  NIGHT_RUNTIME_HELPER(night_runtime_tonumeric)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_pos)                         \
  NIGHT_RUNTIME_HELPER(night_runtime_neg)                         \
  NIGHT_RUNTIME_HELPER(night_runtime_instanceof)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_del_prop)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_arguments)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_arguments_env)               \
  NIGHT_RUNTIME_HELPER(night_runtime_box_nonstrict_this)          \
  NIGHT_RUNTIME_HELPER(night_runtime_get_mapped_arg)              \
  NIGHT_RUNTIME_HELPER(night_runtime_set_mapped_arg)              \
  NIGHT_RUNTIME_HELPER(night_runtime_validate_this_layout)        \
  NIGHT_RUNTIME_HELPER(night_runtime_in)                          \
  NIGHT_RUNTIME_HELPER(night_runtime_has_own)                     \
  NIGHT_RUNTIME_HELPER(night_runtime_to_property_key)             \
  NIGHT_RUNTIME_HELPER(night_runtime_mutate_proto)                \
  NIGHT_RUNTIME_HELPER(night_runtime_init_home_object)            \
  NIGHT_RUNTIME_HELPER(night_runtime_super_base)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_super_fun)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_get_prop_super)              \
  NIGHT_RUNTIME_HELPER(night_runtime_get_elem_super)              \
  NIGHT_RUNTIME_HELPER(night_runtime_set_prop_super)              \
  NIGHT_RUNTIME_HELPER(night_runtime_set_elem_super)              \
  NIGHT_RUNTIME_HELPER(night_runtime_tostring)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_pow)                         \
  NIGHT_RUNTIME_HELPER(night_runtime_check_obj_coercible)         \
  NIGHT_RUNTIME_HELPER(night_runtime_check_class_heritage)        \
  NIGHT_RUNTIME_HELPER(night_runtime_create_generator)            \
  NIGHT_RUNTIME_HELPER(night_runtime_gen_suspend)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_gen_restore)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_gen_check_resume)            \
  NIGHT_RUNTIME_HELPER(night_runtime_gen_closing)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_gen_final)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_async_await)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_async_resolve)               \
  NIGHT_RUNTIME_HELPER(night_runtime_async_reject)                \
  NIGHT_RUNTIME_HELPER(night_runtime_can_skip_await)              \
  NIGHT_RUNTIME_HELPER(night_runtime_maybe_extract_await)         \
  NIGHT_RUNTIME_HELPER(night_runtime_check_is_obj)                \
  NIGHT_RUNTIME_HELPER(night_runtime_check_this)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_check_lexical)               \
  NIGHT_RUNTIME_HELPER(night_runtime_throw_set_const)             \
  NIGHT_RUNTIME_HELPER(night_runtime_push_lexical_env)            \
  NIGHT_RUNTIME_HELPER(night_runtime_push_class_body_env)         \
  NIGHT_RUNTIME_HELPER(night_runtime_freshen_lexical_env)         \
  NIGHT_RUNTIME_HELPER(night_runtime_recreate_lexical_env)        \
  NIGHT_RUNTIME_HELPER(night_runtime_init_glexical)               \
  NIGHT_RUNTIME_HELPER(night_runtime_get_name)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_bind_name)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_get_bound_name)              \
  NIGHT_RUNTIME_HELPER(night_runtime_bind_unqualified_name)       \
  NIGHT_RUNTIME_HELPER(night_runtime_bind_var)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_del_name)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_push_var_env)                \
  NIGHT_RUNTIME_HELPER(night_runtime_enter_with)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_throw_msg)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_builtin_object)              \
  NIGHT_RUNTIME_HELPER(night_runtime_builtin_object_cell)         \
  NIGHT_RUNTIME_HELPER(night_runtime_del_elem)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_global_this)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_regexp)                      \
  NIGHT_RUNTIME_HELPER(night_runtime_init_prop_getset)            \
  NIGHT_RUNTIME_HELPER(night_runtime_to_boolean)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_typeof)                      \
  NIGHT_RUNTIME_HELPER(night_runtime_typeof_eq)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_constant_strict_eq)          \
  NIGHT_RUNTIME_HELPER(night_runtime_bind_unqualified_gname)      \
  NIGHT_RUNTIME_HELPER(night_runtime_set_name)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_new_object)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_new_array)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_init_prop)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_init_elem)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_init_elem_getset)            \
  NIGHT_RUNTIME_HELPER(night_runtime_check_private_field)         \
  NIGHT_RUNTIME_HELPER(night_runtime_new_private_name)            \
  NIGHT_RUNTIME_HELPER(night_runtime_env_setup)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_get_aliased)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_set_aliased)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_lambda)                      \
  NIGHT_RUNTIME_HELPER(night_runtime_exception)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_throw)                       \
  NIGHT_RUNTIME_HELPER(night_runtime_throw_with_stack)            \
  NIGHT_RUNTIME_HELPER(night_runtime_get_exception_for_finally)   \
  NIGHT_RUNTIME_HELPER(night_runtime_global_decl_instantiation)   \
  NIGHT_RUNTIME_HELPER(night_runtime_iter)                        \
  NIGHT_RUNTIME_HELPER(night_runtime_more_iter)                   \
  NIGHT_RUNTIME_HELPER(night_runtime_end_iter)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_close_iter_for_exception)    \
  NIGHT_RUNTIME_HELPER(night_runtime_symbol)                      \
  NIGHT_RUNTIME_HELPER(night_runtime_optimize_get_iterator)       \
  NIGHT_RUNTIME_HELPER(night_runtime_close_iter)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_to_async_iter)               \
  NIGHT_RUNTIME_HELPER(night_runtime_spread_call)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_optimize_spread_call)        \
  NIGHT_RUNTIME_HELPER(night_runtime_object)                      \
  NIGHT_RUNTIME_HELPER(night_runtime_post_write_barrier)          \
  NIGHT_RUNTIME_HELPER(night_runtime_post_write_barrier_elem)     \
  NIGHT_RUNTIME_HELPER(night_runtime_pre_write_barrier)           \
  NIGHT_RUNTIME_HELPER(night_runtime_resolve_global_slot)         \
  NIGHT_RUNTIME_HELPER(night_runtime_resolve_global_slot_guarded) \
  NIGHT_RUNTIME_HELPER(night_runtime_set_global)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_binding_written)             \
  NIGHT_RUNTIME_HELPER(night_runtime_binding_value)               \
  NIGHT_RUNTIME_HELPER(night_runtime_math_unary)                  \
  NIGHT_RUNTIME_HELPER(night_runtime_math_pow)                    \
  NIGHT_RUNTIME_HELPER(night_runtime_fmod)                        \
  NIGHT_RUNTIME_HELPER(night_runtime_create_this)                 \
  NIGHT_RUNTIME_HELPER(night_runtime_rest)                        \
  NIGHT_RUNTIME_HELPER(night_runtime_implicit_this)               \
  NIGHT_RUNTIME_HELPER(night_runtime_check_this_reinit)           \
  NIGHT_RUNTIME_HELPER(night_runtime_check_return)                \
  NIGHT_RUNTIME_HELPER(night_runtime_obj_with_proto)              \
  NIGHT_RUNTIME_HELPER(night_runtime_fun_with_proto)              \
  NIGHT_RUNTIME_HELPER(night_runtime_set_fun_name)                \
  NIGHT_RUNTIME_HELPER(night_runtime_no_extra_indexed)            \
  NIGHT_RUNTIME_HELPER(night_runtime_gen_is_closing)              \
  NIGHT_RUNTIME_HELPER(night_runtime_regex_ci_compare)

namespace js {
namespace night {

// Wasm value-type letter for a C ABI type (the night-compiler.h
// signature-string encoding: i=i32, j=i64, f=f32, d=f64, v=void return).
template <typename T>
struct NightSigChar;
template <typename T>
struct NightSigChar<T*> {
  static constexpr char value = 'i';
};
template <>
struct NightSigChar<bool> {
  static constexpr char value = 'i';
};
template <>
struct NightSigChar<int32_t> {
  static constexpr char value = 'i';
};
template <>
struct NightSigChar<uint32_t> {
  static constexpr char value = 'i';
};
template <>
struct NightSigChar<int64_t> {
  static constexpr char value = 'j';
};
template <>
struct NightSigChar<uint64_t> {
  static constexpr char value = 'j';
};
template <>
struct NightSigChar<float> {
  static constexpr char value = 'f';
};
template <>
struct NightSigChar<double> {
  static constexpr char value = 'd';
};
template <>
struct NightSigChar<void> {
  static constexpr char value = 'v';
};

// "ret(params)" signature string built from a function pointer type.
template <typename F>
struct NightHelperSig;
template <typename R, typename... Args>
struct NightHelperSig<R (*)(Args...)> {
  static constexpr std::array<char, sizeof...(Args) + 4> value = [] {
    std::array<char, sizeof...(Args) + 4> s{};
    size_t i = 0;
    s[i++] = NightSigChar<R>::value;
    s[i++] = '(';
    ((s[i++] = NightSigChar<Args>::value), ...);
    s[i] = ')';
    return s;
  }();
};

struct NightHelperEntry {
  const char* name;
  uint32_t funcptr;
  const char* sig;
};

// On wasm32 a C function pointer IS its index in the indirect function
// table, which is exactly what the injected module's import resolution
// needs. The cast is meaningless on native targets, where the table is
// unused (the list itself stays target-independent).
#ifdef __wasm__
#  define NIGHT_RUNTIME_HELPER_FUNCPTR(name) \
    static_cast<uint32_t>(reinterpret_cast<uintptr_t>(&::name))
#else
#  define NIGHT_RUNTIME_HELPER_FUNCPTR(name) 0u
#endif

#define NIGHT_RUNTIME_HELPER(name)            \
  {#name, NIGHT_RUNTIME_HELPER_FUNCPTR(name), \
   NightHelperSig<decltype(&::name)>::value.data()},
inline const NightHelperEntry kNightHelpers[] = {
    FOR_EACH_NIGHT_RUNTIME_HELPER(NIGHT_RUNTIME_HELPER)};
#undef NIGHT_RUNTIME_HELPER
#undef NIGHT_RUNTIME_HELPER_FUNCPTR

inline constexpr size_t kNightHelperCount =
    sizeof(kNightHelpers) / sizeof(kNightHelpers[0]);

}  // namespace night
}  // namespace js

#endif  // night_runtime_NightHelperList_h
