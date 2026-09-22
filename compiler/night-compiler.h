/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef js_night_compiler_night_compiler_h
#define js_night_compiler_night_compiler_h

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef void night_source_t;
typedef uint32_t night_source_object_t;
const night_source_object_t NIGHT_SOURCE_OTHER = UINT32_MAX;

const uint8_t NIGHT_OBJECT_KIND_OTHER = 0;
const uint8_t NIGHT_OBJECT_KIND_PLAIN = 1;
const uint8_t NIGHT_OBJECT_KIND_ARRAY = 2;
const uint8_t NIGHT_OBJECT_KIND_FUNCTION = 3;

// Primordial-identity overlay ids (live-heap ingestion): a live
// object recognized as one of these is mapped to the described builtin
// abstraction via night_source_object_set_builtin_id. Must match
// BuiltinId::from_u8 in analysis/builtins.rs.
const uint8_t NIGHT_BUILTIN_OBJECT_CTOR = 0;
const uint8_t NIGHT_BUILTIN_OBJECT_PROTO = 1;
const uint8_t NIGHT_BUILTIN_ARRAY_CTOR = 2;
const uint8_t NIGHT_BUILTIN_ARRAY_PROTO = 3;
const uint8_t NIGHT_BUILTIN_FUNCTION_CTOR = 4;
const uint8_t NIGHT_BUILTIN_FUNCTION_PROTO = 5;
const uint8_t NIGHT_BUILTIN_STRING_CTOR = 6;
const uint8_t NIGHT_BUILTIN_STRING_PROTO = 7;
const uint8_t NIGHT_BUILTIN_NUMBER_CTOR = 8;
const uint8_t NIGHT_BUILTIN_NUMBER_PROTO = 9;
const uint8_t NIGHT_BUILTIN_BOOLEAN_CTOR = 10;
const uint8_t NIGHT_BUILTIN_BOOLEAN_PROTO = 11;
const uint8_t NIGHT_BUILTIN_MATH = 12;
const uint8_t NIGHT_BUILTIN_DATE_CTOR = 13;
const uint8_t NIGHT_BUILTIN_DATE_PROTO = 14;
const uint8_t NIGHT_BUILTIN_ERROR_CTOR = 15;
const uint8_t NIGHT_BUILTIN_ERROR_PROTO = 16;
const uint8_t NIGHT_BUILTIN_REGEXP_CTOR = 17;
const uint8_t NIGHT_BUILTIN_REGEXP_PROTO = 18;
const uint8_t NIGHT_BUILTIN_PRINT = 19;
const uint8_t NIGHT_BUILTIN_ASSERT_EQ = 20;
const uint8_t NIGHT_BUILTIN_NONE = 0xff;

night_source_t* night_source_new();

// Write the deterministic textual dump of the Source graph (rooted at
// `root`) to `path`. Returns false on I/O failure.
bool night_source_dump_file(night_source_t* source, night_source_object_t root,
                            const char* path);
void night_source_delete(night_source_t* source);
night_source_object_t night_source_add_object(night_source_t* source);
night_source_object_t night_source_add_script(night_source_t* source,
                                              const uint8_t* bytecode,
                                              uint32_t len);
void night_source_mark_selfhosted(night_source_t* source,
                                  night_source_object_t script,
                                  const uint8_t* name, uint32_t name_len);
void night_source_add_regex_program(
    night_source_t* source, const uint16_t* pattern_chars, uint32_t pattern_len,
    uint32_t flags, const uint8_t* latin1_bc, uint32_t latin1_len,
    const uint8_t* twobyte_bc, uint32_t twobyte_len, uint32_t num_registers,
    uint32_t pair_count);
night_source_object_t night_source_add_string_latin1(night_source_t* source,
                                                     const uint8_t* bytes,
                                                     uint32_t len);
night_source_object_t night_source_add_string_wide(night_source_t* source,
                                                   const uint16_t* codepoints,
                                                   uint32_t len);
night_source_object_t night_source_add_undefined(night_source_t* source);
night_source_object_t night_source_add_null(night_source_t* source);
night_source_object_t night_source_add_boolean(night_source_t* source,
                                               bool value);
night_source_object_t night_source_add_int32(night_source_t* source,
                                             int32_t value);
night_source_object_t night_source_add_double(night_source_t* source,
                                              double value);
void night_source_object_set_non_native(night_source_t* source,
                                        night_source_object_t obj);
void night_source_object_set_kind(night_source_t* source,
                                  night_source_object_t obj, uint8_t kind);
void night_source_object_set_name(night_source_t* source,
                                  night_source_object_t obj,
                                  night_source_object_t name);
void night_source_object_set_script(night_source_t* source,
                                    night_source_object_t obj,
                                    night_source_object_t script);
// Record an object's concrete [[Prototype]] (live-heap ingestion). Only
// non-primordial protos are passed; primordial/null protos are left
// unset so the analysis synthesizes the proto from the object's kind.
void night_source_object_set_proto(night_source_t* source,
                                   night_source_object_t obj,
                                   night_source_object_t proto);
// Mark a live object as a recognized primordial (identity overlay),
// keyed by a NIGHT_BUILTIN_* id: transcription reuses the
// described builtin abstraction instead of transcribing it.
void night_source_object_set_builtin_id(night_source_t* source,
                                        night_source_object_t obj,
                                        uint8_t builtin_id);
// Mark a live object as the global object (global-from-live): its
// own properties seed the Global(name) bindings.
void night_source_set_global_object(night_source_t* source,
                                    night_source_object_t obj);
void night_source_object_add_property(night_source_t* source,
                                      night_source_object_t obj,
                                      night_source_object_t key,
                                      night_source_object_t value);
void night_source_object_add_element(night_source_t* source,
                                     night_source_object_t obj, uint32_t index,
                                     night_source_object_t value);
void night_source_script_add_gcthing(night_source_t* source,
                                     night_source_object_t script,
                                     night_source_object_t value);
void night_source_script_set_resume_offsets(night_source_t* source,
                                            night_source_object_t script,
                                            const uint32_t* offsets,
                                            uint32_t len);
void night_source_script_add_try_note(night_source_t* source,
                                      night_source_object_t script,
                                      uint8_t kind, uint32_t stack_depth,
                                      uint32_t start, uint32_t length);
night_source_object_t night_source_add_scope(night_source_t* source,
                                             uint8_t kind,
                                             bool has_environment);
// Record a binding declared in a scope: its name (a string source
// object), whether it is a `var` binding (vs lexical/formal/...),
// and its environment slot if it is closed-over.
void night_source_scope_add_binding(night_source_t* source,
                                    night_source_object_t scope,
                                    night_source_object_t name, bool is_var,
                                    bool has_env_slot, uint32_t env_slot);
// Mark a scope as a (Strict)NamedLambda scope (holds a named function
// expression's self-name binding, initialized by the VM).
void night_source_scope_set_is_named_lambda(night_source_t* source,
                                            night_source_object_t scope);
// Record a concrete (env slot, value) pair read from a live CallObject
// captured by the post-setup snapshot (live-heap ingestion). Seeds the
// scope's environment abstraction so steady-state GetAliasedVar resolves
// to the captured value.
void night_source_scope_add_env_slot_value(night_source_t* source,
                                           night_source_object_t scope,
                                           uint32_t slot,
                                           night_source_object_t value);
void night_source_scope_set_enclosing(night_source_t* source,
                                      night_source_object_t scope,
                                      night_source_object_t enclosing);
void night_source_script_add_scope_note(night_source_t* source,
                                        night_source_object_t script,
                                        uint32_t gcthing_index, uint32_t start,
                                        uint32_t length);
// Set a script's declared formal-argument count (0 for non-function
// scripts); used to seed the arguments of functions callable from
// outside the closed world.
void night_source_script_set_nargs(night_source_t* source,
                                   night_source_object_t script,
                                   uint16_t nargs);
// Set whether the script is a generator or async function (its call
// result is a VM-created generator/promise object, not its return
// value).
void night_source_script_set_is_generator_or_async(night_source_t* source,
                                                   night_source_object_t script,
                                                   bool value);
// Set the script's strictness flags: strict-mode code, and whether it
// gets a MAPPED arguments object (sloppy + simple formals + uses
// `arguments`; such scripts stay interpreted).
void night_source_script_set_strictness(night_source_t* source,
                                        night_source_object_t script,
                                        bool strict, bool has_mapped_args);
void night_source_script_set_body_scope(night_source_t* source,
                                        night_source_object_t script,
                                        night_source_object_t scope);

// In-process AOT batch build. Compiles the Source graph into wasm-jit-runner
// function blobs (blob i is predicted at funcref-table index table_base + i)
// plus a serialized environment descriptor.
//
// Helper signature strings ("i(ii)" style): "<ret>(<params>)", one char per
// type:
//   i = i32 (pointers, uint32_t/int32_t, bool)
//   j = i64 (uint64_t, boxed JS Values)
//   f = f32
//   d = f64 (double)
//   v = void (return position only)
// Examples: "i(iijj)" is int32_t f(int32_t, int32_t, uint64_t, uint64_t);
// "v(i)" is void f(int32_t).
//
// `alloc` is called exactly twice (fixed layout region, then the prop-IC/
// cell region + string-literal blob) and must return zeroed (calloc-style),
// 8-aligned, non-null memory; it may be called with size 0. The env
// descriptor is a 29-word little-endian u32 header followed by the
// serialized atom/gbind/layout/fuse/regex/strlit tables (offsets into the
// descriptor buffer; region addresses point into the `alloc` regions); the
// header word order is documented in wasm/inprocess.rs (ENV_DESC_WORDS).
// The string-literal payload at [strlit_off, strlit_off+strlit_len) must be
// copied to linear address strlit_addr before compiled code runs.
typedef uint32_t (*night_alloc_fn)(size_t size);
typedef void night_inproc_out_t;
night_inproc_out_t* night_inproc_build(night_source_t* analysis_source,
                                       night_source_object_t root_id,
                                       const char* const* helper_names,
                                       const char* const* helper_sigs,
                                       const uint32_t* helper_funcptrs,
                                       uint32_t n_helpers, uint32_t table_base,
                                       night_alloc_fn alloc);
uint32_t night_inproc_num_blobs(night_inproc_out_t* out);
const uint8_t* night_inproc_blob_ptr(night_inproc_out_t* out, uint32_t i);
uint32_t night_inproc_blob_len(night_inproc_out_t* out, uint32_t i);
uint32_t night_inproc_num_externs(night_inproc_out_t* out);
const uint32_t* night_inproc_extern_indices(night_inproc_out_t* out);
uint32_t night_inproc_num_scripts(night_inproc_out_t* out);
uint32_t night_inproc_script_source_id(night_inproc_out_t* out, uint32_t i);
uint32_t night_inproc_script_blob(night_inproc_out_t* out, uint32_t i);
const uint8_t* night_inproc_env_desc_ptr(night_inproc_out_t* out);
uint32_t night_inproc_env_desc_len(night_inproc_out_t* out);
void night_inproc_delete(night_inproc_out_t* out);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // js_night_compiler_night_compiler_h
