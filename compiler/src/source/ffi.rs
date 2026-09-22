/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! FFI interface for SpiderMonkey-side C++ code to build the Source input.

use super::*;
use crate::bytecode::Script;
use crate::ids::JsString;
use crate::ids::Pc;

#[no_mangle]
pub extern "C" fn night_source_new() -> Box<Source> {
    Box::new(Source {
        objects: vec![],
        global_object: None,
        selfhosted: Vec::new(),
        regex_programs: Vec::new(),
    })
}

#[no_mangle]
pub extern "C" fn night_source_delete(_source: Box<Source>) {}

#[no_mangle]
pub extern "C" fn night_source_add_object(source: &mut Source) -> u32 {
    source
        .push(SourceObject::Object(ObjectData {
            slots_exact: false,
            non_native: false,
            kind: ObjectKind::Other,
            script: None,
            name: None,
            proto: None,
            builtin_id: None,
            properties: vec![],
            elements: vec![],
        }))
        .id()
}

/// Mark a live object as a recognized primordial (the identity overlay):
/// transcription reuses the described builtin abstraction keyed by
/// `builtin_id` instead of allocating a fresh one.
#[no_mangle]
pub extern "C" fn night_source_object_set_builtin_id(
    source: &mut Source,
    obj: u32,
    builtin_id: u8,
) {
    let obj = SourceObjectId::new(obj);
    source.object_mut(obj).as_object_mut().builtin_id = Some(builtin_id);
}

/// Mark a live object as the global object (global-from-live): its
/// own properties seed the `Global(name)` bindings.
#[no_mangle]
pub extern "C" fn night_source_set_global_object(source: &mut Source, obj: u32) {
    source.global_object = Some(SourceObjectId::new(obj));
}

#[no_mangle]
pub extern "C" fn night_source_object_set_name(source: &mut Source, obj: u32, new_name: u32) {
    let obj = SourceObjectId::new(obj);
    let new_name = SourceObjectId::new(new_name);
    source.object_mut(obj).as_object_mut().name = Some(new_name);
}

/// Record an object's concrete `[[Prototype]]` (live-heap ingestion). The
/// caller passes only non-primordial protos; primordial/null protos are
/// left unset so transcription synthesizes the proto from the object's
/// kind.
#[no_mangle]
pub extern "C" fn night_source_object_set_proto(source: &mut Source, obj: u32, new_proto: u32) {
    let obj = SourceObjectId::new(obj);
    let new_proto = SourceObjectId::new(new_proto);
    source.object_mut(obj).as_object_mut().proto = Some(new_proto);
}

#[no_mangle]
pub extern "C" fn night_source_add_undefined(source: &mut Source) -> u32 {
    source
        .push(SourceObject::Primitive(Primitive::Undefined))
        .id()
}

#[no_mangle]
pub extern "C" fn night_source_add_null(source: &mut Source) -> u32 {
    source.push(SourceObject::Primitive(Primitive::Null)).id()
}

#[no_mangle]
pub extern "C" fn night_source_add_boolean(source: &mut Source, value: bool) -> u32 {
    source
        .push(SourceObject::Primitive(Primitive::Boolean(value)))
        .id()
}

#[no_mangle]
pub extern "C" fn night_source_add_int32(source: &mut Source, value: i32) -> u32 {
    source
        .push(SourceObject::Primitive(Primitive::Int32(value)))
        .id()
}

#[no_mangle]
pub extern "C" fn night_source_add_double(source: &mut Source, value: f64) -> u32 {
    source
        .push(SourceObject::Primitive(Primitive::Double(value)))
        .id()
}

/// The elements behind an FFI `(ptr, len)` pair, copied out; empty for a
/// null pointer or a zero length.
///
/// # Safety
/// A non-null `ptr` must point to `len` initialized, readable `T`s.
unsafe fn slice_or_empty<T: Copy>(ptr: *const T, len: u32) -> Vec<T> {
    if ptr.is_null() || len == 0 {
        return Vec::new();
    }
    unsafe { core::slice::from_raw_parts(ptr, usize::try_from(len).unwrap()).to_vec() }
}

/// # Safety
/// See [`slice_or_empty`].
#[no_mangle]
pub unsafe extern "C" fn night_source_add_script(
    source: &mut Source,
    bytecode_ptr: *const u8,
    bytecode_len: u32,
) -> u32 {
    let bytecode = unsafe { slice_or_empty(bytecode_ptr, bytecode_len) };
    let script = Script {
        bytecode,
        addr: 0,
        gcthings: vec![],
        resume_offsets: vec![],
        try_notes: vec![],
        scope_notes: vec![],
        body_scope: None,
        nargs: 0,
        is_generator_or_async: false,
        is_class_ctor: false,
        strict: false,
        has_mapped_args: false,
    };
    source.push(SourceObject::Script(script)).id()
}

/// # Safety
/// See [`slice_or_empty`].
#[no_mangle]
pub unsafe extern "C" fn night_source_mark_selfhosted(
    source: &mut Source,
    script: u32,
    name_ptr: *const u8,
    name_len: u32,
) {
    let name = unsafe { slice_or_empty(name_ptr, name_len) };
    let name = String::from_utf8(name).expect("selfhosted name must be UTF-8");
    source.selfhosted.push((SourceObjectId::new(script), name));
}

/// Register one regex literal's irregexp bytecode (both encodings) for AOT
/// matcher compilation. Deduped by (pattern, flags) on the C++ side; a
/// duplicate here is harmless (first entry wins at runtime lookup).
///
/// # Safety
/// See [`slice_or_empty`].
#[no_mangle]
pub unsafe extern "C" fn night_source_add_regex_program(
    source: &mut Source,
    pattern_ptr: *const u16,
    pattern_len: u32,
    flags: u32,
    latin1_ptr: *const u8,
    latin1_len: u32,
    twobyte_ptr: *const u8,
    twobyte_len: u32,
    num_registers: u32,
    pair_count: u32,
) {
    let pattern = JsString::from_chars(unsafe { slice_or_empty(pattern_ptr, pattern_len) });
    let latin1_bytecode = unsafe { slice_or_empty(latin1_ptr, latin1_len) };
    let twobyte_bytecode = unsafe { slice_or_empty(twobyte_ptr, twobyte_len) };
    source.regex_programs.push(RegexProgramSrc {
        pattern,
        flags,
        latin1_bytecode,
        twobyte_bytecode,
        num_registers,
        pair_count,
    });
}

#[no_mangle]
pub extern "C" fn night_source_script_set_nargs(source: &mut Source, script: u32, nargs: u16) {
    let script_id = SourceObjectId::new(script);
    source.object_mut(script_id).as_script_mut().nargs = nargs;
}

#[no_mangle]
pub extern "C" fn night_source_script_set_is_generator_or_async(
    source: &mut Source,
    script: u32,
    value: bool,
) {
    let script_id = SourceObjectId::new(script);
    source
        .object_mut(script_id)
        .as_script_mut()
        .is_generator_or_async = value;
}

#[no_mangle]
pub extern "C" fn night_source_script_set_strictness(
    source: &mut Source,
    script: u32,
    strict: bool,
    has_mapped_args: bool,
) {
    let script_id = SourceObjectId::new(script);
    let script = source.object_mut(script_id).as_script_mut();
    script.strict = strict;
    script.has_mapped_args = has_mapped_args;
}

#[no_mangle]
pub extern "C" fn night_source_add_scope(
    source: &mut Source,
    kind: u8,
    has_environment: bool,
) -> u32 {
    source
        .push(SourceObject::Scope(ScopeData {
            kind,
            has_environment,
            enclosing: None,
            bindings: vec![],
            is_named_lambda: false,
            env_nfixed: None,
            env_slot_values: vec![],
        }))
        .id()
}

/// Record a concrete (env slot, value) pair read from a live CallObject
/// captured by the post-setup snapshot (live-heap ingestion).
#[no_mangle]
pub extern "C" fn night_source_scope_add_env_slot_value(
    source: &mut Source,
    scope: u32,
    slot: u32,
    value: u32,
) {
    let scope = SourceObjectId::new(scope);
    let value = SourceObjectId::new(value);
    source
        .object_mut(scope)
        .as_scope_mut()
        .env_slot_values
        .push((slot, value));
}

#[no_mangle]
pub extern "C" fn night_source_scope_set_is_named_lambda(source: &mut Source, scope: u32) {
    let scope = SourceObjectId::new(scope);
    source.object_mut(scope).as_scope_mut().is_named_lambda = true;
}

#[no_mangle]
pub extern "C" fn night_source_scope_add_binding(
    source: &mut Source,
    scope: u32,
    name: u32,
    is_var: bool,
    has_env_slot: bool,
    env_slot: u32,
) {
    let scope = SourceObjectId::new(scope);
    let name = SourceObjectId::new(name);
    let slot = if has_env_slot { Some(env_slot) } else { None };
    source
        .object_mut(scope)
        .as_scope_mut()
        .bindings
        .push((name, is_var, slot));
}

#[no_mangle]
pub extern "C" fn night_source_scope_set_enclosing(
    source: &mut Source,
    scope: u32,
    new_enclosing: u32,
) {
    let scope = SourceObjectId::new(scope);
    let new_enclosing = SourceObjectId::new(new_enclosing);
    source.object_mut(scope).as_scope_mut().enclosing = Some(new_enclosing);
}

#[no_mangle]
pub extern "C" fn night_source_script_add_scope_note(
    source: &mut Source,
    script: u32,
    gcthing_index: u32,
    start: u32,
    length: u32,
) {
    let script = SourceObjectId::new(script);
    source
        .object_mut(script)
        .as_script_mut()
        .scope_notes
        .push(bytecode::ScopeNote {
            gcthing_index,
            start: Pc::new(start),
            length,
        });
}

#[no_mangle]
pub extern "C" fn night_source_script_set_body_scope(source: &mut Source, script: u32, scope: u32) {
    let script_id = SourceObjectId::new(script);
    let scope = SourceObjectId::new(scope);
    source.object_mut(script_id).as_script_mut().body_scope = Some(scope);
}

/// # Safety
/// See [`slice_or_empty`].
#[no_mangle]
pub unsafe extern "C" fn night_source_add_string_latin1(
    source: &mut Source,
    bytes_ptr: *const u8,
    bytes_len: u32,
) -> u32 {
    let bytes = unsafe { slice_or_empty(bytes_ptr, bytes_len) };
    let codepoints = bytes.iter().map(|b| u16::from(*b)).collect::<Vec<_>>();
    source
        .push(SourceObject::String(JsString::from_chars(codepoints)))
        .id()
}

/// # Safety
/// See [`slice_or_empty`].
#[no_mangle]
pub unsafe extern "C" fn night_source_add_string_wide(
    source: &mut Source,
    codepoints_ptr: *const u16,
    codepoints_len: u32,
) -> u32 {
    let codepoints = unsafe { slice_or_empty(codepoints_ptr, codepoints_len) };
    source
        .push(SourceObject::String(JsString::from_chars(codepoints)))
        .id()
}

#[no_mangle]
pub extern "C" fn night_source_object_set_script(source: &mut Source, obj: u32, script: u32) {
    let obj = SourceObjectId::new(obj);
    let new_script = SourceObjectId::new(script);
    source.object_mut(obj).as_object_mut().script = Some(new_script);
}

#[no_mangle]
pub extern "C" fn night_source_object_add_property(
    source: &mut Source,
    obj: u32,
    key: u32,
    value: u32,
) {
    let obj = SourceObjectId::new(obj);
    let key = SourceObjectId::new(key);
    let value = SourceObjectId::new(value);
    source
        .object_mut(obj)
        .as_object_mut()
        .properties
        .push((key, value));
}

#[no_mangle]
pub extern "C" fn night_source_object_add_element(
    source: &mut Source,
    obj: u32,
    index: u32,
    value: u32,
) {
    let obj = SourceObjectId::new(obj);
    let value = SourceObjectId::new(value);
    source
        .object_mut(obj)
        .as_object_mut()
        .elements
        .push((index, value));
}

#[no_mangle]
pub extern "C" fn night_source_object_set_non_native(source: &mut Source, obj: u32) {
    let obj = SourceObjectId::new(obj);
    source.object_mut(obj).as_object_mut().non_native = true;
}

#[no_mangle]
pub extern "C" fn night_source_object_set_kind(source: &mut Source, obj: u32, raw_kind: u8) {
    let obj = SourceObjectId::new(obj);
    let new_kind = match raw_kind {
        0 => ObjectKind::Other,
        1 => ObjectKind::Plain,
        2 => ObjectKind::Array,
        3 => ObjectKind::Function,
        _ => panic!("invalid ObjectKind"),
    };
    source.object_mut(obj).as_object_mut().kind = new_kind;
}

#[no_mangle]
pub extern "C" fn night_source_script_add_gcthing(source: &mut Source, script: u32, value: u32) {
    let script = SourceObjectId::new(script);
    let value = SourceObjectId::new(value);
    source
        .object_mut(script)
        .as_script_mut()
        .gcthings
        .push(value);
}

#[no_mangle]
pub extern "C" fn night_source_script_add_try_note(
    source: &mut Source,
    script: u32,
    kind: u8,
    stack_depth: u32,
    start: u32,
    length: u32,
) {
    let script = SourceObjectId::new(script);
    let kind = match kind {
        0 => bytecode::TryNoteKind::Catch,
        1 => bytecode::TryNoteKind::Finally,
        2 => bytecode::TryNoteKind::ForIn,
        3 => bytecode::TryNoteKind::Destructuring,
        4 => bytecode::TryNoteKind::ForOf,
        5 => bytecode::TryNoteKind::ForOfIterClose,
        6 => bytecode::TryNoteKind::Loop,
        _ => panic!("invalid TryNoteKind"),
    };
    let note = bytecode::TryNote {
        kind,
        stack_depth,
        start: Pc::new(start),
        length,
    };
    source
        .object_mut(script)
        .as_script_mut()
        .try_notes
        .push(note);
}

/// # Safety
/// See [`slice_or_empty`].
#[no_mangle]
pub unsafe extern "C" fn night_source_script_set_resume_offsets(
    source: &mut Source,
    script: u32,
    offsets_ptr: *const u32,
    offsets_len: u32,
) {
    let script = SourceObjectId::new(script);
    let offsets = unsafe { slice_or_empty(offsets_ptr, offsets_len) };
    source.object_mut(script).as_script_mut().resume_offsets =
        offsets.into_iter().map(Pc::new).collect();
}

/// Write the deterministic textual dump of the Source graph (rooted at
/// `root`) to the NUL-terminated file path. Returns false on I/O failure.
///
/// # Safety
/// `path` must point to a NUL-terminated string.
#[no_mangle]
pub unsafe extern "C" fn night_source_dump_file(
    source: &Source,
    root: u32,
    path: *const core::ffi::c_char,
) -> bool {
    let path = unsafe { core::ffi::CStr::from_ptr(path) };
    let Ok(path) = path.to_str() else {
        return false;
    };
    let text = crate::source::dump::dump(source, SourceObjectId::new(root));
    std::fs::write(path, text).is_ok()
}
