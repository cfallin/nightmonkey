/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Deterministic textual serialization of a `Source` graph, for
//! differential comparison between Source producers (e.g. the C++
//! live-heap walker vs. the snapshot reader).
//! Regex program bytecode bytes are summarized by length only: the
//! irregexp bytecode is not stable across compiles.

use crate::source::{ObjectData, Primitive, ScopeData, Source, SourceObject, SourceObjectId};
use std::fmt::Write;

fn fmt_id(id: &Option<SourceObjectId>) -> String {
    match id {
        Some(i) if i.is_other() => "OTHER".to_string(),
        Some(i) => format!("{}", i.id()),
        None => "-".to_string(),
    }
}

fn fmt_string(chars: &[u16]) -> String {
    let printable = chars
        .iter()
        .all(|&c| (0x20..0x7f).contains(&c) && c != b'"' as u16 && c != b'\\' as u16);
    if printable {
        let s: String = chars.iter().map(|&c| c as u8 as char).collect();
        format!("\"{s}\"")
    } else {
        let hex: Vec<String> = chars.iter().map(|c| format!("{c:04x}")).collect();
        format!("u16[{}]", hex.join(","))
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

pub fn dump(source: &Source, root: SourceObjectId) -> String {
    let mut out = String::new();
    writeln!(out, "root {}", root.id()).unwrap();
    for (id, obj) in source.objects() {
        let id = id.id();
        match obj {
            SourceObject::Object(ObjectData {
                non_native,
                kind,
                slots_exact: _,
                script,
                name,
                proto,
                builtin_id,
                properties,
                elements,
            }) => {
                let props: Vec<String> = properties
                    .iter()
                    .map(|(k, v)| format!("({},{})", k.id(), v.id()))
                    .collect();
                let elems: Vec<String> = elements
                    .iter()
                    .map(|(i, v)| format!("({},{})", i, v.id()))
                    .collect();
                writeln!(
                    out,
                    "{id} object kind={kind:?} non_native={} script={} name={} proto={} \
                     builtin={:?} props=[{}] elems=[{}]",
                    *non_native as u8,
                    fmt_id(script),
                    fmt_id(name),
                    fmt_id(proto),
                    builtin_id,
                    props.join(","),
                    elems.join(",")
                )
                .unwrap();
            }
            SourceObject::Symbol => {
                writeln!(out, "{id} symbol").unwrap();
            }
            SourceObject::Script(s) => {
                let gcthings: Vec<String> = s
                    .gcthings
                    .iter()
                    .map(|t| {
                        if t.is_other() {
                            "OTHER".to_string()
                        } else {
                            format!("{}", t.id())
                        }
                    })
                    .collect();
                let resume: Vec<String> = s.resume_offsets.iter().map(|o| o.to_string()).collect();
                let trynotes: Vec<String> = s
                    .try_notes
                    .iter()
                    .map(|t| format!("({:?},{},{},{})", t.kind, t.stack_depth, t.start, t.length))
                    .collect();
                let scopenotes: Vec<String> = s
                    .scope_notes
                    .iter()
                    .map(|n| format!("({},{},{})", n.gcthing_index, n.start, n.length))
                    .collect();
                writeln!(
                    out,
                    "{id} script len={} nargs={} gen={} strict={} mapped_args={} body_scope={} \
                     gcthings=[{}] resume=[{}] trynotes=[{}] scopenotes=[{}] code={}",
                    s.bytecode.len(),
                    s.nargs,
                    s.is_generator_or_async as u8,
                    s.strict as u8,
                    s.has_mapped_args as u8,
                    fmt_id(&s.body_scope),
                    gcthings.join(","),
                    resume.join(","),
                    trynotes.join(","),
                    scopenotes.join(","),
                    hex(&s.bytecode)
                )
                .unwrap();
            }
            SourceObject::String(s) => {
                writeln!(out, "{id} string {}", fmt_string(s.chars())).unwrap();
            }
            SourceObject::Primitive(p) => {
                let v = match p {
                    Primitive::Undefined => "undefined".to_string(),
                    Primitive::Null => "null".to_string(),
                    Primitive::Boolean(b) => format!("bool:{b}"),
                    Primitive::Int32(i) => format!("i32:{i}"),
                    Primitive::Double(d) => format!("f64:{:016x}", d.to_bits()),
                };
                writeln!(out, "{id} prim {v}").unwrap();
            }
            SourceObject::Scope(ScopeData {
                kind,
                has_environment,
                enclosing,
                bindings,
                env_slot_values,
                is_named_lambda,
                env_nfixed: _,
            }) => {
                let binds: Vec<String> = bindings
                    .iter()
                    .map(|(n, is_var, slot)| {
                        format!(
                            "({},{},{})",
                            n.id(),
                            *is_var as u8,
                            slot.map(|s| s.to_string())
                                .unwrap_or_else(|| "-".to_string())
                        )
                    })
                    .collect();
                let envs: Vec<String> = env_slot_values
                    .iter()
                    .map(|(s, v)| format!("({},{})", s, v.id()))
                    .collect();
                writeln!(
                    out,
                    "{id} scope kind={kind} env={} enclosing={} named_lambda={} bindings=[{}] \
                     env_values=[{}]",
                    *has_environment as u8,
                    fmt_id(enclosing),
                    *is_named_lambda as u8,
                    binds.join(","),
                    envs.join(",")
                )
                .unwrap();
            }
        }
    }
    for (i, r) in source.regex_programs.iter().enumerate() {
        writeln!(
            out,
            "regex {i} pattern={} flags={} l1_len={} tb_len={} max_regs={} pairs={}",
            fmt_string(&r.pattern),
            r.flags,
            r.latin1_bytecode.len(),
            r.twobyte_bytecode.len(),
            r.num_registers,
            r.pair_count
        )
        .unwrap();
    }
    out
}
