//! `--viz`: one JSON record per script for `tools/viz.py`, the
//! source | bytecode | MIR | waffle IR visualizer. A record holds the
//! script's source position and pc -> line table (from the snapshot), its
//! bytecode ops with decoded operands, and, for a script MIR compiled, its
//! MIR (each instruction marked `;;@i<index> pc=<pc> s=<script>`) and its
//! lowered body (each value marked `;;@i<index>` with the instruction that
//! emitted it): the links between the columns. Diagnostics only.

use crate::bytecode::{JSOp, Script};
use crate::source::{Source, SourceObject};
use std::fmt::Write;

/// `s` as a JSON string literal.
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => write!(out, "\\u{:04x}", c as u32).unwrap(),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A gcthing operand, as text: a string's characters, else its kind.
fn gcthing(source: &Source, script: &Script, index: u32) -> String {
    let Some(&id) = script.gcthings.get(index as usize) else {
        return format!("#{index}?");
    };
    if id.is_other() {
        return format!("#{index}");
    }
    match source.object(id) {
        SourceObject::String(s) => {
            let t = String::from_utf16_lossy(s.chars());
            let t = if t.chars().count() > 60 {
                let mut short: String = t.chars().take(57).collect();
                short.push_str("...");
                short
            } else {
                t
            };
            format!("{t:?}")
        }
        SourceObject::Script(_) => format!("script#{}", id.id()),
        SourceObject::Scope(_) => format!("scope#{}", id.id()),
        _ => format!("object#{}", id.id()),
    }
}

/// An op's operands as text, by its format (Opcodes.h's `JOF_` type).
fn operands(source: &Source, script: &Script, pc: u32, op: JSOp) -> String {
    let start = pc as usize + 1;
    let end = (pc + op.len()) as usize;
    let Some(imm) = script.bytecode.get(start..end) else {
        return String::new();
    };
    let le = |b: &[u8]| b.iter().rev().fold(0u64, |a, &x| (a << 8) | u64::from(x));
    let u32_at = |i: usize| imm.get(i..i + 4).map_or(0, |b| le(b) as u32);
    match op.format() {
        "BYTE" => String::new(),
        "JUMP" => format!("-> {}", i64::from(pc) + i64::from(u32_at(0) as i32)),
        "ATOM" | "STRING" | "OBJECT" | "REGEXP" | "SCOPE" | "BIGINT" | "GCTHING" | "SHAPE" => {
            gcthing(source, script, u32_at(0))
        }
        "INT8" => format!("{}", imm[0] as i8),
        "INT32" => format!("{}", u32_at(0) as i32),
        "UINT8" | "UINT16" | "UINT24" | "UINT32" | "ARGC" | "QARG" | "LOCAL" | "RESUMEINDEX" | "ICINDEX" => {
            format!("{}", le(imm))
        }
        "ENVCOORD" if imm.len() >= 5 => format!("hops {} slot {}", le(&imm[..2]), le(&imm[2..5])),
        "DOUBLE" if imm.len() >= 8 => format!("{}", f64::from_bits(le(&imm[..8]))),
        _ => imm.iter().map(|b| format!("{b:02x}")).collect::<Vec<_>>().join(" "),
    }
}

/// The record for one script (one line of the `--viz` file).
pub fn record(
    source: &Source,
    sid: u32,
    script: &Script,
    name: Option<&str>,
    tier: &str,
    texts: Option<&(String, String)>,
) -> String {
    let mut out = String::new();
    write!(out, "{{\"sid\":{sid},\"name\":{},\"nargs\":{},\"tier\":{}", json_str(name.unwrap_or("")), script.nargs, json_str(tier)).unwrap();
    if let Some(p) = &script.pos {
        write!(
            out,
            ",\"pos\":{{\"line\":{},\"column\":{},\"start\":{},\"end\":{}}}",
            p.line, p.column, p.source_start, p.source_end
        )
        .unwrap();
        let lines: Vec<String> = p.lines.iter().map(|(pc, l, c)| format!("[{},{l},{c}]", pc.get())).collect();
        write!(out, ",\"lines\":[{}]", lines.join(",")).unwrap();
    }
    let mut ops = vec![];
    let mut pc = 0u32;
    while (pc as usize) < script.bytecode.len() {
        let Some(op) = JSOp::from_byte(script.bytecode[pc as usize]) else {
            break;
        };
        ops.push(format!("[{pc},{},{}]", json_str(&format!("{op:?}")), json_str(&operands(source, script, pc, op))));
        pc += op.len().max(1);
    }
    write!(out, ",\"ops\":[{}]", ops.join(",")).unwrap();
    if let Some((mir, waffle)) = texts {
        write!(out, ",\"mir\":{},\"waffle\":{}", json_str(mir), json_str(waffle)).unwrap();
    }
    // What the analysis knows: script-wide lines, and per pc the pushed
    // values' types and the site's rows.
    let view = crate::likelier::viz::VIEW
        .lock()
        .unwrap()
        .as_mut()
        .and_then(|v| v.scripts.remove(&sid));
    if let Some(v) = view {
        let list = |l: &[String]| l.iter().map(|t| json_str(t)).collect::<Vec<_>>().join(",");
        let sites: Vec<String> = v
            .sites
            .iter()
            .map(|(pc, (pushed, rows))| format!("\"{pc}\":[[{}],[{}]]", list(pushed), list(rows)))
            .collect();
        write!(out, ",\"facts\":{{\"script\":[{}],\"sites\":{{{}}}}}", list(&v.script), sites.join(",")).unwrap();
    }
    out.push('}');
    out
}

/// The record of the predicted layouts the facts name (`L<key>`): one
/// line, `{"layouts":{"<key>":"<fields>",...}}`.
pub fn layouts_record() -> Option<String> {
    let guard = crate::likelier::viz::VIEW.lock().unwrap();
    let v = guard.as_ref()?;
    let l: Vec<String> = v.layouts.iter().map(|(k, t)| format!("\"{k}\":{}", json_str(t))).collect();
    Some(format!("{{\"layouts\":{{{}}}}}", l.join(",")))
}
