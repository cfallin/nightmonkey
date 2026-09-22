/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

// Generate the layout-descriptor field list from the engine's X-macro so the
// Rust mirror can never drift from NightRegistration.h.
use std::fmt::Write;

fn main() {
    let header = "../runtime/NightRegistration.h";
    println!("cargo:rerun-if-changed={header}");
    let text = std::fs::read_to_string(header).expect("reading NightRegistration.h");
    let start = text
        .find("#define NIGHT_LAYOUT_FIELDS(_)")
        .expect("NIGHT_LAYOUT_FIELDS not found");
    // The macro body ends at the first line that doesn't continue with '\'.
    let mut body = String::new();
    for line in text[start..].lines() {
        body.push_str(line);
        body.push('\n');
        if !line.trim_end().ends_with('\\') {
            break;
        }
    }
    let mut names = Vec::new();
    let mut rest = body.as_str();
    while let Some(pos) = rest.find("_(") {
        rest = &rest[pos + 2..];
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap();
        let name = &rest[..end];
        if !name.is_empty() && rest[end..].starts_with(',') {
            names.push(name.to_string());
        }
    }
    assert!(names.len() > 10, "suspiciously few layout fields parsed");

    let abi_version: u32 = {
        let marker = "NightAotAbiVersion =";
        let pos = text.find(marker).expect("NightAotAbiVersion not found");
        let rest = &text[pos + marker.len()..];
        let end = rest.find(';').expect("unterminated NightAotAbiVersion");
        rest[..end].trim().parse().expect("bad NightAotAbiVersion")
    };

    let mut out = String::new();
    writeln!(
        out,
        "/// Generated from NightRegistration.h NIGHT_LAYOUT_FIELDS."
    )
    .unwrap();
    writeln!(out, "pub const ABI_VERSION: u32 = {abi_version};").unwrap();
    writeln!(out, "#[derive(Clone, Copy, Debug, PartialEq, Eq)]").unwrap();
    writeln!(out, "#[allow(non_camel_case_types)]").unwrap();
    writeln!(out, "#[repr(u32)]").unwrap();
    writeln!(out, "pub enum Field {{").unwrap();
    for n in &names {
        writeln!(out, "    {n},").unwrap();
    }
    writeln!(out, "}}").unwrap();
    writeln!(out, "pub const FIELD_COUNT: usize = {};", names.len()).unwrap();
    let dst = std::path::Path::new(&std::env::var("OUT_DIR").unwrap()).join("layout_fields.rs");
    std::fs::write(dst, out).unwrap();
}
