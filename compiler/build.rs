/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

fn main() {
    use std::fmt::Write;

    let out_dir = std::env::var("OUT_DIR").unwrap();
    let opcodes_rs = std::path::Path::new(&out_dir).join("opcodes.rs");

    write_env_regions(&out_dir);
    write_region_shape(&out_dir);

    let ops = read_opcodes();

    let mut out = String::new();
    writeln!(
        &mut out,
        "#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]"
    )
    .unwrap();
    writeln!(&mut out, "#[repr(u16)]").unwrap();
    writeln!(&mut out, "pub enum JSOp {{").unwrap();
    for opcode in &ops {
        writeln!(&mut out, "    {},", opcode.name).unwrap();
    }
    writeln!(&mut out, "}}").unwrap();
    writeln!(&mut out, "#[allow(clippy::len_without_is_empty)]").unwrap();
    writeln!(&mut out, "impl JSOp {{").unwrap();
    writeln!(
        &mut out,
        "    pub fn from_byte(value: u8) -> Option<JSOp> {{"
    )
    .unwrap();
    writeln!(&mut out, "        match value {{").unwrap();
    for (i, opcode) in ops.iter().enumerate() {
        writeln!(
            &mut out,
            "            {} => Some(JSOp::{}),",
            i, opcode.name
        )
        .unwrap();
    }
    for i in ops.len()..256 {
        writeln!(&mut out, "            {} => None,", i).unwrap();
    }
    writeln!(&mut out, "        }}").unwrap();
    writeln!(&mut out, "    }}").unwrap();
    writeln!(&mut out, "    pub fn len(&self) -> u32 {{").unwrap();
    writeln!(&mut out, "        match self {{").unwrap();
    for opcode in &ops {
        writeln!(
            &mut out,
            "            JSOp::{} => {},",
            opcode.name, opcode.len
        )
        .unwrap();
    }
    writeln!(&mut out, "        }}").unwrap();
    writeln!(&mut out, "    }}").unwrap();
    writeln!(&mut out, "    pub fn nuses(&self) -> Option<u32> {{").unwrap();
    writeln!(&mut out, "        match self {{").unwrap();
    for opcode in &ops {
        if opcode.nuses < 0 {
            writeln!(&mut out, "            JSOp::{} => None,", opcode.name).unwrap();
        } else {
            writeln!(
                &mut out,
                "            JSOp::{} => Some({}),",
                opcode.name, opcode.nuses
            )
            .unwrap();
        }
    }
    writeln!(&mut out, "        }}").unwrap();
    writeln!(&mut out, "    }}").unwrap();
    writeln!(&mut out, "    pub fn ndefs(&self) -> u32 {{").unwrap();
    writeln!(&mut out, "        match self {{").unwrap();
    for opcode in &ops {
        writeln!(
            &mut out,
            "            JSOp::{} => {},",
            opcode.name, opcode.ndefs
        )
        .unwrap();
    }
    writeln!(&mut out, "        }}").unwrap();
    writeln!(&mut out, "    }}").unwrap();
    writeln!(&mut out, "}}").unwrap();
    std::fs::write(&opcodes_rs, &out).unwrap();
}

fn runtime_header(name: &str) -> String {
    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let path = std::path::Path::new(&dir)
        .join("..")
        .join("runtime")
        .join(name);
    println!("cargo:rerun-if-changed={}", path.display());
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()))
}

// `static constexpr uint32_t <name> = <literal>;`
fn scrape_u32(text: &str, name: &str) -> u32 {
    let marker = format!("{name} =");
    let pos = text
        .find(&marker)
        .unwrap_or_else(|| panic!("{name} not found"));
    let rest = &text[pos + marker.len()..];
    let end = rest
        .find(';')
        .unwrap_or_else(|| panic!("unterminated {name}"));
    rest[..end]
        .trim()
        .parse()
        .unwrap_or_else(|e| panic!("bad {name}: {e}"))
}

/// Generate the region-descriptor mirror from NightEnv.h's NIGHT_ENV_REGIONS
/// X-macro: the same names, the same order, the same wire kinds the engine
/// compiles into `NightEnvDesc`. Both writers (the snapshot tool's
/// `regionTable` and the in-process `env_desc`) fill the generated
/// `RegionWords` struct, so a field added, removed or renamed in the header
/// is a Rust *compile* error at every writer, not a runtime surprise.
fn write_env_regions(out_dir: &str) {
    use std::fmt::Write;

    let env_h = runtime_header("NightEnv.h");
    let reg_h = runtime_header("NightRegistration.h");
    let abi_version = scrape_u32(&reg_h, "NightAotAbiVersion");
    let header_words = scrape_u32(&env_h, "NightEnvDescHeaderWords");

    let start = env_h
        .find("#define NIGHT_ENV_REGIONS(_)")
        .expect("NIGHT_ENV_REGIONS not found");
    let mut body = String::new();
    for line in env_h[start..].lines() {
        body.push_str(line);
        body.push('\n');
        if !line.trim_end().ends_with('\\') {
            break;
        }
    }
    let mut regions: Vec<(String, String)> = Vec::new();
    let mut rest = body.as_str();
    while let Some(pos) = rest.find("_(") {
        rest = &rest[pos + 2..];
        let Some((args, tail)) = rest.split_once(')') else {
            break;
        };
        rest = tail;
        let Some((name, kind)) = args.split_once(',') else {
            continue;
        };
        let (name, kind) = (name.trim(), kind.trim());
        if name.is_empty() || !matches!(kind, "Table" | "Len" | "Addr") {
            continue;
        }
        regions.push((name.to_string(), kind.to_string()));
    }
    assert!(
        regions.len() > 10,
        "suspiciously few NIGHT_ENV_REGIONS entries parsed"
    );

    let mut out = String::new();
    writeln!(out, "// Generated from NightEnv.h NIGHT_ENV_REGIONS.").unwrap();
    writeln!(out, "pub const ABI_VERSION: u32 = {abi_version};").unwrap();
    writeln!(
        out,
        "pub const ENV_DESC_HEADER_WORDS: usize = {header_words};"
    )
    .unwrap();
    writeln!(out, "pub const REGION_COUNT: usize = {};", regions.len()).unwrap();
    writeln!(out, "#[derive(Clone, Copy, Debug, PartialEq, Eq)]").unwrap();
    writeln!(out, "pub enum RegionKind {{").unwrap();
    writeln!(out, "    Table,").unwrap();
    writeln!(out, "    Len,").unwrap();
    writeln!(out, "    Addr,").unwrap();
    writeln!(out, "}}").unwrap();
    writeln!(
        out,
        "pub const REGION_KINDS: [RegionKind; REGION_COUNT] = ["
    )
    .unwrap();
    for (_, kind) in &regions {
        writeln!(out, "    RegionKind::{kind},").unwrap();
    }
    writeln!(out, "];").unwrap();
    writeln!(out, "pub const REGION_NAMES: [&str; REGION_COUNT] = [").unwrap();
    for (name, _) in &regions {
        writeln!(out, "    \"{name}\",").unwrap();
    }
    writeln!(out, "];").unwrap();
    writeln!(
        out,
        "/// The region words, by name. `to_words` orders them for the wire."
    )
    .unwrap();
    writeln!(out, "#[allow(non_snake_case)]").unwrap();
    writeln!(out, "#[derive(Clone, Copy, Debug, Default)]").unwrap();
    writeln!(out, "pub struct RegionWords {{").unwrap();
    for (name, _) in &regions {
        writeln!(out, "    pub {name}: u32,").unwrap();
    }
    writeln!(out, "}}").unwrap();
    writeln!(out, "impl RegionWords {{").unwrap();
    writeln!(out, "    pub fn to_words(&self) -> [u32; REGION_COUNT] {{").unwrap();
    writeln!(out, "        [").unwrap();
    for (name, _) in &regions {
        writeln!(out, "            self.{name},").unwrap();
    }
    writeln!(out, "        ]").unwrap();
    writeln!(out, "    }}").unwrap();
    writeln!(out, "}}").unwrap();
    std::fs::write(std::path::Path::new(out_dir).join("env_regions.rs"), out).unwrap();
}

/// Generate the region-shape mirror from NightRegionShape.h's
/// NIGHT_REGION_SHAPE X-macro: every entry stride, table size and
/// intra-region offset the compiled code and the runtime both index with.
/// One literal with two generated consumers, so the two sides' copies of a
/// layout constant cannot drift apart -- the one silent-miscompile class
/// the tier's guards cannot cover.
fn write_region_shape(out_dir: &str) {
    use std::fmt::Write;

    let text = runtime_header("NightRegionShape.h");
    let start = text
        .find("#define NIGHT_REGION_SHAPE(_)")
        .expect("NIGHT_REGION_SHAPE not found");
    let mut body = String::new();
    for line in text[start..].lines() {
        body.push_str(line);
        body.push('\n');
        if !line.trim_end().ends_with('\\') {
            break;
        }
    }
    // Comment lines inside the macro body also contain "_(" -free text, but a
    // `/* ... */` run could in principle hold one; strip comments first so the
    // parse sees only entries.
    let mut stripped = String::new();
    let mut rest = body.as_str();
    while let Some(pos) = rest.find("/*") {
        stripped.push_str(&rest[..pos]);
        match rest[pos..].find("*/") {
            Some(end) => rest = &rest[pos + end + 2..],
            None => {
                rest = "";
                break;
            }
        }
    }
    stripped.push_str(rest);

    let mut entries: Vec<(String, u32)> = Vec::new();
    let mut rest = stripped.as_str();
    while let Some(pos) = rest.find("_(") {
        rest = &rest[pos + 2..];
        let Some((args, tail)) = rest.split_once(')') else {
            break;
        };
        rest = tail;
        let Some((name, value)) = args.split_once(',') else {
            continue;
        };
        let name = name.trim();
        let value: u32 = value
            .trim()
            .parse()
            .unwrap_or_else(|e| panic!("NIGHT_REGION_SHAPE {name} is not a literal: {e}"));
        assert!(!name.is_empty());
        entries.push((name.to_string(), value));
    }
    assert!(
        entries.len() > 20,
        "suspiciously few NIGHT_REGION_SHAPE entries parsed"
    );

    let mut out = String::new();
    writeln!(
        out,
        "// Generated from NightRegionShape.h NIGHT_REGION_SHAPE."
    )
    .unwrap();
    for (name, value) in &entries {
        writeln!(out, "pub const {}: u32 = {value};", screaming(name)).unwrap();
    }
    std::fs::write(std::path::Path::new(out_dir).join("region_shape.rs"), out).unwrap();
}

/// `inlineIcWayBytes` -> `INLINE_IC_WAY_BYTES`.
fn screaming(name: &str) -> String {
    let mut out = String::new();
    for c in name.chars() {
        if c.is_ascii_uppercase() && !out.is_empty() {
            out.push('_');
        }
        out.push(c.to_ascii_uppercase());
    }
    out
}

struct Opcode {
    name: String,
    len: u32,
    nuses: i32,
    ndefs: u32,
}

/// The engine's opcode table. `NIGHT_OPCODES_H` names the file directly;
/// otherwise it is `$SPIDERMONKEY_DIST/include-private/vm/Opcodes.h`, the
/// private-header export of a SpiderMonkey build made with
/// --enable-external-compiler-hooks.
fn opcodes_path() -> std::path::PathBuf {
    println!("cargo:rerun-if-env-changed=NIGHT_OPCODES_H");
    println!("cargo:rerun-if-env-changed=SPIDERMONKEY_DIST");
    if let Ok(p) = std::env::var("NIGHT_OPCODES_H") {
        return std::path::PathBuf::from(p);
    }
    if let Ok(dist) = std::env::var("SPIDERMONKEY_DIST") {
        return std::path::Path::new(&dist)
            .join("include-private")
            .join("vm")
            .join("Opcodes.h");
    }
    panic!(
        "set SPIDERMONKEY_DIST to the dist/ directory of a SpiderMonkey build \
         made with --enable-external-compiler-hooks (or NIGHT_OPCODES_H to \
         its vm/Opcodes.h)"
    );
}

/// A `#define NAME <number>` in a C header.
fn defined_number(text: &str, name: &str, what: &str) -> u32 {
    text.lines()
        .find_map(|l| {
            let l = l.trim();
            let rest = l.strip_prefix("#define ")?.trim_start();
            let rest = rest.strip_prefix(name)?;
            rest.trim().split_whitespace().next()?.parse().ok()
        })
        .unwrap_or_else(|| panic!("{what}: no `#define {name} <number>`"))
}

/// The engine's bytecode semantics version must match the one the lowerings
/// were written for (runtime/NightOpcodeVersion.h); see that header.
fn check_semantics_version(opcodes_file: &str, opcodes_path: &std::path::Path) {
    let ours_path = std::path::Path::new(&std::env::var("CARGO_MANIFEST_DIR").unwrap())
        .join("..")
        .join("runtime")
        .join("NightOpcodeVersion.h");
    println!("cargo:rerun-if-changed={}", ours_path.display());
    let ours_text = std::fs::read_to_string(&ours_path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", ours_path.display()));
    let theirs = defined_number(opcodes_file, "JSOP_SEMANTICS_VERSION", &opcodes_path.display().to_string());
    let ours = defined_number(&ours_text, "NIGHT_JSOP_SEMANTICS_VERSION", &ours_path.display().to_string());
    if theirs != ours {
        panic!(
            "SpiderMonkey bytecode semantics version {theirs} ({}) does not match the \
             version NightMonkey's lowerings were written for, {ours} ({}): review \
             compiler/src/opsem.rs and the lowerings against vm/Opcodes.h, then raise \
             NIGHT_JSOP_SEMANTICS_VERSION",
            opcodes_path.display(),
            ours_path.display()
        );
    }
}

fn read_opcodes() -> Vec<Opcode> {
    let path = opcodes_path();
    println!("cargo:rerun-if-changed={}", path.display());
    let opcodes_file = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    check_semantics_version(std::str::from_utf8(&opcodes_file).unwrap(), &path);
    let opcodes_file = std::str::from_utf8(&opcodes_file).unwrap();

    let mut in_opcodes = false;
    let mut ret = vec![];
    for line in opcodes_file.lines() {
        if !in_opcodes && line.contains("#define FOR_EACH_OPCODE") {
            in_opcodes = true;
        } else if line.contains("FOR_EACH_TRAILING_UNUSED_OPCODE") {
            break;
        } else if in_opcodes {
            if let Some(start) = line.find("MACRO(") {
                let start = start + 6;
                let end = line.find(")").unwrap();
                let fields = &line[start..end];
                let split = fields.split(",").collect::<Vec<_>>();
                let name = split[0].trim().to_string();
                let len = split[3].trim().parse::<u32>().unwrap();
                let nuses = split[4].trim().parse::<i32>().unwrap();
                let ndefs = split[5].trim().parse::<u32>().unwrap();
                ret.push(Opcode {
                    name,
                    len,
                    nuses,
                    ndefs,
                });
            }
        }
    }
    ret
}
