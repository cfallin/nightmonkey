// The runtime's derivatives of the ABI (region table, region shape)
// are generated here from the runtime headers in this tree. The
// engine's opcode table is not: it is generated ahead of time by
// scripts/gen_opcodes.py and checked in under src/opcodes/, one file
// per engine version.
fn main() {
    let out_dir = std::env::var("OUT_DIR").unwrap();

    write_env_regions(&out_dir);
    write_region_shape(&out_dir);
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
