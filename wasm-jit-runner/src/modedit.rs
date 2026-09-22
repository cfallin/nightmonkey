/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Stream-editing of the guest module so that all of its memories, tables and
//! globals are exported under synthetic names. The runner needs handles to
//! these items at runtime so that dynamically-added functions can import them
//! (and so we can append new entries to the funcptr table).

use std::ops::Range;

use anyhow::Result;
use wasmparser::{Parser, Payload, TypeRef};

/// Synthetic export-name prefixes. Chosen to be very unlikely to collide with
/// names a real toolchain would emit.
pub const MEM_PREFIX: &str = "__wjr_mem";
pub const TABLE_PREFIX: &str = "__wjr_table";
pub const GLOBAL_PREFIX: &str = "__wjr_global";

/// Number of memories / tables / globals in the (edited) guest module. Each is
/// exported as `<prefix><index>` for index in `0..count`.
#[derive(Clone, Copy, Debug)]
pub struct ModuleLayout {
    pub n_mem: u32,
    pub n_table: u32,
    pub n_global: u32,
}

fn map_kind(k: wasmparser::ExternalKind) -> wasm_encoder::ExportKind {
    use wasm_encoder::ExportKind as X;
    use wasmparser::ExternalKind as E;
    match k {
        E::Func => X::Func,
        E::Table => X::Table,
        E::Memory => X::Memory,
        E::Global => X::Global,
        E::Tag => X::Tag,
        // `FuncExact` (typed function references) is still a function export as
        // far as the export *kind* byte is concerned.
        E::FuncExact => X::Func,
    }
}

/// Build the export section: any pre-existing exports, followed by a synthetic
/// export for every memory, table and global.
fn build_export_section(
    existing: &[(String, wasmparser::ExternalKind, u32)],
    layout: ModuleLayout,
) -> wasm_encoder::ExportSection {
    use wasm_encoder::ExportKind;
    let mut sec = wasm_encoder::ExportSection::new();
    for (name, kind, index) in existing {
        sec.export(name, map_kind(*kind), *index);
    }
    for i in 0..layout.n_mem {
        sec.export(&format!("{MEM_PREFIX}{i}"), ExportKind::Memory, i);
    }
    for i in 0..layout.n_table {
        sec.export(&format!("{TABLE_PREFIX}{i}"), ExportKind::Table, i);
    }
    for i in 0..layout.n_global {
        sec.export(&format!("{GLOBAL_PREFIX}{i}"), ExportKind::Global, i);
    }
    sec
}

/// For a section payload we copy through verbatim, return its section id and the
/// byte range of its contents (which `range()` already excludes the id/size
/// header from). Returns `None` for payloads we handle specially, for the
/// per-entry code payloads (covered by `CodeSectionStart`'s range), and for
/// non-section payloads such as the header and end markers.
fn passthrough_section(payload: &Payload) -> Option<(u8, Range<usize>)> {
    Some(match payload {
        Payload::CustomSection(r) => (0, r.range()),
        Payload::TypeSection(r) => (1, r.range()),
        Payload::FunctionSection(r) => (3, r.range()),
        Payload::StartSection { range, .. } => (8, range.clone()),
        Payload::ElementSection(r) => (9, r.range()),
        Payload::CodeSectionStart { range, .. } => (10, range.clone()),
        Payload::DataSection(r) => (11, r.range()),
        Payload::DataCountSection { range, .. } => (12, range.clone()),
        Payload::TagSection(r) => (13, r.range()),
        _ => return None,
    })
}

/// Rewrite `wasm` so that every memory, table and global is exported under a
/// synthetic name (in addition to any existing exports), and so that every
/// table type has its maximum stripped (making the funcptr table growable, so
/// the guest needs no `-Wl,--growable-table`). Returns the new module bytes plus
/// the layout describing how many of each item exist.
pub fn add_item_exports(wasm: &[u8]) -> Result<(Vec<u8>, ModuleLayout)> {
    use wasm_encoder::reencode::{Reencode, RoundtripReencoder};
    use wasm_encoder::{EntityType, RawSection};

    let mut module = wasm_encoder::Module::new();
    let (mut n_mem, mut n_table, mut n_global) = (0u32, 0u32, 0u32);
    let mut exports_done = false;
    let mut reenc = RoundtripReencoder;
    let reencode_err =
        |e: wasm_encoder::reencode::Error| anyhow::anyhow!("re-encoding module: {e:?}");

    // Single pass over wasmparser's per-section payloads, emitting each section
    // (in order) into the output. Most sections are copied verbatim via their
    // content range; the import, table and export sections are rebuilt. Counts
    // of memories/tables/globals are complete by the time we reach the export
    // section (or, for modules with none, the first section that follows it).
    for payload in Parser::new(0).parse_all(wasm) {
        let payload = payload?;
        let layout = ModuleLayout {
            n_mem,
            n_table,
            n_global,
        };

        // If the module has no export section, insert one just before the first
        // section that must follow exports (section id >= 8).
        if !exports_done {
            if let Some((id, _)) = passthrough_section(&payload) {
                if id >= 8 {
                    module.section(&build_export_section(&[], layout));
                    exports_done = true;
                }
            }
        }

        match payload {
            Payload::ImportSection(reader) => {
                let mut isec = wasm_encoder::ImportSection::new();
                for imp in reader.into_imports() {
                    let imp = imp?;
                    match imp.ty {
                        TypeRef::Memory(_) => n_mem += 1,
                        TypeRef::Table(_) => n_table += 1,
                        TypeRef::Global(_) => n_global += 1,
                        _ => {}
                    }
                    // Strip the maximum off imported tables so they stay growable.
                    let mut ety = reenc.entity_type(imp.ty).map_err(reencode_err)?;
                    if let EntityType::Table(t) = &mut ety {
                        t.maximum = None;
                    }
                    isec.import(imp.module, imp.name, ety);
                }
                module.section(&isec);
            }
            Payload::TableSection(reader) => {
                n_table += reader.count();
                let mut tsec = wasm_encoder::TableSection::new();
                for table in reader {
                    let table = table?;
                    let mut ty = reenc.table_type(table.ty).map_err(reencode_err)?;
                    ty.maximum = None; // make the funcptr table growable
                    match table.init {
                        wasmparser::TableInit::RefNull => {
                            tsec.table(ty);
                        }
                        wasmparser::TableInit::Expr(e) => {
                            tsec.table_with_init(ty, &reenc.const_expr(e).map_err(reencode_err)?);
                        }
                    }
                }
                module.section(&tsec);
            }
            Payload::MemorySection(reader) => {
                n_mem += reader.count();
                module.section(&RawSection {
                    id: 5,
                    data: &wasm[reader.range()],
                });
            }
            Payload::GlobalSection(reader) => {
                n_global += reader.count();
                module.section(&RawSection {
                    id: 6,
                    data: &wasm[reader.range()],
                });
            }
            Payload::ExportSection(reader) => {
                let mut existing = Vec::new();
                for e in reader {
                    let e = e?;
                    existing.push((e.name.to_string(), e.kind, e.index));
                }
                module.section(&build_export_section(&existing, layout));
                exports_done = true;
            }
            other => {
                if let Some((id, range)) = passthrough_section(&other) {
                    module.section(&RawSection {
                        id,
                        data: &wasm[range],
                    });
                }
            }
        }
    }

    let layout = ModuleLayout {
        n_mem,
        n_table,
        n_global,
    };
    if !exports_done {
        module.section(&build_export_section(&[], layout));
    }

    Ok((module.finish(), layout))
}
