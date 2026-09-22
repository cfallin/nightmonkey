// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! nightmonkey: the external AOT snapshot transform. Reads a wizer snapshot
//! of a SpiderMonkey-in-wasm embedding whose init registered its script
//! roots (JS::NightRegisterRoot), compiles the registered script graph with
//! the night_compiler translator against the snapshot's own exported night_runtime_*
//! helpers, appends the compiled bodies to the module, patches each
//! compiled script's nightFuncIndex_ in the memory image, claims fresh memory
//! for the cell regions and serialized side tables, records everything in
//! the registration block's region table, and re-serializes the module.
//! After resume, JS::NightActivate installs the runtime environment and
//! dispatch begins.

mod finder;
mod image;
mod strip;
#[cfg(all(feature = "wizen", unix))]
mod wizen;

use anyhow::{anyhow, bail, Context, Result};
use night_compiler::env_regions::RegionWords;
use night_compiler::source::Source;
use night_compiler::wasm::{
    build_call_classify_helper, build_elem_append_helper, find_export_func, find_indirect_table,
    layout_env, patch_const, resolve_helpers, serialize_atom_table, serialize_fuse_table,
    serialize_global_binding_table, serialize_layout_table, serialize_regex_table, translate,
    translate_all, HelperPrebuilt, TranslateOut,
};
use night_compiler::Options;
use night_snapshot::registration::{OFF_COMPILED, OFF_REGION_TABLE, OFF_TOOL_VERSION};
use night_snapshot::{walk, Field, Registration, SliceMem};
use std::path::PathBuf;
use waffle::{
    FrontendOptions, FuncDecl, FunctionBody, Module, Operator, SignatureData, Type, ValueDef,
};

const TOOL_VERSION: u32 = 1;

struct Args {
    input: PathBuf,
    output: Option<PathBuf>,
    #[cfg(all(feature = "wizen", unix))]
    shell: Option<PathBuf>,
    #[cfg(all(feature = "wizen", unix))]
    keep_snapshot: Option<PathBuf>,
    keep_names: bool,
    dump_graph: bool,
    opts: Options,
}

#[cfg(all(feature = "wizen", unix))]
const INPUT_USAGE: &str = "  <input>   a .js program (needs --shell), or a pre-made wizer snapshot

Input
  --shell <path>           the wasm JS shell to wizen the program into;
                           required for a .js input
  --keep-snapshot <path>   also write the intermediate wizer snapshot here
";

#[cfg(not(all(feature = "wizen", unix)))]
const INPUT_USAGE: &str = "  <input>   a pre-made wizer snapshot (.wasm)\n";

fn usage() -> String {
    format!(
        "\
usage: nightmonkey [options] <input> -o <output>

{INPUT_USAGE}

Output
  -o <path>                the compiled module
  --keep-names             keep the name and DWARF sections (stripped by default)

Compilation
  --force-interp           leave every script interpreted

Diagnostics
  --stats                  report phase timings and counts
  --dump-opsize            per-op emitted-IR census (static code size)
  --dump-ctxedge           per-continuation-edge ctx fact census
  --dump-clsfact           per-consumer class-fact availability census
  --trace-cell <c>         trace every raise into one analysis cell,
                           arg:<sid>:<n> or local:<sid>:<n>
  --trace-field <name>     trace every heap read/write of one property name
  --trace-site <sid>:<pc>  trace the per-context evaluation of one read site
  --dump-propgap           per-site census of why a property access got no
                           class-fact row (the coverage half of code size)
  --dump-cfg               the CFG, dominator tree and loop nest over the
                           unified pc space, with the loop-extent audit
  --dump-peel              per loop header, the read slots whose single-
                           version join is weaker than the back edge's
                           arrival (the peel rule's census)
  --dump-redundant         per-op census of box round trips, dead boxes and
                           frame round trips in the emitted IR

Instrumentation (CHANGES the generated code; never on in production)
  --census                 emit night_runtime_census calls: per-track version
                           entries and per-arm fork takes, dumped at exit
  --guard-census           emit night_runtime_census calls on every arm of
                           every property/arith speculation point: the
                           per-site guard hit rate, dumped at exit
  --block-census           emit night_runtime_census calls at the head of
                           every block an op's lowering created, with a
                           static per-block record: executed IR per op
  --dump-bytecode[=IDS]    disassemble each script's bytecode; IDS is a
                           comma-separated source-id list (default: all)
  --dump-bbv               dump the per-version BBV state
  --dump-facts <path>      write the analysis fact tables to <path>
  --dump-graph             print the walked script graph and exit
  --viz                    emit the speculation trace for tools/viz.py
  --viz-lower              with --viz, also dump the per-op lowering
  --viz-facts <path>       write the analysis half of the trace to <path>
                           instead of stderr
  -h, --help               print this message
"
    )
}

fn parse_args() -> Result<Args> {
    let mut input = None;
    let mut output = None;
    #[cfg(all(feature = "wizen", unix))]
    let mut shell = None;
    #[cfg(all(feature = "wizen", unix))]
    let mut keep_snapshot = None;
    let mut keep_names = false;
    let mut dump_graph = false;
    let mut opts = Options::default();
    let mut it = std::env::args().skip(1);
    fn val(it: &mut impl Iterator<Item = String>, flag: &str) -> Result<String> {
        it.next()
            .with_context(|| format!("{flag} needs an argument"))
    }
    while let Some(a) = it.next() {
        match a.as_str() {
            "-h" | "--help" => {
                print!("{}", usage());
                std::process::exit(0);
            }
            "-o" => output = Some(PathBuf::from(val(&mut it, "-o")?)),
            #[cfg(all(feature = "wizen", unix))]
            "--shell" => shell = Some(PathBuf::from(val(&mut it, "--shell")?)),
            #[cfg(all(feature = "wizen", unix))]
            "--keep-snapshot" => {
                keep_snapshot = Some(PathBuf::from(val(&mut it, "--keep-snapshot")?))
            }
            "--keep-names" => keep_names = true,
            "--dump-graph" => dump_graph = true,
            "--force-interp" => opts.force_interp = true,
            "--stats" => opts.diagnostics.stats = true,
            "--dump-opsize" => opts.diagnostics.opsize = true,
            "--dump-ctxedge" => opts.diagnostics.ctxedge = true,
            "--dump-clsfact" => opts.diagnostics.clsfact = true,
            "--dump-propgap" => opts.diagnostics.propgap = true,
            "--dump-cfg" => opts.diagnostics.cfg = true,
            "--dump-peel" => opts.diagnostics.peel = true,
            "--dump-redundant" => opts.diagnostics.redundant = true,
            "--trace-cell" => opts.diagnostics.trace_cell = Some(val(&mut it, "--trace-cell")?),
            "--trace-field" => opts.diagnostics.trace_field = Some(val(&mut it, "--trace-field")?),
            "--trace-site" => opts.diagnostics.trace_site = Some(val(&mut it, "--trace-site")?),
            "--census" => opts.instrument.census = true,
            "--guard-census" => opts.instrument.guards = true,
            "--block-census" => opts.instrument.blocks = true,
            "--dump-bytecode" => opts.diagnostics.disasm = Some(Vec::new()),
            _ if a.starts_with("--dump-bytecode=") => {
                let list = &a["--dump-bytecode=".len()..];
                let ids = list
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| {
                        s.parse::<u32>()
                            .with_context(|| format!("bad source id `{s}` in `{a}`"))
                    })
                    .collect::<Result<Vec<u32>>>()?;
                opts.diagnostics.disasm = Some(ids);
            }
            "--dump-bbv" => opts.diagnostics.bbv = true,
            "--dump-facts" => opts.diagnostics.facts = Some(val(&mut it, "--dump-facts")?),
            "--viz" => opts.diagnostics.viz = true,
            "--viz-facts" => opts.diagnostics.viz_facts = Some(val(&mut it, "--viz-facts")?),
            "--viz-lower" => {
                opts.diagnostics.viz = true;
                opts.diagnostics.viz_lower = true;
            }
            _ if a.starts_with('-') && a != "-" => {
                bail!("unknown option `{a}`\n\n{}", usage())
            }
            _ if input.is_none() => input = Some(PathBuf::from(a)),
            _ => bail!("unexpected argument `{a}`\n\n{}", usage()),
        }
    }
    let Some(input) = input else {
        bail!("no input\n\n{}", usage());
    };
    Ok(Args {
        input,
        output,
        #[cfg(all(feature = "wizen", unix))]
        shell,
        #[cfg(all(feature = "wizen", unix))]
        keep_snapshot,
        keep_names,
        dump_graph,
        opts,
    })
}

fn main() -> Result<()> {
    let args = parse_args()?;
    let opts = args.opts;
    let stats = opts.diagnostics.stats;
    let t0 = std::time::Instant::now();
    let input = args.input.display().to_string();
    let bytes = std::fs::read(&args.input).with_context(|| format!("reading {input}"))?;
    #[cfg(all(feature = "wizen", unix))]
    let mut bytes = bytes;
    if !bytes.starts_with(b"\0asm") {
        #[cfg(all(feature = "wizen", unix))]
        {
            let shell = args
                .shell
                .as_deref()
                .context("--shell <wasm> is required when the input is a program")?;
            bytes = wizen::wizen(shell, &args.input)
                .with_context(|| format!("wizening {input} against {}", shell.display()))?;
            if stats {
                eprintln!("nightmonkey: [time] wizen {}ms", t0.elapsed().as_millis());
            }
        }
        #[cfg(not(all(feature = "wizen", unix)))]
        bail!("this nightmonkey build accepts only an existing wizer snapshot (.wasm)");
    }
    #[cfg(all(feature = "wizen", unix))]
    if let Some(path) = &args.keep_snapshot {
        std::fs::write(path, &bytes).with_context(|| format!("writing {}", path.display()))?;
    }
    let t = std::time::Instant::now();
    let mut m = Module::from_wasm_bytes(&bytes, &FrontendOptions::default())
        .map_err(|e| anyhow!("parse snapshot module: {e}"))?;
    if stats {
        eprintln!("nightmonkey: [time] parse {}ms", t.elapsed().as_millis());
    }

    let t = std::time::Instant::now();
    let mut img = image::build_image(&m)?;
    let reg_addr = finder::find_global_data_by_exported_func(&m, "night.registration")
        .context("no night.registration exported constant accessor")?;
    let reg = {
        let mem = SliceMem(&img.bytes);
        Registration::read(&mem, reg_addr)?
    };
    if reg.compiled != 0 {
        bail!("snapshot is already transformed (compiled flag set)");
    }

    if args.dump_graph {
        // Walk the registered roots only (matching night-snapshot-dump's
        // wasmtime-instantiated walk) and print the shared graph dump.
        let mem = SliceMem(&img.bytes);
        let out = walk(&mem, &reg)?;
        print!(
            "{}",
            night_compiler::source::dump::dump(&out.source, out.root_ids[0])
        );
        return Ok(());
    }
    let output = args.output.context("-o <out.wasm> is required")?;

    // Walk the user roots plus the engine-recorded self-hosted roots.
    let n_reg_roots = reg.roots.len();
    let mut wreg = reg;
    for &(addr, _) in &wreg.selfhosted {
        wreg.roots.push(addr);
    }
    let walk_out = {
        let mem = SliceMem(&img.bytes);
        walk(&mem, &wreg)?
    };
    let mut source: Source = walk_out.source;
    let root_id = walk_out.root_ids[0];
    for (i, (_, name)) in wreg.selfhosted.iter().enumerate() {
        let id = walk_out.root_ids[n_reg_roots + i];
        if !source.selfhosted.iter().any(|(sid, _)| *sid == id) {
            source.selfhosted.push((id, name.clone()));
        }
    }
    let n_regex = wreg.regex_programs.len();
    source.regex_programs = std::mem::take(&mut wreg.regex_programs);
    if stats {
        eprintln!(
            "nightmonkey: walked {} objects ({} selfhosted roots, {} regex programs), \
             image+walk {}ms",
            source.objects.len(),
            wreg.selfhosted.len(),
            n_regex,
            t.elapsed().as_millis()
        );
    }

    // Production environment: memory regions claimed past the snapshot's
    // current memory end; helpers resolved as the snapshot's own night_runtime_*
    // exports; compiled bodies placed in the exported funcref table.
    let mem_id = m
        .memories
        .iter()
        .next()
        .ok_or_else(|| anyhow!("module has no memory"))?;
    let fixed_base = u32::try_from(img.len()).context("snapshot memory exceeds 32 bits")?;
    let t = std::time::Instant::now();
    let mut env = layout_env(&source, root_id, fixed_base, &opts).map_err(|e| anyhow!(e))?;
    if stats {
        eprintln!(
            "nightmonkey: [time] layout_env {}ms",
            t.elapsed().as_millis()
        );
    }

    let night_abi_sig = m.signatures.push(SignatureData {
        params: vec![
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I64,
        ],
        returns: vec![Type::I32],
    });
    let indirect_table = find_indirect_table(&m).map_err(|e| anyhow!(e))?;
    let direct_call_stub = {
        let mut body = FunctionBody::new(&m, night_abi_sig);
        let entry = body.entry;
        let i32_ty = body.single_type_list(Type::I32);
        let one = body.add_value(ValueDef::Operator(
            Operator::I32Const { value: 1 },
            Default::default(),
            i32_ty,
        ));
        body.append_to_block(entry, one);
        body.set_terminator(entry, waffle::Terminator::Return { values: vec![one] });
        m.funcs.push(FuncDecl::Body(
            night_abi_sig,
            "night_direct_stub".to_string(),
            body,
        ))
    };
    let (ta_get_poly, ta_set_poly) =
        translate::build_ta_poly_helpers(&mut m, mem_id, env.ta_class_base);
    let ic_get_poly = translate::build_ic_get_helper(&mut m, mem_id, env.mega_get_base);
    let ic_set_cold =
        night_compiler::wasm::build_ic_set_cold_helper(&mut m, mem_id, env.mega_set_base);
    let (elem_mega_get, elem_mega_set_probe) = night_compiler::wasm::build_elem_mega_helpers(
        &mut m,
        mem_id,
        env.mega_get_base,
        env.mega_set_base,
    );
    let call_classify = build_call_classify_helper(&mut m, mem_id, env.fn_class_slot);
    let elem_append_check = build_elem_append_helper(
        &mut m,
        mem_id,
        env.append_cache_base,
        opts.instrument.guards,
    );
    let night_abi_sig2 = m.signatures.push(SignatureData {
        params: vec![
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I32,
            Type::I64,
        ],
        returns: vec![Type::I32, Type::I32],
    });
    let direct_call_stub2 = {
        let mut body = FunctionBody::new(&m, night_abi_sig2);
        let entry = body.entry;
        let i32_ty = body.single_type_list(Type::I32);
        let one = body.add_value(ValueDef::Operator(
            Operator::I32Const { value: 1 },
            Default::default(),
            i32_ty,
        ));
        body.append_to_block(entry, one);
        let zero = body.add_value(ValueDef::Operator(
            Operator::I32Const { value: 0 },
            Default::default(),
            i32_ty,
        ));
        body.append_to_block(entry, zero);
        body.set_terminator(
            entry,
            waffle::Terminator::Return {
                values: vec![one, zero],
            },
        );
        m.funcs.push(FuncDecl::Body(
            night_abi_sig2,
            "night_direct_stub2".to_string(),
            body,
        ))
    };
    let helpers = resolve_helpers(
        &mut m,
        &mut |m, name| find_export_func(m, name),
        HelperPrebuilt {
            mem: mem_id,
            ta_get_poly,
            ta_set_poly,
            ic_get_poly,
            ic_set_cold,
            elem_mega_get,
            elem_mega_set_probe,
            call_classify,
            elem_append_check,
            night_abi_sig,
            indirect_table,
            direct_call_stub,
            night_abi_sig2,
            direct_call_stub2,
        },
        env.helper_bases(),
        opts.diagnostics.viz,
    )
    .map_err(|e| anyhow!(e))?;

    // Snapshot-object stamping candidates: an image object whose
    // oracle-certified slot-exact property list matches a layout row
    // EXACTLY gets the SLOTS-carrying word patched into the image below.
    // This is the population born at wizer init (statics, module-setup
    // singletons), where no compiled ctor ever runs -- without the patch
    // it stays "receiver never stamped" for the whole run.
    let mut snapshot_stamps_short = 0usize;
    let snapshot_stamps: Vec<(u32, u32)> = {
        use night_compiler::source::{ObjectKind, SourceObject};
        let names = &env.facts.names;
        let mut row_of: std::collections::HashMap<Vec<Vec<u16>>, u32> =
            std::collections::HashMap::new();
        // Per layout, the longest row extending it (the clump's extension
        // bound, as `serialize_layout_table` computes it).
        let ext_len: Vec<usize> = env
            .layout_ctors
            .iter()
            .map(|key| {
                let fields = &env.likely_class_layouts[key];
                env.layout_ctors
                    .iter()
                    .map(|e| &env.likely_class_layouts[e])
                    .filter(|ef| ef.len() >= fields.len() && ef[..fields.len()] == fields[..])
                    .map(Vec::len)
                    .max()
                    .unwrap_or(fields.len())
            })
            .collect();
        for (lid, key) in env.layout_ctors.iter().enumerate() {
            let fields = &env.likely_class_layouts[key];
            if fields.is_empty() || fields.len() > 16 {
                continue;
            }
            let chars: Vec<Vec<u16>> = fields
                .iter()
                .map(|&n| names.get(n).chars().to_vec())
                .collect();
            // First row wins on duplicate field lists (layout_ctors is
            // sorted, so the pick is stable).
            row_of.entry(chars).or_insert(u32::try_from(lid).unwrap());
        }
        let global = source.global_object.map(|g| g.id());
        let mut out = Vec::new();
        for (i, o) in source.objects.iter().enumerate() {
            let SourceObject::Object(od) = o else {
                continue;
            };
            if od.non_native
                || od.kind != ObjectKind::Plain
                || !od.slots_exact
                || Some(i as u32) == global
            {
                continue;
            }
            if od.properties.is_empty() || od.properties.len() > 16 {
                continue;
            }
            let mut chars = Vec::with_capacity(od.properties.len());
            let mut ok = true;
            for &(nid, _) in &od.properties {
                match source.object(nid) {
                    SourceObject::String(s) => chars.push(s.chars().to_vec()),
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let Some(&lid) = row_of.get(&chars) else {
                continue;
            };
            let Some(&addr) = walk_out.object_addr.get(&(i as u32)) else {
                continue;
            };
            // An image object was allocated by the interpreter's own
            // sizing (the ctor body's property-count estimate, which a
            // delegating ctor leaves at zero), never by the compiled
            // construct path that reserves the full row: an object whose
            // fixed slots cannot hold its clump's longest extension can
            // never advance past its prefix key.
            let shape = img.read_u32(addr + night_compiler::wasm::stamp::SHAPE_OFFSET)?;
            let flags =
                img.read_u32(shape + night_compiler::wasm::stamp::SHAPE_IMMUTABLE_FLAGS_OFFSET)?;
            let nfixed = (flags >> night_compiler::wasm::stamp::SHAPE_FIXED_SLOTS_SHIFT)
                & night_compiler::wasm::stamp::SHAPE_FIXED_SLOTS_MASK_BITS;
            if (nfixed as usize) < ext_len[lid as usize] {
                snapshot_stamps_short += 1;
            }
            out.push((addr, (lid + 1) | night_compiler::wasm::stamp::SLOTS));
        }
        out
    };

    let t = std::time::Instant::now();
    // The string table moves from the analysis output to the translator here.
    let names = std::mem::take(&mut env.facts.names);
    let out = translate_all(
        &mut m,
        &source,
        root_id,
        &opts,
        helpers,
        &env,
        names,
        mem_id,
        &mut |_| false,
        &mut |_, _| {},
        &mut |_, _| Ok(env.prop_ic_base),
    )
    .map_err(|e| anyhow!(e))?;
    if stats {
        eprintln!(
            "nightmonkey: [time] translate_all {}ms",
            t.elapsed().as_millis()
        );
    }
    let TranslateOut {
        mut atoms,
        sid_to_index,
        fuse_binding_index,
        strlit_patches,
        regex_entries,
        prop_ic_base,
        prop_ic_size,
        call_cells_base,
        call_cells_size,
        alloc_cells_base,
        alloc_cells_size,
        intrinsic_cells_base,
        intrinsic_cells_size,
        ctor_nslots_base,
        ctor_nslots_size,
        ..
    } = out;

    // The table gained the compiled bodies; keep any maximum valid.
    {
        let t = &mut m.tables[indirect_table];
        if let Some(max) = t.max {
            if max < t.initial {
                t.max = Some(t.initial);
            }
        }
    }

    // Serialize the side tables (same order as the production merge: the
    // layout table interns its atoms before the atom table serializes).
    let layout_bytes = serialize_layout_table(&env, &mut atoms);
    for (name, _) in &env.fused_list {
        atoms.intern(*name);
    }
    let atom_bytes = serialize_atom_table(&atoms);
    let gbind_bytes =
        serialize_global_binding_table(&atoms.names, &env.syn_gname_names, &fuse_binding_index);
    let fuse_bytes = serialize_fuse_table(&env, &mut atoms);
    let regex_bytes = serialize_regex_table(&regex_entries);
    let strlit_bytes = atoms.strlit_blob().to_vec();

    // Claim memory after the cell regions for the serialized tables and the
    // string-literal blob; everything else in the claimed range stays zero
    // (== unarmed cells), so it needs no data segments.
    let mut cursor = u32::try_from(ctor_nslots_base + ctor_nslots_size)
        .context("cell regions exceed 32 bits")?;
    let place = |len: usize, align: u32, cursor: &mut u32| -> u32 {
        let base = cursor.next_multiple_of(align);
        *cursor = base + u32::try_from(len).unwrap();
        base
    };
    let atom_addr = place(atom_bytes.len(), 4, &mut cursor);
    let gbind_addr = place(gbind_bytes.len(), 4, &mut cursor);
    let layout_addr = place(layout_bytes.len(), 4, &mut cursor);
    let fuse_addr = place(fuse_bytes.len(), 4, &mut cursor);
    let regex_addr = place(regex_bytes.len(), 4, &mut cursor);
    let strlit_addr = place(strlit_bytes.len(), 8, &mut cursor);
    img.extend_to(cursor as usize);
    img.write_bytes(atom_addr, &atom_bytes)?;
    img.write_bytes(gbind_addr, &gbind_bytes)?;
    img.write_bytes(layout_addr, &layout_bytes)?;
    img.write_bytes(fuse_addr, &fuse_bytes)?;
    img.write_bytes(regex_addr, &regex_bytes)?;
    img.write_bytes(strlit_addr, &strlit_bytes)?;
    patch_const(&mut m, strlit_patches, strlit_addr, 1);

    // Fill the ctor-nslots region: per compiled ctor (keyed by its
    // funcref-table index) the likelier's full-layout slot count in the
    // low half and the ctor's stamp key + 1 in the high half, so a
    // dynamically-classified construct site can both size `this` and seed
    // the keyed alloc word (SLOTS-checkable adds on the generic path).
    let mut n_sized = 0usize;
    for (sid, &idx) in &sid_to_index {
        let script = night_compiler::ids::ScriptId::new(*sid);
        if let Some(&n) = env.ctor_nslots_tx.get(&script) {
            let key = env
                .stamp_ctors_tx
                .get(&script)
                .map_or(0, |si| si.layout_id + 1);
            // An id past the early-key field degrades to keyless (sized
            // but SLOTS-unseeded). The ceiling MUST be the emitter's:
            // this half is shifted straight into the early-key region,
            // where a spilling key would set the RANGES bit.
            let key = if key <= night_compiler::wasm::EARLY_KEY_MAX {
                key
            } else {
                0
            };
            let entry = (n & 0xFFFF) | (key << 16);
            img.write_bytes(
                u32::try_from(ctor_nslots_base).context("nslots base")? + 4 * idx,
                &entry.to_le_bytes(),
            )?;
            n_sized += 1;
        }
    }

    // Patch each compiled script's nightFuncIndex_ in the image.
    let night_func_index_off = wreg.layout.get(Field::baseScriptNightFuncIndex);
    let mut patched = 0usize;
    for (&sid, &index) in &sid_to_index {
        let Some(&script_addr) = walk_out.script_addr.get(&sid) else {
            eprintln!("nightmonkey: script source#{sid} has no heap address");
            continue;
        };
        img.write_u32(script_addr + night_func_index_off, index)?;
        patched += 1;
    }
    // Patch the snapshot-object stamps into the image.
    let mut stamped = 0usize;
    for &(addr, word) in &snapshot_stamps {
        img.write_u32(addr + night_compiler::wasm::stamp::WORD_OFFSET, word)?;
        stamped += 1;
    }
    if stats {
        eprintln!(
            "nightmonkey: {n_sized} ctor-nslots entries, {patched} scripts armed, \
             {stamped} snapshot objects stamped ({snapshot_stamps_short} with fewer fixed \
             slots than their clump's longest row)"
        );
    }

    // Region table: every word an absolute address or a length (this flow has
    // no descriptor-relative offsets). Field names and wire order come from
    // NIGHT_ENV_REGIONS in NightEnv.h via night-compiler's build.rs, so a
    // field added or removed there fails to compile here.
    let region_table = RegionWords {
        atomPtr: atom_addr,
        atomLen: u32::try_from(atom_bytes.len())?,
        gbindPtr: gbind_addr,
        gbindLen: u32::try_from(gbind_bytes.len())?,
        layoutPtr: layout_addr,
        layoutLen: u32::try_from(layout_bytes.len())?,
        fusePtr: fuse_addr,
        fuseLen: u32::try_from(fuse_bytes.len())?,
        regexPtr: regex_addr,
        regexLen: u32::try_from(regex_bytes.len())?,
        gslotsPtr: env.global_slots_base,
        propicPtr: u32::try_from(prop_ic_base)?,
        propicLen: u32::try_from(prop_ic_size)?,
        propicGenPtr: env.prop_ic_gen_base,
        layoutCellsPtr: env.this_cells_base,
        callCellsPtr: u32::try_from(call_cells_base)?,
        callCellsLen: u32::try_from(call_cells_size)?,
        allocCellsPtr: u32::try_from(alloc_cells_base)?,
        allocCellsLen: u32::try_from(alloc_cells_size)?,
        intrinsicCellsPtr: u32::try_from(intrinsic_cells_base)?,
        intrinsicCellsLen: u32::try_from(intrinsic_cells_size)?,
        fuseCellsPtr: env.gname_fuse_base,
        megaGetPtr: env.mega_get_base,
        megaSetPtr: env.mega_set_base,
        mathNativesPtr: env.math_natives_base,
        appendCachePtr: env.append_cache_base,
        accessorCachePtr: env.accessor_cache_base,
    }
    .to_words();
    for (i, w) in region_table.iter().enumerate() {
        img.write_u32(reg_addr + OFF_REGION_TABLE + 4 * i as u32, *w)?;
    }
    img.write_u32(reg_addr + OFF_COMPILED, 1)?;
    img.write_u32(reg_addr + OFF_TOOL_VERSION, TOOL_VERSION)?;

    image::update(&mut m, &img);
    let t = std::time::Instant::now();
    let mut out_bytes = m
        .to_wasm_bytes()
        .map_err(|e| anyhow!("serialize transformed module: {e}"))?;
    let unstripped = out_bytes.len();
    if !args.keep_names {
        out_bytes = strip::strip(&out_bytes)?;
    }
    if stats {
        eprintln!(
            "nightmonkey: [time] to_wasm_bytes {}ms (total {}ms)",
            t.elapsed().as_millis(),
            t0.elapsed().as_millis()
        );
    }
    let out_len = out_bytes.len();
    let output = output.display().to_string();
    std::fs::write(&output, out_bytes).with_context(|| format!("writing {output}"))?;
    if stats {
        eprintln!(
            "nightmonkey: wrote {output}, {out_len} bytes (stripped {}), \
             memory {} -> {} pages",
            unstripped - out_len,
            fixed_base as usize / waffle::WASM_PAGE,
            img.len() / waffle::WASM_PAGE
        );
    }
    Ok(())
}
