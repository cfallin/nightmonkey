//! DWARF for `--debug-info` builds: source-level debug info for the
//! baseline bodies of the program's own scripts.
//!
//! A `--debug-info` build compiles every script with the baseline tier
//! only, because baseline keeps the whole JS frame in NightStack memory at
//! a layout that is a function of the script alone (`baseline::layout`):
//! every argument, local and the environment chain sits in a boxed
//! `JS::Value` slot at a fixed offset from the body's `sp` parameter. That
//! makes the debug info simple and exact at every instruction:
//!
//! - **Lines.** Baseline tags each waffle value with the bytecode pc of
//!   the op it implements (frame setup gets [`PROLOGUE_LOC`]); waffle's
//!   backend reports the code offset of each tagged instruction; and the
//!   engine's source notes (the snapshot digest's per-script positions)
//!   map each pc to a line and column.
//! - **Frames.** `DW_AT_frame_base` is the `sp` parameter (Wasm local 1,
//!   which waffle never reuses for another value). Arguments and `this`
//!   are `sp`-relative. Locals are `vp`-relative, where `vp` is `sp`
//!   unless the script reads actuals past its formals; then it is
//!   recomputed from `argc` (local 2) exactly as the prologue does.
//! - **Bindings.** Each scope's bindings get the locations SpiderMonkey's
//!   `BindingIter` assigns (argument, frame or environment slot), replayed
//!   from the scope data in the snapshot. Block scopes become lexical
//!   blocks over the code their scope notes cover. A closed-over binding
//!   lives in an environment object, found from the frame's environment
//!   slot through as many `enclosing` hops as the static scope chain at
//!   each pc requires, so it gets a location list.
//! - **Globals.** Top-level `var`s and functions are global-object
//!   properties, and top-level lexicals live in the global lexical
//!   environment; their slots are resolved in the snapshot image (heap
//!   addresses are stable: compacting GC is off) and described as memory
//!   locations.
//! - **Values.** Every binding has type `JS::Value`. The engine's heap
//!   layout (value tags, object/shape/property-map/string layouts and
//!   their flag bits) is described as DWARF structure and enumeration
//!   types under the `js::` and `JS::` namespaces, so a debugger can
//!   pretty-print JS values without baking in the engine's layout.
//!
//! The location space of `FunctionBody::source_locs` in a `--debug-info`
//! build is the script's bytecode pcs, not the module's interned
//! locations.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use gimli::write::{
    Address, AttributeValue, DwarfUnit, EndianVec, Expression, LineProgram, LineString, Location,
    LocationList, Range, RangeList, Sections, UnitEntryId,
};
use gimli::{Encoding, Format, LineEncoding, LittleEndian};
use waffle::entity::EntityRef;
use waffle::{CodeLayout, Func};

use super::baseline::layout::{FrameLayout, ARGC_FLAGS};
use crate::bytecode::Script;
use crate::ids::Pc;
use crate::source::{ScopeData, Source, SourceObject, SourceObjectId};

pub mod heap;

/// The source location of baseline code that runs ahead of the first op
/// (frame setup): not a pc.
pub const PROLOGUE_LOC: u32 = u32::MAX - 1;

/// `DW_AT_language` for JavaScript compiled by NightMonkey. DWARF has no
/// code for JavaScript; this is in the vendor range.
pub const DW_LANG_NIGHTMONKEY_JS: u16 = 0xa53a;

/// The Wasm locals of a body's parameters (the `night_abi_sig2` ABI:
/// `(cx, sp, argc, retval_out, script, new_target)`).
const LOCAL_SP: u32 = 1;
const LOCAL_ARGC: u32 = 2;

/// What a `--debug-info` build describes.
pub struct DebugInput<'a> {
    pub source: &'a Source,
    /// The program's top-level script: the scripts reachable from it are
    /// the program's own (self-hosted code gets no debug info).
    pub root: SourceObjectId,
    /// The program's source file, as a debugger should open it.
    pub path: &'a str,
    /// The body each compiled script's code lives in, by script id
    /// (`TranslateOut::source_id_to_func`).
    pub bodies: &'a dyn Fn(u32) -> Option<Func>,
    /// Where the output module's functions landed (waffle).
    pub layout: &'a CodeLayout,
    /// The snapshot image, for resolving global bindings.
    pub image: &'a dyn heap::Image,
    /// The image address of a source object (an `Object`'s, by id).
    pub object_addr: &'a dyn Fn(u32) -> Option<u32>,
    /// The global object's address in the image.
    pub global_object: Option<u32>,
}

/// Build the DWARF sections (name, contents) for the output module.
pub fn build(input: &DebugInput) -> Result<Vec<(String, Vec<u8>)>, String> {
    let encoding = Encoding {
        format: Format::Dwarf32,
        version: 4,
        address_size: 4,
    };
    let (dir, file) = match input.path.rfind('/') {
        Some(i) => (&input.path[..i.max(1)], &input.path[i + 1..]),
        None => (".", input.path),
    };
    let line_program = LineProgram::new(
        encoding,
        LineEncoding::default(),
        LineString::String(dir.as_bytes().to_vec()),
        None,
        LineString::String(file.as_bytes().to_vec()),
        None,
    );
    let mut dwarf = DwarfUnit::new(encoding);
    dwarf.unit.line_program = line_program;
    let dir_id = dwarf.unit.line_program.default_directory();
    let file_id = dwarf.unit.line_program.add_file(
        LineString::String(file.as_bytes().to_vec()),
        dir_id,
        None,
    );

    let root = dwarf.unit.root();
    {
        let cu = dwarf.unit.get_mut(root);
        cu.set(
            gimli::DW_AT_producer,
            AttributeValue::String(b"NightMonkey (baseline, --debug-info)".to_vec()),
        );
        cu.set(
            gimli::DW_AT_language,
            AttributeValue::Language(gimli::DwLang(DW_LANG_NIGHTMONKEY_JS)),
        );
        cu.set(
            gimli::DW_AT_name,
            AttributeValue::String(input.path.as_bytes().to_vec()),
        );
        cu.set(
            gimli::DW_AT_comp_dir,
            AttributeValue::String(dir.as_bytes().to_vec()),
        );
        cu.set(gimli::DW_AT_low_pc, AttributeValue::Address(Address::Constant(0)));
    }

    let types = heap::emit_types(&mut dwarf);
    let mut cx = Cx {
        input,
        dwarf: &mut dwarf,
        types,
        file_id,
        has_var_scope: BTreeSet::new(),
    };
    for o in &input.source.objects {
        if let SourceObject::Scope(ScopeData {
            kind: SK_FUNCTION_BODY_VAR,
            enclosing: Some(e),
            ..
        }) = o
        {
            cx.has_var_scope.insert(e.id());
        }
    }

    let names = function_names(input.source);
    let funcs: HashMap<Func, usize> = input
        .layout
        .funcs
        .iter()
        .enumerate()
        .map(|(i, (f, _))| (*f, i))
        .collect();
    let mut cu_ranges = vec![];
    for sid in user_scripts(input.source, input.root) {
        let Some(func) = (input.bodies)(sid) else {
            continue;
        };
        let Some(&li) = funcs.get(&func) else {
            continue;
        };
        let fl = &input.layout.funcs[li].1;
        let SourceObject::Script(script) = input.source.object(SourceObjectId::new(sid)) else {
            continue;
        };
        let is_toplevel = sid == input.root.id();
        let name = if is_toplevel {
            "<toplevel>".to_string()
        } else {
            names
                .get(&sid)
                .cloned()
                .unwrap_or_else(|| "<anonymous>".to_string())
        };
        cx.function(script, is_toplevel, &name, fl)?;
        cu_ranges.push(Range::StartEnd {
            begin: Address::Constant(u64::from(fl.start)),
            end: Address::Constant(u64::from(fl.end)),
        });
    }
    let ranges = cx.dwarf.unit.ranges.add(RangeList(cu_ranges));
    cx.dwarf
        .unit
        .get_mut(root)
        .set(gimli::DW_AT_ranges, AttributeValue::RangeListRef(ranges));
    cx.globals()?;

    let mut sections = Sections::new(EndianVec::new(LittleEndian));
    dwarf.write(&mut sections).map_err(|e| format!("DWARF: {e}"))?;
    let mut out = vec![];
    sections
        .for_each(|id, data| -> Result<(), String> {
            if !data.slice().is_empty() {
                out.push((id.name().to_string(), data.slice().to_vec()));
            }
            Ok(())
        })
        .map_err(|e| format!("DWARF: {e}"))?;
    Ok(out)
}

// js::ScopeKind (vm/ScopeKind.h).
const SK_FUNCTION: u8 = 0;
const SK_FUNCTION_BODY_VAR: u8 = 1;
const SK_LEXICAL: u8 = 2;
const SK_SIMPLE_CATCH: u8 = 3;
const SK_CATCH: u8 = 4;
const SK_FUNCTION_LEXICAL: u8 = 7;
const SK_CLASS_BODY: u8 = 8;
const SK_WITH: u8 = 9;
const SK_GLOBAL: u8 = 12;
const SK_NON_SYNTACTIC: u8 = 13;
const SK_MODULE: u8 = 14;

/// Where `BindingIter` puts a binding (`BindingLocation`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BindingLoc {
    /// Actual argument `i`.
    Argument(u32),
    /// Frame slot (local) `i`.
    Frame(u32),
    /// Slot `i` of the scope's environment object.
    Environment(u32),
    /// Somewhere else (global, import, named-lambda callee).
    Other,
}

struct Cx<'a, 'b> {
    input: &'a DebugInput<'a>,
    dwarf: &'b mut DwarfUnit,
    types: heap::Types,
    file_id: gimli::write::FileId,
    /// Function scopes with a separate var scope: the function has
    /// parameter expressions, so its positional formals also get frame
    /// slots.
    has_var_scope: BTreeSet<u32>,
}

impl Cx<'_, '_> {
    fn source(&self) -> &Source {
        self.input.source
    }

    fn scope(&self, id: SourceObjectId) -> Option<&ScopeData> {
        match self.source().object(id) {
            SourceObject::Scope(s) => Some(s),
            _ => None,
        }
    }

    fn string(&self, id: SourceObjectId) -> Option<String> {
        match self.source().object(id) {
            SourceObject::String(s) => Some(String::from_utf16_lossy(s.chars())),
            _ => None,
        }
    }

    /// Each binding of scope `id` with its location (`BindingIter`).
    fn bindings(&self, id: SourceObjectId) -> Vec<(Option<SourceObjectId>, bool, BindingLoc)> {
        let Some(scope) = self.scope(id) else {
            return vec![];
        };
        let mut frame = self.first_frame_slot(id);
        let mut out = vec![];
        let nargs = self.function_nargs(id);
        let param_exprs = self.has_var_scope.contains(&id.id());
        for (i, &(name, is_var, env)) in scope.all_bindings.iter().enumerate() {
            let i = u32::try_from(i).unwrap();
            let loc = match (scope.kind, env) {
                (_, Some(slot)) => BindingLoc::Environment(slot),
                (SK_FUNCTION, None) if i < nargs => {
                    if param_exprs && name.is_some() {
                        frame += 1;
                    }
                    BindingLoc::Argument(i)
                }
                (
                    SK_FUNCTION | SK_FUNCTION_BODY_VAR | SK_LEXICAL | SK_SIMPLE_CATCH | SK_CATCH
                    | SK_FUNCTION_LEXICAL | SK_CLASS_BODY | SK_MODULE,
                    None,
                ) => {
                    frame += 1;
                    BindingLoc::Frame(frame - 1)
                }
                _ => BindingLoc::Other,
            };
            out.push((name, is_var, loc));
        }
        out
    }

    /// The positional-formal count of a function scope (the function's
    /// script's `nargs`), else 0.
    fn function_nargs(&self, scope: SourceObjectId) -> u32 {
        if self.scope(scope).map(|s| s.kind) != Some(SK_FUNCTION) {
            return 0;
        }
        self.source()
            .objects
            .iter()
            .find_map(|o| match o {
                SourceObject::Script(s) if s.body_scope == Some(scope) => Some(u32::from(s.nargs)),
                _ => None,
            })
            .unwrap_or(0)
    }

    /// `LexicalScope::firstFrameSlot` and friends: intra-frame scopes
    /// continue the frame slots of the scope around them.
    fn first_frame_slot(&self, id: SourceObjectId) -> u32 {
        let Some(scope) = self.scope(id) else {
            return 0;
        };
        match scope.kind {
            SK_FUNCTION_BODY_VAR | SK_LEXICAL | SK_SIMPLE_CATCH | SK_CATCH | SK_FUNCTION_LEXICAL
            | SK_CLASS_BODY => scope.enclosing.map_or(0, |e| self.next_frame_slot(e)),
            _ => 0,
        }
    }

    /// The frame slot after scope `id`'s own (`nextFrameSlot`).
    fn next_frame_slot(&self, id: SourceObjectId) -> u32 {
        let Some(scope) = self.scope(id) else {
            return 0;
        };
        match scope.kind {
            SK_WITH => scope.enclosing.map_or(0, |e| self.next_frame_slot(e)),
            SK_FUNCTION | SK_FUNCTION_BODY_VAR | SK_LEXICAL | SK_SIMPLE_CATCH | SK_CATCH
            | SK_FUNCTION_LEXICAL | SK_CLASS_BODY | SK_MODULE => {
                let frames = self
                    .bindings(id)
                    .iter()
                    .filter_map(|&(_, _, l)| match l {
                        BindingLoc::Frame(s) => Some(s + 1),
                        _ => None,
                    })
                    .max();
                // With parameter expressions, positional formals take frame
                // slots ahead of any Frame binding.
                let first = self.first_frame_slot(id);
                let formals = if self.has_var_scope.contains(&id.id()) {
                    u32::try_from(
                        scope.all_bindings[..self.function_nargs(id) as usize]
                            .iter()
                            .filter(|(n, _, e)| n.is_some() && e.is_none())
                            .count(),
                    )
                    .unwrap()
                } else {
                    0
                };
                frames.unwrap_or(first + formals).max(first + formals)
            }
            _ => 0,
        }
    }

    /// The static scope at `pc`: the innermost scope note covering it,
    /// else the body scope.
    fn scope_at(&self, script: &Script, pc: Pc) -> Option<SourceObjectId> {
        let mut best: Option<(u32, SourceObjectId)> = None;
        for n in &script.scope_notes {
            if n.gcthing_index == u32::MAX || pc < n.start || pc >= n.start + n.length {
                continue;
            }
            let Some(&gc) = script.gcthings.get(n.gcthing_index as usize) else {
                continue;
            };
            if gc.is_other() || self.scope(gc).is_none() {
                continue;
            }
            if best.is_none_or(|(len, _)| n.length < len) {
                best = Some((n.length, gc));
            }
        }
        best.map(|(_, s)| s).or(script.body_scope)
    }

    /// Environment hops from the innermost environment at `pc` to scope
    /// `target`'s environment, if `target` is on the static chain there.
    fn env_hops(&self, script: &Script, pc: Pc, target: SourceObjectId) -> Option<u32> {
        let mut cur = self.scope_at(script, pc)?;
        let mut hops = 0;
        loop {
            if cur == target {
                return Some(hops);
            }
            let s = self.scope(cur)?;
            if s.has_environment {
                hops += 1;
            }
            cur = s.enclosing?;
        }
    }

    /// Emit one script's subprogram, line rows and variables.
    fn function(
        &mut self,
        script: &Script,
        is_toplevel: bool,
        name: &str,
        fl: &waffle::FuncCodeLayout,
    ) -> Result<(), String> {
        let pos = script.pos.clone().unwrap_or_default();
        // Map each tagged instruction to its pc (or the prologue).
        let rows: Vec<(u32, u32)> = fl.locs.iter().map(|&(off, loc)| (off, loc.index() as u32)).collect();
        self.lines(script, &pos, fl, &rows);

        let root = self.dwarf.unit.root();
        let sub = self.dwarf.unit.add(root, gimli::DW_TAG_subprogram);
        let frame_layout = FrameLayout::of(script);
        {
            let e = self.dwarf.unit.get_mut(sub);
            e.set(gimli::DW_AT_name, AttributeValue::String(name.as_bytes().to_vec()));
            e.set(
                gimli::DW_AT_low_pc,
                AttributeValue::Address(Address::Constant(u64::from(fl.start))),
            );
            e.set(gimli::DW_AT_high_pc, AttributeValue::Udata(u64::from(fl.end - fl.start)));
            e.set(gimli::DW_AT_decl_file, AttributeValue::FileIndex(Some(self.file_id)));
            e.set(gimli::DW_AT_decl_line, AttributeValue::Udata(u64::from(pos.line)));
            e.set(gimli::DW_AT_external, AttributeValue::Flag(true));
            let mut fb = Expression::new();
            fb.op_wasm_local(LOCAL_SP);
            e.set(gimli::DW_AT_frame_base, AttributeValue::Exprloc(fb));
            if name == "main" {
                e.set(gimli::DW_AT_main_subprogram, AttributeValue::Flag(true));
            }
        }
        if is_toplevel {
            // Top-level bindings are globals (`globals`).
            return Ok(());
        }
        let this = self.var(sub, gimli::DW_TAG_formal_parameter, "this");
        let mut loc = Expression::new();
        loc.op_fbreg(i64::from(FrameLayout::THIS));
        self.set_loc(this, loc);

        // Code ranges per bytecode-pc predicate.
        let ranges = |pred: &dyn Fn(Pc) -> bool| -> Vec<(u32, u32)> {
            let mut out: Vec<(u32, u32)> = vec![];
            for (i, &(off, pc)) in rows.iter().enumerate() {
                let end = rows.get(i + 1).map_or(fl.end, |&(o, _)| o);
                if pc == PROLOGUE_LOC || !pred(Pc::new(pc)) {
                    continue;
                }
                match out.last_mut() {
                    Some(last) if last.1 == off => last.1 = end,
                    _ => out.push((off, end)),
                }
            }
            out
        };

        // The body scope's bindings, at function level.
        if let Some(body) = script.body_scope {
            self.scope_vars(script, &frame_layout, sub, body, &ranges, &BTreeSet::new())?;
            // Then the bindings this function closes over: those of the
            // enclosing functions' environments, up to the global scope,
            // except where a nearer binding shadows them.
            let mut shadowed: BTreeSet<String> = BTreeSet::new();
            let mut own = vec![body];
            own.extend(script.scope_notes.iter().filter_map(|n| {
                script.gcthings.get(n.gcthing_index as usize).copied()
            }));
            for s in own {
                for (name, _, _) in self.bindings(s) {
                    shadowed.extend(name.and_then(|n| self.string(n)));
                }
            }
            let mut cur = self.scope(body).and_then(|s| s.enclosing);
            while let Some(scope) = cur {
                let Some(data) = self.scope(scope) else { break };
                if matches!(data.kind, SK_GLOBAL | SK_NON_SYNTACTIC) {
                    break;
                }
                let (has_environment, enclosing) = (data.has_environment, data.enclosing);
                if has_environment {
                    self.scope_vars(script, &frame_layout, sub, scope, &ranges, &shadowed)?;
                }
                for (name, _, _) in self.bindings(scope) {
                    shadowed.extend(name.and_then(|n| self.string(n)));
                }
                cur = enclosing;
            }
        }
        // Block scopes, as lexical blocks over the code of their notes.
        let mut blocks: BTreeMap<u32, Vec<(Pc, u32)>> = BTreeMap::new();
        for n in &script.scope_notes {
            if n.gcthing_index == u32::MAX {
                continue;
            }
            let Some(&gc) = script.gcthings.get(n.gcthing_index as usize) else {
                continue;
            };
            if gc.is_other() || self.scope(gc).is_none() || Some(gc) == script.body_scope {
                continue;
            }
            blocks.entry(gc.id()).or_default().push((n.start, n.length));
        }
        for (scope, notes) in blocks {
            let rs = ranges(&|pc| notes.iter().any(|&(s, l)| pc >= s && pc < s + l));
            if rs.is_empty() {
                continue;
            }
            let block = self.dwarf.unit.add(sub, gimli::DW_TAG_lexical_block);
            let list = self.dwarf.unit.ranges.add(RangeList(
                rs.iter()
                    .map(|&(b, e)| Range::StartEnd {
                        begin: Address::Constant(u64::from(b)),
                        end: Address::Constant(u64::from(e)),
                    })
                    .collect(),
            ));
            self.dwarf
                .unit
                .get_mut(block)
                .set(gimli::DW_AT_ranges, AttributeValue::RangeListRef(list));
            self.scope_vars(
                script,
                &frame_layout,
                block,
                SourceObjectId::new(scope),
                &ranges,
                &BTreeSet::new(),
            )?;
        }
        Ok(())
    }

    /// Line rows for one function: a row wherever the source position
    /// changes, `is_stmt` where the line does.
    fn lines(&mut self, script: &Script, pos: &crate::bytecode::ScriptPos, fl: &waffle::FuncCodeLayout, rows: &[(u32, u32)]) {
        let position = |pc: u32| -> (u32, u32) {
            if pc == PROLOGUE_LOC {
                return (pos.line, pos.column);
            }
            let i = pos.lines.partition_point(|&(p, _, _)| p.get() <= pc);
            match i.checked_sub(1) {
                Some(i) => (pos.lines[i].1, pos.lines[i].2),
                None => (pos.line, pos.column),
            }
        };
        let _ = script;
        let lp = &mut self.dwarf.unit.line_program;
        lp.begin_sequence(Some(Address::Constant(u64::from(fl.start))));
        let mut last: Option<(u32, u32)> = None;
        let mut last_line = None;
        let mut seen_body = false;
        for &(off, pc) in rows {
            let (line, col) = position(pc);
            let prologue_end = pc != PROLOGUE_LOC && !seen_body;
            if last == Some((line, col)) && !prologue_end {
                continue;
            }
            seen_body |= pc != PROLOGUE_LOC;
            let row = lp.row();
            row.address_offset = u64::from(off - fl.start);
            row.file = self.file_id;
            row.line = u64::from(line);
            row.column = u64::from(col);
            row.is_statement = last_line != Some(line) || prologue_end;
            row.prologue_end = prologue_end;
            lp.generate_row();
            last = Some((line, col));
            last_line = Some(line);
        }
        lp.end_sequence(u64::from(fl.end - fl.start));
    }

    /// A variable DIE of type `JS::Value` under `parent`.
    fn var(&mut self, parent: UnitEntryId, tag: gimli::DwTag, name: &str) -> UnitEntryId {
        let v = self.dwarf.unit.add(parent, tag);
        let e = self.dwarf.unit.get_mut(v);
        e.set(gimli::DW_AT_name, AttributeValue::String(name.as_bytes().to_vec()));
        e.set(gimli::DW_AT_type, AttributeValue::UnitRef(self.types.value));
        e.set(gimli::DW_AT_decl_file, AttributeValue::FileIndex(Some(self.file_id)));
        v
    }

    fn set_loc(&mut self, v: UnitEntryId, loc: Expression) {
        self.dwarf
            .unit
            .get_mut(v)
            .set(gimli::DW_AT_location, AttributeValue::Exprloc(loc));
    }

    /// Push `vp + off`.
    fn vp_rel(&self, e: &mut Expression, layout: &FrameLayout, off: u32) {
        if !layout.rebase_vp {
            e.op_fbreg(i64::from(off));
            return;
        }
        // vp = sp + 8 * max(0, (argc & !ARGC_FLAGS) - nargs)
        e.op_wasm_local(LOCAL_ARGC);
        e.op_constu(u64::from(!ARGC_FLAGS));
        e.op(gimli::DW_OP_and);
        e.op_constu(u64::from(layout.nargs));
        e.op(gimli::DW_OP_minus);
        e.op(gimli::DW_OP_dup);
        e.op_constu(0);
        e.op(gimli::DW_OP_ge);
        e.op(gimli::DW_OP_mul);
        e.op_constu(8);
        e.op(gimli::DW_OP_mul);
        e.op_fbreg(i64::from(off));
        e.op(gimli::DW_OP_plus);
    }

    /// Variables for scope `scope`'s bindings under DIE `parent`.
    fn scope_vars(
        &mut self,
        script: &Script,
        layout: &FrameLayout,
        parent: UnitEntryId,
        scope: SourceObjectId,
        ranges: &dyn Fn(&dyn Fn(Pc) -> bool) -> Vec<(u32, u32)>,
        shadowed: &BTreeSet<String>,
    ) -> Result<(), String> {
        // A scope of an enclosing function: only its environment's
        // bindings are reachable from here.
        let own = script.body_scope == Some(scope)
            || script.scope_notes.iter().any(|n| {
                script.gcthings.get(n.gcthing_index as usize) == Some(&scope)
            });
        let env_nfixed = self.scope(scope).and_then(|s| s.env_nfixed);
        let is_function = self.scope(scope).map(|s| s.kind) == Some(SK_FUNCTION);
        let nargs = self.function_nargs(scope);
        for (i, (name, _is_var, loc)) in self.bindings(scope).into_iter().enumerate() {
            let formal = own && is_function && (i as u32) < nargs;
            let Some(name) = name.and_then(|n| self.string(n)) else {
                continue;
            };
            // Synthetic bindings (`.this`, `.generator`, `*namespace*`...).
            if name.starts_with('.') || name.starts_with('*') || shadowed.contains(&name) {
                continue;
            }
            if !own && !matches!(loc, BindingLoc::Environment(_)) {
                continue;
            }
            match loc {
                BindingLoc::Argument(i) => {
                    let v = self.var(parent, gimli::DW_TAG_formal_parameter, &name);
                    let mut e = Expression::new();
                    e.op_fbreg(i64::from(layout.arg(i)));
                    self.set_loc(v, e);
                }
                BindingLoc::Frame(slot) if slot < layout.nlocals => {
                    let v = self.var(parent, gimli::DW_TAG_variable, &name);
                    let mut e = Expression::new();
                    self.vp_rel(&mut e, layout, layout.local(slot));
                    self.set_loc(v, e);
                }
                BindingLoc::Environment(slot) => {
                    let Some(nfixed) = env_nfixed else { continue };
                    if !layout.has_env {
                        continue;
                    }
                    // Group the code by environment hops.
                    let mut by_hops: BTreeMap<u32, Vec<(u32, u32)>> = BTreeMap::new();
                    for h in 0..8 {
                        let rs = ranges(&|pc| self.env_hops(script, pc, scope) == Some(h));
                        if !rs.is_empty() {
                            by_hops.insert(h, rs);
                        }
                    }
                    if by_hops.is_empty() {
                        continue;
                    }
                    let tag = if formal {
                        gimli::DW_TAG_formal_parameter
                    } else {
                        gimli::DW_TAG_variable
                    };
                    let v = self.var(parent, tag, &name);
                    let mut list = vec![];
                    for (hops, rs) in by_hops {
                        let mut e = Expression::new();
                        self.vp_rel(&mut e, layout, layout.env());
                        // The env Value's payload: the object pointer.
                        e.op_deref_size(4);
                        for _ in 0..hops {
                            heap::env_enclosing(&mut e);
                        }
                        heap::object_slot(&mut e, slot, nfixed);
                        for (b, end) in rs {
                            list.push(Location::StartEnd {
                                begin: Address::Constant(u64::from(b)),
                                end: Address::Constant(u64::from(end)),
                                data: e.clone(),
                            });
                        }
                    }
                    let list = self.dwarf.unit.locations.add(LocationList(list));
                    self.dwarf
                        .unit
                        .get_mut(v)
                        .set(gimli::DW_AT_location, AttributeValue::LocationListRef(list));
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// CU-level variables for the top-level script's bindings, resolved
    /// in the snapshot image.
    fn globals(&mut self) -> Result<(), String> {
        let SourceObject::Script(root) = self.source().object(self.input.root) else {
            return Ok(());
        };
        let Some(body) = root.body_scope else {
            return Ok(());
        };
        let Some(global) = self.input.global_object else {
            return Ok(());
        };
        let image = self.input.image;
        let lexical = heap::global_lexical_env(image, self.source(), self.input.object_addr);
        let names: Vec<(String, bool)> = self
            .scope(body)
            .map(|s| {
                s.bindings
                    .iter()
                    .filter_map(|&(n, is_var, _)| Some((self.string(n)?, is_var)))
                    .collect()
            })
            .unwrap_or_default();
        let cu = self.dwarf.unit.root();
        for (name, is_var) in names {
            // `var`s and functions are global-object properties, lexicals
            // live in the global lexical environment.
            let holder = if is_var { Some(global) } else { lexical };
            let Some(holder) = holder else { continue };
            let Some(loc) = heap::own_property_slot(image, holder, &name) else {
                continue;
            };
            let v = self.var(cu, gimli::DW_TAG_variable, &name);
            let mut e = Expression::new();
            e.op_addr(Address::Constant(u64::from(holder)));
            heap::object_slot(&mut e, loc.slot, loc.nfixed);
            self.dwarf.unit.get_mut(v).set(gimli::DW_AT_external, AttributeValue::Flag(true));
            self.set_loc(v, e);
        }
        Ok(())
    }
}

/// The scripts of the program itself: the top-level script and every
/// script reachable through its gcthings (nested functions), excluding
/// self-hosted code.
fn user_scripts(source: &Source, root: SourceObjectId) -> BTreeSet<u32> {
    let mut seen = BTreeSet::new();
    let mut work = vec![root];
    while let Some(id) = work.pop() {
        if !seen.insert(id.id()) {
            continue;
        }
        let SourceObject::Script(s) = source.object(id) else {
            continue;
        };
        for &gc in &s.gcthings {
            if gc.is_other() {
                continue;
            }
            match source.object(gc) {
                SourceObject::Script(_) => work.push(gc),
                SourceObject::Object(od) => {
                    if let Some(sc) = od.script {
                        work.push(sc);
                    }
                }
                _ => {}
            }
        }
    }
    seen
}

/// Each script's function name (from its function object's atom).
fn function_names(source: &Source) -> HashMap<u32, String> {
    let mut names = HashMap::new();
    for o in &source.objects {
        let SourceObject::Object(od) = o else { continue };
        let (Some(s), Some(n)) = (od.script, od.name) else {
            continue;
        };
        if let SourceObject::String(n) = source.object(n) {
            names.entry(s.id()).or_insert_with(|| String::from_utf16_lossy(n.chars()));
        }
    }
    names
}
