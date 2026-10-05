//! The MIR tier's driver under `pipeline=mir` (`docs/MIR.md` §9): build a
//! MIR body for the script, compile its baseline body with the MIR body's
//! exit and throw pcs as resume targets, and lower the MIR into the
//! script's table entry, with the baseline body beside it.

pub(crate) mod abi;
pub mod build;
pub mod helpers;
pub(crate) mod inline;
pub mod lower;
pub(crate) mod stamp;

use crate::bytecode::Script;
use crate::ids::ScriptId;
use crate::wasm::baseline;
use crate::wasm::baseline::layout;
use crate::wasm::translate::{AtomTable, ExtraBody, Outcome, TranslateCtx};
use waffle::Module;

/// Whether MIR inlines calls (§5.5; in progress).
const INLINING: bool = true;

/// The most bytecode a script may have to be inlined (§5.5).
pub(crate) const INLINE_MAX_BYTECODE: usize = 500;

/// The most MIR instructions a function may have, inlined callees and
/// all.
const MAX_MIR_INSTS: usize = 60_000;

/// Whether `script` may be inlined into a MIR caller (§5.5): small, and
/// without the constructs an inline frame does not model. A property of
/// the script alone, so a compile of it knows, with no word from its
/// callers, that its baseline body must resume at any op.
pub(crate) fn inline_eligible(ctx: &TranslateCtx, script: &Script) -> bool {
    use crate::bytecode::TryNoteKind;
    INLINING
        && ctx.opts.pipeline == crate::options::Pipeline::Mir
        && script.addr != 0
        && script.bytecode.len() <= INLINE_MAX_BYTECODE
        && !script.is_generator_or_async
        && !script.is_class_ctor
        // Mapped formals (write-through, aliasing): none with no formals.
        && !(script.has_mapped_args && script.nargs > 0)
        // No handler or close: `inline::splice` sends every throw straight
        // to the call site.
        && script.try_notes.iter().all(|t| t.kind == TryNoteKind::Loop)
        // A callee reading its actuals gets them all in its inline frame
        // (`InlineFrame::argc`), which its actuals ops read.
        && !(script.parser().opcodes().any(|op| op == crate::bytecode::JSOp::ArgumentsLength)
            && !baseline::layout::reads_actuals(script))
        && (!baseline::needs_env(script) || baseline::env_is_plain(ctx.source, script))
}

/// `--viz`: each MIR-compiled script's MIR text (each instruction marked
/// `;;@i<index> pc=<pc> s=<script>`) and its lowered body's text (each value
/// marked `;;@i<index>` with the instruction that emitted it), by script id,
/// for the translation loop's records.
pub static VIZ_TEXTS: std::sync::Mutex<std::collections::BTreeMap<u32, (String, String)>> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

/// A script's MIR, built, optimized and verified: the front half of
/// [`translate_script`]. `diag` holds the diagnostic lines it produced, for
/// the serial back half to print in script order.
pub struct Prebuilt {
    built: Result<(crate::mir::Module, crate::mir::Func), String>,
    diag: Vec<String>,
}

/// Build, optimize and verify `script`'s MIR. Reads only the analysis: the
/// context and the analysis-time `names` (`build` never sees what codegen
/// interns), so scripts run it in parallel and in any order.
pub fn prebuild(
    ctx: &TranslateCtx,
    names: &crate::ids::Names,
    sid: ScriptId,
    script: &Script,
    is_global: bool,
) -> Prebuilt {
    let mut diag = vec![];
    let built = (|| {
        let (mm, mut f) = build::build(ctx, names, sid, script, is_global)?;
        // Past a size, the body (at tens of bytes of wasm per instruction)
        // would approach wasm's function size limit: baseline alone.
        if f.insts.len() > MAX_MIR_INSTS {
            return Err("too large for MIR after inlining".to_string());
        }
        // Guard folding (§10.1). The builder guards locally at every use;
        // this merges them, and the validator checks the result.
        let folded = crate::mir::opt::optimize(&mm, &mut f);
        if ctx.opts.diagnostics.stats && folded > 0 {
            diag.push(format!("night: mir sid#{sid} folded {folded} guards"));
        }
        if let Err(es) = crate::mir::verify(&mm, &f) {
            let first = es.first().map(|e| e.to_string()).unwrap_or_default();
            if ctx.opts.diagnostics.mir {
                diag.push(format!(
                    "night: invalid MIR for sid#{sid}:\n{}",
                    crate::mir::print::print_func(&mm, &f)
                ));
            }
            return Err(format!(
                "BUG: invalid MIR ({} errors; {first})",
                es.len()
            ));
        }
        Ok((mm, f))
    })();
    Prebuilt { built, diag }
}

/// Compile `script` as a MIR body plus its baseline body, from its
/// [`prebuild`]. `Ok(Err(reason))` is a decline: the caller falls back to
/// baseline alone.
pub fn translate_script(
    ctx: &TranslateCtx,
    m: &mut Module,
    atoms: &mut AtomTable,
    sid: ScriptId,
    script: &Script,
    is_global: bool,
    pre: Prebuilt,
) -> Result<Result<Outcome, String>, String> {
    for line in &pre.diag {
        crate::diag_line!("{line}");
    }
    let (mm, f) = match pre.built {
        Ok(x) => x,
        Err(reason) => return Ok(Err(reason)),
    };
    if ctx.opts.diagnostics.mir {
        crate::diag_line!("{}", crate::mir::print::print_func(&mm, &f));
    }
    let resumes = lower::resume_words(&f);
    let onramps: Vec<(crate::ids::Pc, Vec<layout::ResumeWord>)> = f
        .roots
        .iter()
        .filter_map(|r| match r.kind {
            crate::mir::func::RootKind::Onramp(pc) => {
                Some((pc, lower::resume_words_from(&f, r.block)))
            }
            _ => None,
        })
        .collect();
    let base =
        match baseline::build_body(ctx, m, atoms, sid, script, is_global, &resumes, &onramps)? {
            Ok(b) => b,
            Err(reason) => return Ok(Err(format!("baseline declined: {reason}"))),
        };
    let gname_bids = mm
        .atoms
        .iter()
        .filter_map(|(a, s)| {
            let n = atoms.names.lookup(s.chars())?;
            Some((a, *ctx.syn_gnames.get(&n)?))
        })
        .collect();
    let add_preds = mm
        .atoms
        .iter()
        .filter_map(|(a, s)| {
            let n = atoms.names.lookup(s.chars())?;
            let pairs = ctx.layout_addpred_in.get(&n)?;
            // Capped: an over-full list only costs the helper.
            (pairs.len() <= 16).then(|| (a, pairs.iter().map(|p| (p.key.get(), p.offset)).collect()))
        })
        .collect();
    let gname_fused = mm
        .atoms
        .iter()
        .filter_map(|(a, s)| {
            let n = atoms.names.lookup(s.chars())?;
            Some((a, *ctx.fused_gnames.get(&n)?))
        })
        .collect();
    let mut lowered = match lower::lower(
        m,
        ctx.helpers,
        &mm,
        atoms,
        &f,
        baseline::layout::FrameLayout::of(script),
        lower::LowerOpts {
            stress: ctx.opts.mir_stress,
            exit_census: ctx.opts.instrument.mir_exits,
            block_census: ctx.opts.instrument.blocks,
            root_census: ctx.opts.instrument.roots,
            value_census: ctx.opts.instrument.values,
            viz: ctx.opts.diagnostics.viz.is_some(),
            strict: script.strict,
            plain_env: baseline::needs_env(script) && baseline::env_is_plain(ctx.source, script),
            own_env: baseline::needs_env(script) && !baseline::env_is_plain(ctx.source, script),
            forward_resume: inline_eligible(ctx, script),
            is_gen: script.is_generator_or_async,
            mapped_formals: script.has_mapped_args && script.nargs > 0,
            inline_layouts: f
                .inline_frames
                .iter()
                .map(|fr| match ctx.source.object(crate::source::SourceObjectId::new(fr.script.get())) {
                    crate::source::SourceObject::Script(ks) => baseline::layout::FrameLayout::of(ks),
                    _ => unreachable!("an inline frame's callee is a script"),
                })
                .collect(),
        },
        gname_bids,
        gname_fused,
        add_preds,
    ) {
        Ok(l) => l,
        Err(reason) => return Ok(Err(reason)),
    };
    // A lowering bug (a value used where its definition does not
    // dominate) shows here, not at module serialization.
    if ctx.opts.strict_coverage || ctx.opts.mir_stress > 0 {
        if let Err(e) = lowered.body.validate() {
            return Err(format!("mir: sid#{sid}: lowered body is not valid SSA: {e}"));
        }
    }
    let params: usize = lowered.body.blocks.values().map(|b| b.params.len()).sum();
    let edge_args: usize = lowered
        .body
        .blocks
        .values()
        .map(|b| {
            let mut n = 0;
            b.terminator.visit_targets(|t| n += t.args.len());
            n
        })
        .sum();
    if ctx.opts.diagnostics.stats {
        crate::diag_line!(
            "night: mir body sid#{sid} blocks {} values {} bytecode {} params {params} edge_args {edge_args} roots {} inlined {}",
            lowered.body.blocks.len(),
            lowered.body.values.len(),
            script.bytecode.len(),
            f.roots.len(),
            f.inline_frames.len()
        );
    }
    if ctx.opts.diagnostics.opsize {
        for (op, (n, vals)) in &lowered.opsize {
            crate::diag_line!("night: mir opsize sid#{sid} {op} n {n} values {vals}");
        }
    }
    if let Some(waffle_text) = lowered.viz_text.take() {
        // Each instruction marked with its index, and the bytecode op it
        // was built for (pc -1: none) in its frame's script.
        let mir_text = crate::mir::print::print_func_with(&mm, &f, &|i| {
            let fr = f.inst_frame[i] as usize;
            let s = if fr == 0 { f.script } else { f.inline_frames[fr - 1].script };
            let pc = i64::from(f.inst_pc[i]) - 1;
            format!(" ;;@i{} pc={pc} s={s}", crate::mir::entity::EntityRef::index(i))
        });
        VIZ_TEXTS.lock().unwrap().insert(sid.get(), (mir_text, waffle_text));
    }
    Ok(Ok(Outcome::Compiled {
        sig: ctx.helpers.night_abi_sig2,
        body: lowered.body,
        likely_patches: lowered.likely_patches,
        call_cell_patches: lowered.call_cell_patches,
        alloc_cell_patches: lowered.alloc_cell_patches,
        iof_cell_patches: lowered.iof_cell_patches,
        construct_cell_patches: lowered.construct_cell_patches,
        strlit_patches: vec![],
        intrinsic_cell_patches: lowered.intrinsic_cell_patches,
        prop_ic_patches: lowered.prop_ic_patches,
        body_off_patches: lowered.body_off_patches,
        ctor_nslots_patches: vec![],
        extra_bodies: vec![ExtraBody {
            sig: base.sig,
            body: base.body,
            body_off_patches: base.body_off_patches,
            main_call_patches: base.main_calls,
            prop_ic_patches: base.prop_ic_patches,
        }],
        extra_call_patches: lowered.baseline_calls.into_iter().map(|v| (v, 0)).collect(),
    }))
}
