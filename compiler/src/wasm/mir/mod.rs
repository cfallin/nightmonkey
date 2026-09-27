//! The MIR tier's driver under `pipeline=mir` (`docs/MIR.md` §9): build a
//! MIR body for the script, compile its baseline body with the MIR body's
//! exit and throw pcs as resume targets, and lower the MIR into the
//! script's table entry, with the baseline body beside it.

pub mod build;
pub(crate) mod inline;
pub mod lower;

use crate::bytecode::Script;
use crate::ids::ScriptId;
use crate::wasm::baseline;
use crate::wasm::baseline::layout;
use crate::wasm::translate::{AtomTable, ExtraBody, Outcome, TranslateCtx};
use waffle::Module;

/// Whether MIR inlines calls (§5.5; in progress).
const INLINING: bool = true;

/// The most bytecode a script may have to be inlined (§5.5).
pub(crate) const INLINE_MAX_BYTECODE: usize = 200;

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
        && !script.has_mapped_args
        && !baseline::layout::FrameLayout::of(script).rebase_vp
        && script.try_notes.iter().all(|t| t.kind == TryNoteKind::Loop)
        // The actuals ops read the frame they run in, which for an inlined
        // copy is not the callee's (`ArgumentsLength` is not in
        // `reads_actuals`).
        && !script.parser().opcodes().any(|op| {
            matches!(
                op,
                crate::bytecode::JSOp::ArgumentsLength
                    | crate::bytecode::JSOp::GetActualArg
                    | crate::bytecode::JSOp::Arguments
                    | crate::bytecode::JSOp::Rest
            )
        })
        && (!baseline::needs_env(script) || baseline::env_is_plain(ctx.source, script))
}

/// Compile `script` as a MIR body plus its baseline body. `Ok(Err(reason))`
/// is a decline: the caller falls back to baseline alone.
pub fn translate_script(
    ctx: &TranslateCtx,
    m: &mut Module,
    atoms: &mut AtomTable,
    sid: ScriptId,
    script: &Script,
    is_global: bool,
) -> Result<Result<Outcome, String>, String> {
    let (mm, mut f) = match build::build(ctx, &atoms.names, sid, script, is_global) {
        Ok(x) => x,
        Err(reason) => return Ok(Err(reason)),
    };
    // Guard folding (§10.1). The builder guards locally at every use;
    // this merges them, and the validator checks the result.
    let folded = crate::mir::opt::optimize(&mm, &mut f);
    if ctx.opts.diagnostics.stats && folded > 0 {
        crate::diag_line!("night: mir sid#{sid} folded {folded} guards");
    }
    if let Err(es) = crate::mir::verify(&mm, &f) {
        let first = es.first().map(|e| e.to_string()).unwrap_or_default();
        if ctx.opts.diagnostics.mir {
            crate::diag_line!(
                "night: invalid MIR for sid#{sid}:\n{}",
                crate::mir::print::print_func(&mm, &f)
            );
        }
        return Ok(Err(format!(
            "BUG: invalid MIR ({} errors; {first})",
            es.len()
        )));
    }
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
            // Capped, as bbv's: an over-full list only costs the helper.
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
    let lowered = match lower::lower(
        m,
        ctx.helpers,
        &mm,
        atoms,
        &f,
        baseline::layout::FrameLayout::of(script),
        baseline::layout::StackDepths::compute(script)?.max,
        lower::LowerOpts {
            stress: ctx.opts.mir_stress,
            exit_census: ctx.opts.instrument.mir_exits,
            strict: script.strict,
            plain_env: baseline::needs_env(script) && baseline::env_is_plain(ctx.source, script),
            own_env: baseline::needs_env(script) && !baseline::env_is_plain(ctx.source, script),
            forward_resume: inline_eligible(ctx, script),
            ctor_restamp: ctx.deleg_restamps_in.get(&sid).and_then(crate::wasm::bbv::restamp_args),
            ctor_stamp: ctx.stamp_ctors_in.get(&sid).map(|si| {
                [
                    si.layout_id,
                    u32::try_from(si.fields.len()).unwrap(),
                    crate::wasm::bbv::ctor_stamp_keep_bits(si),
                ]
            }),
        },
        gname_bids,
        gname_fused,
        add_preds,
    ) {
        Ok(l) => l,
        Err(reason) => return Ok(Err(reason)),
    };
    if ctx.opts.diagnostics.stats {
        crate::diag_line!(
            "night: mir body sid#{sid} blocks {} values {} bytecode {}",
            lowered.body.blocks.len(),
            lowered.body.values.len(),
            script.bytecode.len()
        );
    }
    Ok(Ok(Outcome::Compiled {
        sig: ctx.helpers.night_abi_sig2,
        body: lowered.body,
        likely_patches: vec![],
        fuse_call_patches: vec![],
        call_cell_patches: vec![],
        alloc_cell_patches: vec![],
        iof_cell_patches: lowered.iof_cell_patches,
        construct_cell_patches: lowered.construct_cell_patches,
        strlit_patches: vec![],
        intrinsic_cell_patches: vec![],
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
