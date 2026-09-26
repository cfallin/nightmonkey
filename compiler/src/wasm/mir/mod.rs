//! The MIR tier's driver under `pipeline=mir` (`docs/MIR.md` §9): build a
//! MIR body for the script, compile its baseline body with the MIR body's
//! exit and throw pcs as resume targets, and lower the MIR into the
//! script's table entry, with the baseline body beside it.

pub mod build;
pub mod lower;

use crate::bytecode::Script;
use crate::ids::ScriptId;
use crate::wasm::baseline;
use crate::wasm::translate::{AtomTable, ExtraBody, Outcome, TranslateCtx};
use waffle::Module;

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
    let (mm, f) = match build::build(ctx, sid, script, is_global) {
        Ok(x) => x,
        Err(reason) => return Ok(Err(reason)),
    };
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
    let base = baseline::translate_script(ctx, m, atoms, sid, script, is_global, &resumes)?;
    let (base_sig, base_body, base_off) = match base {
        Outcome::Compiled {
            sig,
            body,
            body_off_patches,
            ..
        } => (sig, body, body_off_patches),
        Outcome::Skipped(reason) => return Ok(Err(format!("baseline declined: {reason}"))),
    };
    let lowered = match lower::lower(
        m,
        ctx.helpers,
        &mm,
        &f,
        baseline::layout::FrameLayout::of(script),
        ctx.opts.mir_stress,
    ) {
        Ok(l) => l,
        Err(reason) => return Ok(Err(reason)),
    };
    Ok(Ok(Outcome::Compiled {
        sig: ctx.helpers.night_abi_sig2,
        body: lowered.body,
        likely_patches: vec![],
        fuse_call_patches: vec![],
        call_cell_patches: vec![],
        alloc_cell_patches: vec![],
        iof_cell_patches: vec![],
        construct_cell_patches: vec![],
        strlit_patches: vec![],
        intrinsic_cell_patches: vec![],
        prop_ic_patches: vec![],
        body_off_patches: vec![],
        ctor_nslots_patches: vec![],
        extra_bodies: vec![ExtraBody {
            sig: base_sig,
            body: base_body,
            body_off_patches: base_off,
            main_call_patches: vec![],
        }],
        extra_call_patches: lowered.baseline_calls.into_iter().map(|v| (v, 0)).collect(),
    }))
}
