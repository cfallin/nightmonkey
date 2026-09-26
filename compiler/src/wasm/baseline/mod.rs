//! The baseline tier (`docs/BASELINE.md`): a deliberately simple compiled
//! tier that lowers each JSOp to a direct call to one NightMonkey runtime
//! helper (trivial stack and local ops inline), with the whole JS frame in
//! NightStack memory.
//!
//! Baseline is the correctness floor under MIR: a MIR exit writes a
//! baseline frame ([`layout`]) and resumes baseline at a pc, and baseline
//! loop headers onramp into MIR. It shares the AOT stack, the helper ABI
//! and the body signature with the legacy BBV path, so baseline bodies,
//! BBV bodies and the interpreter call one another freely.

mod codegen;
pub mod layout;

use crate::bytecode::{JSOp, Script};
use crate::ids::ScriptId;
use crate::wasm::translate::{AtomTable, Outcome, TranslateCtx};
use layout::StackDepths;
use waffle::{FunctionBody, Module};

/// The decline reason for a script containing `ForceInterpreter`: the one
/// op baseline never compiles, because it means "run in the interpreter".
/// The coverage gate accepts it.
pub const FORCE_INTERPRETER: &str = "ForceInterpreter";

/// Translate one script to a baseline body, or decline. Same contract as
/// `bbv::translate_script`: `Outcome::Compiled` with a `night_abi_sig2`
/// body, or `Outcome::Skipped` with the reason (the script is then
/// interpreted).
pub fn translate_script(
    ctx: &TranslateCtx,
    m: &mut Module,
    atoms: &mut AtomTable,
    _source_id: ScriptId,
    script: &Script,
    is_global: bool,
) -> Result<Outcome, String> {
    if script
        .parser()
        .opcodes()
        .any(|op| op == JSOp::ForceInterpreter)
    {
        return Ok(Outcome::Skipped(FORCE_INTERPRETER.into()));
    }
    let depths = match StackDepths::compute(script) {
        Ok(d) => d,
        Err(e) => return Ok(Outcome::Skipped(format!("stack depths ({e})"))),
    };
    if let Err(e) = depths.check_try_notes(script) {
        return Ok(Outcome::Skipped(format!("BUG: try notes ({e})")));
    }
    // The generator state saved across a suspend holds locals and
    // operands, not the actuals or the arguments object.
    if script.is_generator_or_async && layout::reads_actuals(script) {
        return Ok(Outcome::Skipped("generator using arguments".into()));
    }
    if crate::wasm::translate::uses_env_ops(script) {
        if let Some(reason) = crate::wasm::translate::env_unsupported(ctx.source, script) {
            return Ok(Outcome::Skipped(reason));
        }
    }
    let sig = ctx.helpers.night_abi_sig2;
    let body = FunctionBody::new(m, sig);
    let mut gen = match codegen::Gen::new(ctx, atoms, script, is_global, body, depths) {
        Ok(g) => g,
        Err(e) => return Ok(Outcome::Skipped(e)),
    };
    if let Err(e) = gen.run() {
        return Ok(Outcome::Skipped(e));
    }
    let body_off_patches = std::mem::take(&mut gen.body_off_patches);
    Ok(Outcome::Compiled {
        sig,
        body: gen.body,
        likely_patches: vec![],
        fuse_call_patches: vec![],
        call_cell_patches: vec![],
        alloc_cell_patches: vec![],
        iof_cell_patches: vec![],
        construct_cell_patches: vec![],
        strlit_patches: vec![],
        intrinsic_cell_patches: vec![],
        prop_ic_patches: vec![],
        body_off_patches,
        ctor_nslots_patches: vec![],
    })
}
