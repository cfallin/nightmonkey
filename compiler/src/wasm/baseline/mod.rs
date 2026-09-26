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

pub mod layout;

use crate::bytecode::{JSOp, Script};
use crate::ids::ScriptId;
use crate::wasm::translate::{AtomTable, Outcome, TranslateCtx};
use layout::{FrameLayout, StackDepths};
use waffle::Module;

/// The decline reason for a script containing `ForceInterpreter`: the one
/// op baseline never compiles, because it means "run in the interpreter".
/// The coverage gate accepts it.
pub const FORCE_INTERPRETER: &str = "ForceInterpreter";

/// Translate one script to a baseline body, or decline. Same contract as
/// `bbv::translate_script`: `Outcome::Compiled` with a `night_abi_sig2`
/// body, or `Outcome::Skipped` with the reason (the script is then
/// interpreted).
///
/// B0: the frame contract only. Every script is checked -- layout, stack
/// depths, try-note agreement -- and then declined; codegen lands in B1.
pub fn translate_script(
    _ctx: &TranslateCtx,
    _m: &mut Module,
    _atoms: &mut AtomTable,
    _source_id: ScriptId,
    script: &Script,
    _is_global: bool,
) -> Result<Outcome, String> {
    if script
        .parser()
        .opcodes()
        .any(|op| op == JSOp::ForceInterpreter)
    {
        return Ok(Outcome::Skipped(FORCE_INTERPRETER.into()));
    }
    let _layout = FrameLayout::of(script);
    let depths = match StackDepths::compute(script) {
        Ok(d) => d,
        Err(e) => return Ok(Outcome::Skipped(format!("stack depths ({e})"))),
    };
    if let Err(e) = depths.check_try_notes(script) {
        return Ok(Outcome::Skipped(format!("BUG: try notes ({e})")));
    }
    Ok(Outcome::Skipped("not implemented".into()))
}
