//! The JSOps-to-MIR builder (`docs/MIR.md` §8).

use crate::bytecode::Script;
use crate::ids::ScriptId;
use crate::mir;
use crate::wasm::translate::TranslateCtx;

/// Build the MIR body for `script`, or decline with a reason.
pub fn build(
    _ctx: &TranslateCtx,
    _sid: ScriptId,
    _script: &Script,
    _is_global: bool,
) -> Result<(mir::Module, mir::Func), String> {
    Err("no builder".into())
}
