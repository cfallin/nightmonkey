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
pub(crate) use codegen::needs_env;
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
    source_id: ScriptId,
    script: &Script,
    is_global: bool,
) -> Result<Outcome, String> {
    Ok(
        match build_body(ctx, m, atoms, source_id, script, is_global, &[], &[])? {
            Ok(b) => Outcome::Compiled {
                sig: b.sig,
                body: b.body,
                likely_patches: vec![],
                fuse_call_patches: vec![],
                call_cell_patches: vec![],
                alloc_cell_patches: vec![],
                iof_cell_patches: vec![],
                construct_cell_patches: vec![],
                strlit_patches: vec![],
                intrinsic_cell_patches: vec![],
                prop_ic_patches: vec![],
                body_off_patches: b.body_off_patches,
                ctor_nslots_patches: vec![],
                extra_bodies: vec![],
                extra_call_patches: vec![],
            },
            Err(reason) => Outcome::Skipped(reason),
        },
    )
}

/// A built baseline body and its placeholders.
pub struct Built {
    pub sig: waffle::Signature,
    pub body: FunctionBody,
    /// Adapter-offset placeholders (`Outcome::Compiled::body_off_patches`).
    pub body_off_patches: Vec<waffle::Value>,
    /// Direct-call placeholders for the script's MIR body: the onramps.
    pub main_calls: Vec<waffle::Value>,
}

/// Build a script's baseline body; `Ok(Err(reason))` is a decline.
///
/// For the MIR tier (`docs/BASELINE.md` §4, §7):
/// - `resumes` are the resume words the MIR body's exits and throws
///   carry. The body then also accepts an `ARGC_RESUME_BIT` entry that
///   routes to them.
/// - `onramps` are the loop headers at which the MIR body has an onramp
///   root, each with the resume words its root reaches. At each, the body
///   calls the MIR body (`main_calls`) unless the frame's backoff says to
///   wait, and routes a DEOPT return by those words.
#[allow(clippy::too_many_arguments)]
pub fn build_body(
    ctx: &TranslateCtx,
    m: &mut Module,
    atoms: &mut AtomTable,
    _source_id: ScriptId,
    script: &Script,
    is_global: bool,
    resumes: &[layout::ResumeWord],
    onramps: &[(crate::ids::Pc, Vec<layout::ResumeWord>)],
) -> Result<Result<Built, String>, String> {
    if script
        .parser()
        .opcodes()
        .any(|op| op == JSOp::ForceInterpreter)
    {
        return Ok(Err(FORCE_INTERPRETER.into()));
    }
    // Code size is linear in bytecode size, but a multi-megabyte script
    // (an Emscripten-style giant function) becomes a function of millions
    // of blocks: waffle's backend validation walks the dominator tree per
    // value use, and the engine then compiles it as one Wasm function. Such
    // scripts stay interpreted. The bound is looser than BBV's 128 KiB: a
    // few-hundred-KiB script compiles fine here.
    const MAX_BASELINE_BYTECODE: usize = 1024 * 1024;
    if script.bytecode.len() > MAX_BASELINE_BYTECODE {
        return Ok(Err(format!(
            "script too large ({} bytecode bytes)",
            script.bytecode.len()
        )));
    }
    let depths = match StackDepths::compute(script) {
        Ok(d) => d,
        Err(e) => return Ok(Err(format!("stack depths ({e})"))),
    };
    if let Err(e) = depths.check_try_notes(script) {
        return Ok(Err(format!("BUG: try notes ({e})")));
    }
    // The generator state saved across a suspend holds locals and
    // operands, not the actuals or the arguments object: those may be read
    // only before the first suspend (the frontend reads them in the
    // prologue and keeps the results in bindings).
    if script.is_generator_or_async && reads_actuals_after_yield(script) {
        return Ok(Err("generator reads actuals after a yield".into()));
    }
    if codegen::needs_env(script) {
        if let Some(reason) = env_unsupported(ctx.source, script) {
            return Ok(Err(reason));
        }
    }
    let sig = ctx.helpers.night_abi_sig2;
    let body = FunctionBody::new(m, sig);
    let mut gen = match codegen::Gen::new(
        ctx, atoms, script, is_global, body, depths, resumes, onramps,
    ) {
        Ok(g) => g,
        Err(e) => return Ok(Err(e)),
    };
    if let Err(e) = gen.run() {
        return Ok(Err(e));
    }
    // The design promises reducibility by construction (docs/BASELINE.md
    // §4): check it, so a violation declines just this script, loudly.
    // (No explicit `body.validate()`: waffle's backend runs it on every
    // function anyway, and it is quadratic on long block chains; see
    // waffle's DOMTREE-TODO.md.)
    if let Err(e) = gen.body.verify_reducible() {
        return Ok(Err(format!("BUG: irreducible body ({e})")));
    }
    if ctx.opts.diagnostics.stats {
        crate::diag_line!(
            "night: baseline body sid#{} blocks {} values {} bytecode {}",
            _source_id,
            gen.body.blocks.len(),
            gen.body.values.len(),
            script.bytecode.len()
        );
    }
    let body_off_patches = std::mem::take(&mut gen.body_off_patches);
    let main_calls = std::mem::take(&mut gen.main_calls);
    Ok(Ok(Built {
        sig,
        body: gen.body,
        body_off_patches,
        main_calls,
    }))
}

/// The env shapes the baseline prologue can build (`NightEnvSetup`): a
/// Function body (with its optional named-lambda and call objects) or a
/// Global one.
fn env_unsupported(source: &crate::source::Source, script: &Script) -> Option<String> {
    use crate::source::{ScopeData, SourceObject};
    let bs = script.body_scope?;
    match source.object(bs) {
        // ScopeKind::Function == 0, ScopeKind::Global == 12 (vm/Scope.h).
        SourceObject::Scope(ScopeData { kind: 0 | 12, .. }) => None,
        SourceObject::Scope(ScopeData { kind, .. }) => {
            Some(format!("env under body scope kind {kind}"))
        }
        _ => Some("body scope is not a Scope".into()),
    }
}

/// Whether any op reading the frame's actuals or arguments object follows
/// (in bytecode order) the first suspend point.
fn reads_actuals_after_yield(script: &Script) -> bool {
    let mut yielded = false;
    let mut p = script.parser();
    while let Some(op) = p.next_op() {
        match op {
            JSOp::InitialYield | JSOp::Yield | JSOp::Await => yielded = true,
            JSOp::Arguments | JSOp::Rest | JSOp::GetActualArg | JSOp::ArgumentsLength
                if yielded =>
            {
                return true;
            }
            JSOp::GetArg | JSOp::SetArg if yielded && script.has_mapped_args => return true,
            _ => {}
        }
        let imm = usize::try_from(op.len()).unwrap() - 1;
        if imm > 0 && p.advance(imm).is_none() {
            break;
        }
    }
    false
}
