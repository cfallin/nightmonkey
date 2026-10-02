// Stylistic lints the emitter's shape legitimately conflicts with: lowering
// entry points take many arguments, `to_*` converts an operand rather than
// `self`, and rustdoc list formatting is not a goal.
#![allow(
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::wrong_self_convention,
    clippy::large_enum_variant,
    clippy::doc_lazy_continuation,
    clippy::doc_overindented_list_items
)]
//! NightMonkey: an ahead-of-time compiler from SpiderMonkey bytecode to
//! WebAssembly.
//!
//! The compiler takes a snapshot of a JavaScript program -- its scripts plus
//! the object graph they have built by the end of setup -- and emits a Wasm
//! module that runs it, with no bytecode interpreter on the hot path.
//!
//! JavaScript has no static types, so a translation that committed to
//! nothing would be a threaded interpreter in Wasm clothing: every operand
//! boxed, every operator a helper call. NightMonkey instead runs a
//! whole-program *likely-types* analysis and compiles code specialized to
//! what it finds -- unboxed int32 and double values, direct calls, inline
//! property loads at predicted slots.
//!
//! What the analysis produces is a **prediction, never a proof**. Every
//! specialization is emitted behind a runtime guard, and every guard has a
//! generic fallback that is correct for any value. Correctness therefore
//! rests entirely on the guards and the fallbacks; a wrong prediction costs
//! a failed guard and a slower path, never a wrong answer. Nothing in the
//! analysis has to be sound, which is what lets it be aggressive. Scripts
//! the translator cannot handle are simply left interpreted.
//!
//! The pipeline, in order:
//!
//! - [`source`] -- the input object graph, read out of the engine's linear
//!   memory by `night-snapshot`. The sole input: the compiler reads no
//!   other channel, and in particular takes no profiling data.
//! - [`bytecode`] -- the SpiderMonkey bytecode reader.
//! - [`likelier`] -- the likely-types analysis: one incremental fixpoint
//!   over constraints generated once per function, with calling context as
//!   part of edge identity. Its output is [`facts::LikelyFacts`], the whole
//!   contract between analysis and translator.
//! - [`mir`] and [`wasm`] -- the translator, in two tiers. `wasm::mir`
//!   builds each script into MIR, a typed SSA IR in which every predicted
//!   fact is checked once at its source and then held, optimizes it, and
//!   lowers it to Wasm; a failed check exits to the script's baseline body
//!   (`wasm::baseline`), a generic one-op-at-a-time lowering that also
//!   compiles every script MIR declines (`docs/MIR.md`,
//!   `docs/BASELINE.md`).
//! - [`opsem`] -- the operator-semantics vocabulary (result types, numeric
//!   ranges, interval arithmetic) that the analysis and the lowering share,
//!   so both reason about `+` in the same words.
//!
//! Output is either an in-process batch of function bodies compiled into a
//! live engine ([`wasm::inprocess`], driven by `wasm-jit-runner`'s
//! `night_compile` hostcall) or a standalone module produced by the
//! snapshot compiler, `nightmonkey`.

pub mod bytecode;
pub mod constants;
pub mod env_regions;
pub mod facts;
pub mod ids;
pub mod likelier;
pub mod mir;
pub mod opcodes;
pub mod opsem;
pub mod options;
pub mod region_shape;
pub mod source;
pub mod wasm;

pub use options::{Diagnostics, Options, Pipeline};
