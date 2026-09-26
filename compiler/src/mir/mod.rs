//! The MIR: NightMonkey's mid-tier IR for the optimized (OPT) track.
//!
//! See `docs/MIR.md` for the design. In short: SSA over a CFG with typed
//! block params, where a type is representation × refinement; per-object
//! facts live in the types of object references and global facts are
//! ghost values, so the invariants the optimizer relies on are structural
//! and a validator can check them without flow typing. The baseline tier
//! (`wasm::baseline`, `docs/BASELINE.md`) stays outside the MIR: it is
//! where exits land and where onramps come from, and its frame format is
//! the whole interface between the two.
//!
//! - [`types`]: the lattice (subtyping, join, killable components);
//! - [`ops`]: opcodes, signatures, successor shapes and effect summaries;
//! - [`func`] and [`module`]: the function body and the module tables;
//! - [`print`] and [`parse`]: the text format, for tests and dumps;
//! - [`verify`]: the validator.

pub mod entity;
pub mod func;
pub mod module;
pub mod ops;
pub mod parse;
pub mod print;
pub mod types;
pub mod verify;

#[cfg(test)]
pub(crate) mod tests;

pub use entity::{Block, Inst, Value};
pub use func::Func;
pub use module::Module;
pub use parse::parse;
pub use print::print_module;
pub use types::Type;
pub use verify::{verify, verify_module};
