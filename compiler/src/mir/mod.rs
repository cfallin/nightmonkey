//! The MIR: NightMonkey's mid-tier IR for the optimized (OPT) track.
//!
//! See `docs/MIR.md` for the design. In short: SSA over a CFG with typed
//! block params, where a type is representation × refinement; per-object
//! facts live in the types of object references and global facts are
//! ghost values, so the invariants the optimizer relies on are structural
//! and a validator can check them without flow typing. GEN -- today's
//! `Dirty`-track lowering in `wasm::bbv` -- stays outside the MIR: it is
//! where exits land and where onramps come from.
//!
//! - [`types`]: the lattice (subtyping, join, killable components).

pub mod entity;
pub mod types;

pub use entity::{Block, Inst, Value};
pub use types::Type;
