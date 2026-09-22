//! The guest-side compiler for the in-process test lane: re-exports
//! `night-compiler` and `night-snapshot` so their C entry points are
//! linked into the shell's wasm module.

pub use night_compiler;
pub use night_snapshot;
