/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The guest-side compiler for the in-process test lane: re-exports
//! `night-compiler` and `night-snapshot` so their C entry points are
//! linked into the shell's wasm module.

pub use night_compiler;
pub use night_snapshot;
