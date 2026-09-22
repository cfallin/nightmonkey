/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Read the JSScript graph of a SpiderMonkey-in-Wasm instance directly out of
//! its linear memory (a wizer snapshot for the external transform tool, or
//! the live memory itself for in-process compilation), producing the same
//! `night_compiler::source::Source` graph the compiler consumes.
//!
//! Layout knowledge comes from the engine's `NightLayoutDescriptor` (offsets
//! and flag constants recorded at registration time); facts that raw cell
//! reads cannot soundly derive (gcthing trace kinds, scope bindings) come
//! from the registration digest the engine serializes.

#[cfg(target_family = "wasm")]
pub mod ffi;
pub mod layout;
pub mod mem;
pub mod registration;
pub mod walker;

pub use layout::{Field, Layout};
pub use mem::{MemAccess, SliceMem};
pub use registration::{Digest, Registration};
pub use walker::{walk, WalkOutput};
