/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! `TypeDesc`: the compiler's description of a JavaScript value's type.

use crate::opsem::Prims;

/// The inferred type of one value in a compiled function -- an operand on
/// the bytecode stack, a frame local, or a block parameter.
///
/// A `TypeDesc` denotes a *subset of all possible JavaScript values*: the
/// values that may reach this program point. It is an over-approximation,
/// and always a sound one. Every `TypeDesc` the lowering carries is a
/// guarantee, not a prediction: types enter from literals (the value is the
/// constant), from operator semantics (a compare produces a boolean), from
/// a block-entry context, or on the passing side of an emitted guard.
/// Likely-but-unproven facts live in [`crate::facts`] as bare bit sets and
/// only become a `TypeDesc` once a guard has tested them.
///
/// The full set is the union of two independent halves:
///
/// - `prims`: which *primitive* classes the value may belong to. A set bit
///   means "the value may be an int32 / a double / a string / ...", so more
///   bits is a weaker claim and clearing a bit is a refinement.
/// - `outside`: whether the value may be anything *outside* that primitive
///   alphabet -- an object, a function, or a value the analysis never
///   modeled. `false` is the strong claim: the value is definitely a
///   primitive drawn from `prims`.
///
/// The widest description (`prims` = [`ALL_PRIMS`], `outside` = true) claims
/// nothing; see `wasm::bbv::ctx::bottom_ty`, which is what an ordinary
/// helper-result push carries. The *empty* description (no `prims` bits and
/// `outside` false) does not mean "no value can occur here" -- nothing
/// proves that -- it means unreached or unmodeled, and consumers must treat
/// it as claiming nothing rather than as a contradiction.
///
/// Consumed by the block-versioning lowering in `wasm::bbv`: operand and
/// local types (`wasm::bbv::emit`), and projected onto a block-entry
/// context slot by `wasm::bbv::ctx::SlotCtx::of`, which is what makes a
/// proof durable across a whole version.
///
/// [`ALL_PRIMS`]: crate::opsem::ALL_PRIMS
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TypeDesc {
    pub prims: Prims,
    pub outside: bool,
}
