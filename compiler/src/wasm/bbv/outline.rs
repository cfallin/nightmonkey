/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Per-family out-of-lining of Dirty-track op bodies into generic-helper
//! calls: the gen-only rung's arm-free forms, extended to every Dirty
//! version. Size first -- there is no per-family switch, because there is
//! no design to select between.

use super::*;

impl<'a> Bbv<'a> {
    /// One test per inline-arm decision. A Dirty-track body is a
    /// non-conforming execution: it carries no facts, so no fact could
    /// reach an inline arm's decision anyway, and the generic form is the
    /// whole of what it can say.
    ///
    /// KNOWN GAP, and the biggest one left in the emitter: this answers to
    /// the TRACK, so a lowering has exactly two shapes -- the full
    /// speculative bundle on Opt and the generic helper on GEN -- and a
    /// *weakly predicted* op on Opt gets the whole bundle, every arm
    /// emitted and every arm reached by a dynamic test. Measured on
    /// navier-stokes, one `Mul`: 1 emitted IR instruction with its operands
    /// typed, 15 out-of-lined on GEN, 410 on Opt with them untyped. The
    /// design's pressure valve ("a value the analysis cannot pin stays
    /// generic ON Opt") describes a shape that does not exist here. The arm
    /// policy has to answer to the prediction instead.
    pub(super) fn outline_generic(&self) -> bool {
        self.gen_only || self.cur_track == Track::Dirty
    }
}
