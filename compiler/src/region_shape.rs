/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Mirror of the reserved regions' internal shape: entry strides, table
//! sizes and intra-region offsets. Generated at build time from the
//! `NIGHT_REGION_SHAPE` X-macro in `js/src/night/runtime/NightRegionShape.h`,
//! which is the single source of truth.
//!
//! `env_regions` carries the region BASES; this carries what is inside one.
//! One literal is shared by both sides: a stride or table size out of step
//! between them is a silent miscompile, because a guard would read the
//! wrong address, and a change to the literal breaks whichever side stops
//! agreeing.

include!(concat!(env!("OUT_DIR"), "/region_shape.rs"));
