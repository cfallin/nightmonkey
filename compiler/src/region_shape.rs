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
