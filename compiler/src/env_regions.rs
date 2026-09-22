//! Mirror of the engine's reserved-region descriptor. Generated at build
//! time from the `NIGHT_ENV_REGIONS` X-macro in
//! `js/src/night/runtime/NightEnv.h`, which is the single source of truth
//! for the field list, its order and each word's wire kind. Both writers --
//! the snapshot tool's `NightRegistration::regionTable` and the in-process
//! `env_desc` header -- fill `RegionWords` by name, so a field added,
//! removed or renamed in the header breaks the build here rather than
//! silently shifting a region base.

include!(concat!(env!("OUT_DIR"), "/env_regions.rs"));
