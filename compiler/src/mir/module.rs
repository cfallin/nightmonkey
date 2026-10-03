//! Module-level tables: what ops reference by id rather than carry inline
//! (MIR.md §1). The builder fills these from `LikelyFacts` and the
//! snapshot; after that, nothing downstream of the MIR reads the facts.

use std::collections::BTreeMap;

use crate::ids::{EnvSlot, JsString, LayoutKey, RegionRoot, ScriptId};
use crate::mir::entity::{AtomId, BindingId, EntityVec, FuseId, NativeId, RegionId, SnapObj};
use crate::mir::func::Func;
use crate::mir::types::{KeyRange, ObjKind, Type};
use crate::opsem::TaKind;

/// One predicted field of a layout: its name and the type its `TYPES`
/// bit guarantees (a `Val` type) when a load finds it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FieldDef {
    pub name: AtomId,
    pub claim: Type,
}

/// A predicted instance layout. Field `i` is fixed slot `i`; a `None`
/// is a slot the module does not describe (`hole` in the text format).
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Layout {
    pub fields: Vec<Option<FieldDef>>,
    /// Typed fields with no slot prediction (`named` in the text format):
    /// a `TYPES` claim by name, whose accesses find the slot by IC.
    pub named: Vec<FieldDef>,
    /// For array layouts: the class region the stamp proves, which names
    /// the `Elements`/`ArrayLength` alias regions of its accesses.
    pub elements: Option<RegionRoot>,
    /// Whether its stamp may be CLOSED (`closed_layouts`): publishing an
    /// object of exactly its row then makes it so.
    pub closed: bool,
}

impl Layout {
    pub fn named_field(&self, name: AtomId) -> Option<&FieldDef> {
        self.named.iter().find(|f| f.name == name)
    }

    pub fn field(&self, name: AtomId) -> Option<(usize, &FieldDef)> {
        self.fields
            .iter()
            .enumerate()
            .find_map(|(i, f)| f.as_ref().filter(|f| f.name == name).map(|f| (i, f)))
    }
}

/// A snapshot object referenced by identity. Only its immutable
/// components are recorded: its layout is heap state, and a `const.obj`
/// type never claims it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SnapObjDef {
    pub kind: ObjKind,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FuseDef {
    pub name: String,
    /// The fuse word's address (armed while it reads 1); 0 in a module
    /// with no runtime behind it.
    pub addr: u32,
}

/// A global binding, with the type its fast-path load may assume.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BindingDef {
    pub name: AtomId,
    pub claim: Type,
    /// The runtime's binding row (its syntactic global id, `syn_gnames`).
    pub slot: u32,
    /// The script whose function the analysis predicts the binding holds
    /// (`gname_fns`): `check.binding.fn` tests that it does, and a read
    /// under that check is the function, typed.
    pub pred: Option<ScriptId>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct NativeDef {
    pub name: String,
}

/// An alias region (§6). `None` in a key/root position is the partial
/// wildcard (`Field(*, name)`, `Elements(*)`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Region {
    Field {
        name: AtomId,
        keys: Option<KeyRange>,
    },
    Elements(Option<RegionRoot>),
    ArrayLength(Option<RegionRoot>),
    TypedArrayData(TaKind),
    TypedArrayLength,
    Global(BindingId),
    Env(EnvSlot),
    /// The frame's current environment (its env slot). Only this frame's
    /// scope ops (`env.set`, `env.pop`) write it: code the frame calls
    /// runs in frames of its own, so `Unknown` does not cover it.
    FrameEnv,
    /// Every region.
    Unknown,
}

impl Region {
    /// May an access to `self` touch the same memory as one to `o`?
    pub fn overlaps(&self, o: &Region) -> bool {
        use Region::*;
        match (self, o) {
            (Unknown, FrameEnv) | (FrameEnv, Unknown) => false,
            (Unknown, _) | (_, Unknown) => true,
            (Field { name: a, keys: ka }, Field { name: b, keys: kb }) => {
                a == b
                    && match (ka, kb) {
                        (Some(x), Some(y)) => x.overlaps(y),
                        _ => true,
                    }
            }
            (Elements(a), Elements(b)) | (ArrayLength(a), ArrayLength(b)) => {
                a.is_none() || b.is_none() || a == b
            }
            (a, b) => a == b,
        }
    }
}

/// The tables, plus the functions that reference them.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct Module {
    pub atoms: EntityVec<AtomId, JsString>,
    pub layouts: BTreeMap<LayoutKey, Layout>,
    pub snap_objs: EntityVec<SnapObj, SnapObjDef>,
    pub fuses: EntityVec<FuseId, FuseDef>,
    pub bindings: EntityVec<BindingId, BindingDef>,
    pub natives: EntityVec<NativeId, NativeDef>,
    pub regions: EntityVec<RegionId, Region>,
    pub funcs: Vec<Func>,
    /// The runtime `JSScript*` of each script a `guard.script` names
    /// (§5.5). Not printed: a module parsed from text has none.
    pub script_addrs: BTreeMap<crate::ids::ScriptId, u32>,
    /// Restamp descriptors `restamp` ops index: the runtime helper's
    /// arguments (`stamp::restamp_args`: layout, field count, kept bits,
    /// prefix keys + 1). Not printed.
    pub restamps: Vec<[u32; 7]>,
    /// The least stamp idx an array allocation carries (array keys grow
    /// down from the top of the key space, layout keys up from 1); `None`
    /// if none does. An element store's claim duty is to arrays: on any
    /// other object TYPES is its fields' claim. Not printed.
    pub array_key_min: Option<u32>,
}

impl Module {
    pub fn intern_atom(&mut self, s: &[u16]) -> AtomId {
        if let Some((id, _)) = self.atoms.iter().find(|(_, a)| a.chars() == s) {
            return id;
        }
        self.atoms.push(JsString::from_chars(s.to_vec()))
    }

    pub fn intern_region(&mut self, r: Region) -> RegionId {
        if let Some((id, _)) = self.regions.iter().find(|(_, x)| **x == r) {
            return id;
        }
        self.regions.push(r)
    }

    pub fn func(&self, script: crate::ids::ScriptId) -> Option<&Func> {
        self.funcs.iter().find(|f| f.script == script)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn region_overlap() {
        let x = AtomId::from_u32(0);
        let y = AtomId::from_u32(1);
        let k = |lo, hi| {
            Some(KeyRange {
                lo: LayoutKey::new(lo),
                hi: LayoutKey::new(hi),
            })
        };
        let f = |name, keys| Region::Field { name, keys };
        assert!(f(x, k(1, 3)).overlaps(&f(x, k(3, 4))));
        assert!(!f(x, k(1, 2)).overlaps(&f(x, k(3, 4))));
        assert!(!f(x, k(1, 3)).overlaps(&f(y, k(1, 3))));
        assert!(f(x, None).overlaps(&f(x, k(9, 9))));
        assert!(!f(x, None).overlaps(&f(y, None)));
        assert!(!f(x, None).overlaps(&Region::Elements(None)));
        let r = |n| Region::Elements(Some(RegionRoot::new(n)));
        assert!(!r(1).overlaps(&r(2)));
        assert!(Region::Elements(None).overlaps(&r(2)));
        assert!(!Region::Elements(None).overlaps(&Region::ArrayLength(None)));
        assert!(Region::Unknown.overlaps(&Region::Env(EnvSlot::new(0))));
        // Only the frame's own scope ops write its env slot.
        assert!(!Region::Unknown.overlaps(&Region::FrameEnv));
        assert!(Region::FrameEnv.overlaps(&Region::FrameEnv));
    }
}
