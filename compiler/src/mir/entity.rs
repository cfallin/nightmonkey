//! Typed indices and the arenas they index.
//!
//! The MIR is a graph of small integers -- values, blocks, instructions,
//! module-table rows -- and every one of them is a different space. As in
//! `crate::ids`, each gets its own newtype so a block can never be used
//! where a value belongs. `waffle::entity` has the same shape but its arenas
//! do not implement `PartialEq`, which the printer/parser round-trip
//! (`parse(print(f)) == f`) is stated in terms of; this is the minimal
//! equivalent that does.

use std::fmt::Debug;
use std::marker::PhantomData;

/// A dense index into one entity space.
pub trait EntityRef: Copy + Eq + Ord + std::hash::Hash + Debug {
    fn new(index: usize) -> Self;
    fn index(self) -> usize;
}

/// Declare an entity newtype. `$prefix` is its text-format spelling
/// (`v12`, `b3`, ...), shared by `Display` and the parser.
macro_rules! entity {
    ($(#[$m:meta])* $name:ident, $prefix:literal) => {
        $(#[$m])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(u32);

        impl $name {
            pub const PREFIX: &'static str = $prefix;

            pub const fn from_u32(i: u32) -> $name {
                $name(i)
            }

            pub const fn as_u32(self) -> u32 {
                self.0
            }
        }

        impl $crate::mir::entity::EntityRef for $name {
            fn new(index: usize) -> $name {
                $name(u32::try_from(index).unwrap())
            }
            fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}{}", $prefix, self.0)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}{}", $prefix, self.0)
            }
        }
    };
}

entity!(
    /// An SSA value: a block parameter or an instruction result. Ghost
    /// (`Fact`-typed) values are ordinary values of a ghost type.
    Value,
    "v"
);
entity!(
    /// A basic block.
    Block,
    "b"
);
entity!(
    /// An instruction, including terminators.
    Inst,
    "i"
);
entity!(
    /// A per-op attachment row (IC cells, call cells, site): what the
    /// lowering needs that is neither an operand nor derivable from types.
    AttachId,
    "a"
);
entity!(
    /// An alias region in the module table (MIR.md §6).
    RegionId,
    "R"
);
entity!(
    /// A snapshot object the module references by identity.
    SnapObj,
    "S"
);
entity!(
    /// An interned string: property names and string constants.
    AtomId,
    "A"
);
entity!(
    /// A fuse (a runtime-invalidated global assumption).
    FuseId,
    "F"
);
entity!(
    /// A global binding slot.
    BindingId,
    "G"
);
entity!(
    /// A native function whose intactness a `NativeIntact` fact asserts.
    NativeId,
    "N"
);

/// An arena that *defines* an index space: `push` hands out the next index.
#[derive(Clone, PartialEq, Eq)]
pub struct EntityVec<K: EntityRef, V> {
    items: Vec<V>,
    _k: PhantomData<K>,
}

impl<K: EntityRef, V> Default for EntityVec<K, V> {
    fn default() -> Self {
        EntityVec {
            items: Vec::new(),
            _k: PhantomData,
        }
    }
}

impl<K: EntityRef, V> EntityVec<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, v: V) -> K {
        let k = K::new(self.items.len());
        self.items.push(v);
        k
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn keys(&self) -> impl DoubleEndedIterator<Item = K> + ExactSizeIterator {
        (0..self.items.len()).map(K::new)
    }

    pub fn values(&self) -> impl DoubleEndedIterator<Item = &V> {
        self.items.iter()
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (K, &V)> {
        self.items.iter().enumerate().map(|(i, v)| (K::new(i), v))
    }

    pub fn get(&self, k: K) -> Option<&V> {
        self.items.get(k.index())
    }

    pub fn contains(&self, k: K) -> bool {
        k.index() < self.items.len()
    }
}

impl<K: EntityRef, V> std::ops::Index<K> for EntityVec<K, V> {
    type Output = V;
    fn index(&self, k: K) -> &V {
        &self.items[k.index()]
    }
}

impl<K: EntityRef, V> std::ops::IndexMut<K> for EntityVec<K, V> {
    fn index_mut(&mut self, k: K) -> &mut V {
        &mut self.items[k.index()]
    }
}

impl<K: EntityRef, V: Debug> Debug for EntityVec<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// A side table over an index space some other arena defines. Absent
/// entries read as `V::default()`; equality ignores trailing defaults, so
/// two maps that differ only in how far they were grown compare equal.
#[derive(Clone)]
pub struct EntityMap<K: EntityRef, V: Clone + Default> {
    items: Vec<V>,
    default: V,
    _k: PhantomData<K>,
}

impl<K: EntityRef, V: Clone + Default> Default for EntityMap<K, V> {
    fn default() -> Self {
        EntityMap {
            items: Vec::new(),
            default: V::default(),
            _k: PhantomData,
        }
    }
}

impl<K: EntityRef, V: Clone + Default> EntityMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Iterate the explicitly grown prefix of the map, in index order.
    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.items.iter().enumerate().map(|(i, v)| (K::new(i), v))
    }
}

impl<K: EntityRef, V: Clone + Default> std::ops::Index<K> for EntityMap<K, V> {
    type Output = V;
    fn index(&self, k: K) -> &V {
        self.items.get(k.index()).unwrap_or(&self.default)
    }
}

impl<K: EntityRef, V: Clone + Default> std::ops::IndexMut<K> for EntityMap<K, V> {
    fn index_mut(&mut self, k: K) -> &mut V {
        if k.index() >= self.items.len() {
            self.items.resize(k.index() + 1, V::default());
        }
        &mut self.items[k.index()]
    }
}

impl<K: EntityRef, V: Clone + Default + PartialEq> PartialEq for EntityMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        let n = self.items.len().max(other.items.len());
        (0..n).all(|i| {
            let a = self.items.get(i).unwrap_or(&self.default);
            let b = other.items.get(i).unwrap_or(&other.default);
            a == b
        })
    }
}

impl<K: EntityRef, V: Clone + Default + Eq> Eq for EntityMap<K, V> {}

impl<K: EntityRef, V: Clone + Default + Debug + PartialEq> Debug for EntityMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.iter().filter(|(_, v)| **v != self.default))
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vec_and_map() {
        let mut vs: EntityVec<Value, &str> = EntityVec::new();
        let a = vs.push("a");
        let b = vs.push("b");
        assert_eq!(a.to_string(), "v0");
        assert_eq!(vs[b], "b");
        let mut m: EntityMap<Value, u32> = EntityMap::new();
        assert_eq!(m[b], 0);
        m[b] = 7;
        assert_eq!(m[b], 7);
        let mut m2: EntityMap<Value, u32> = EntityMap::new();
        m2[b] = 7;
        m2[Value::from_u32(9)] = 0;
        assert_eq!(m, m2);
    }
}
