//! The engine's heap layout, for debug info: as DWARF types (so a
//! debugger can pretty-print JS values), as location-expression pieces
//! (environment and property slots), and as a reader of the snapshot
//! image (to resolve global bindings to slots at compile time).
//!
//! Every offset and bit here is SpiderMonkey's for wasm32 (NUNBOX32
//! values, 4-byte pointers) with the external-compiler hooks, and agrees
//! with the constants codegen bakes in (`wasm::mir::abi`), which
//! `NightInlineHeap.cpp` pins with `static_assert`s.

use gimli::write::{AttributeValue, DwarfUnit, Expression, UnitEntryId};

use crate::source::{ScopeData, Source, SourceObject};
use crate::wasm::mir::abi::{
    FIXED_SLOTS_BASE, NATIVE_SLOTS_OFFSET, OBJ_ELEMENTS_OFFSET, SHAPE_FIXED_SLOTS_MASK_BITS,
    SHAPE_FIXED_SLOTS_SHIFT, SHAPE_IMMUTABLE_FLAGS_OFFSET,
};

/// Read access to the snapshot image (linear memory).
pub trait Image {
    fn read_u32(&self, addr: u32) -> Option<u32>;
    fn read_u16(&self, addr: u32) -> Option<u16> {
        let w = self.read_u32(addr & !3)?;
        Some((w >> (8 * (addr & 2))) as u16)
    }
    fn read_u8(&self, addr: u32) -> Option<u8> {
        let w = self.read_u32(addr & !3)?;
        Some((w >> (8 * (addr & 3))) as u8)
    }
}

// --- layout -------------------------------------------------------------------

const SHAPE_PROPMAP_OFFSET: u32 = 16;
const SHAPE_MAP_LENGTH_MASK: u32 = 0xf;
const PROPMAP_KEYS_OFFSET: u32 = 4;
const PROPMAP_CAPACITY: u32 = 8;
const PROPMAP_IS_COMPACT: u32 = 1 << 3;
const PROPMAP_HAS_PREV: u32 = 1 << 4;
const PROPMAP_IS_DICTIONARY: u32 = 1 << 5;
const COMPACT_PROPINFOS_OFFSET: u32 = 36;
const LINKED_PREVIOUS_OFFSET: u32 = 36;
const LINKED_PROPINFOS_OFFSET: u32 = 44;
const PROPINFO_SLOT_SHIFT: u32 = 8;
const PROPINFO_ACCESSOR: u32 = 0x8;
const PROPINFO_CUSTOM_DATA: u32 = 0x10;
const JSID_VOID: u32 = 2;
const STRING_ATOM_BIT: u32 = 1 << 3;
const STRING_LINEAR_BIT: u32 = 1 << 4;
const STRING_DEPENDENT_BIT: u32 = 1 << 5;
const STRING_INLINE_CHARS_BIT: u32 = 1 << 6;
const STRING_LATIN1_CHARS_BIT: u32 = 1 << 10;
const FUNCTION_ENV_OFFSET: u32 = FIXED_SLOTS_BASE + 8;
const TAG_OBJECT: u32 = 0xFFFF_FF8C;
/// EnvironmentObject::ENCLOSING_ENV_SLOT, a fixed slot of every
/// environment object.
const ENCLOSING_ENV_SLOT: u32 = 0;

// --- DWARF types --------------------------------------------------------------

/// The type DIEs other debug info refers to.
pub struct Types {
    /// `JS::Value`, the type of every binding.
    pub value: UnitEntryId,
}

/// A member type, by name of a type defined earlier.
enum M {
    U32,
    U64,
    Named(&'static str),
    Ptr(&'static str),
    Array(&'static str, u64),
}

/// Struct types: (name, byte size, members (name, type, offset)).
/// Overlapping members describe a union's arms.
const STRUCTS: &[(&str, u64, &[(&str, M, u64)])] = &[
    ("JS::Value", 8, &[("asBits_", M::U64, 0)]),
    (
        "js::NativeObject",
        16,
        &[
            ("shape_", M::Ptr("js::Shape"), 0),
            ("externalWord_", M::U32, 4),
            ("slots_", M::Ptr("JS::Value"), NATIVE_SLOTS_OFFSET as u64),
            ("elements_", M::Ptr("JS::Value"), OBJ_ELEMENTS_OFFSET as u64),
            ("fixedSlots_", M::Array("JS::Value", 0), FIXED_SLOTS_BASE as u64),
        ],
    ),
    (
        "js::ObjectElements",
        16,
        &[
            ("flags", M::U32, 0),
            ("initializedLength", M::U32, 4),
            ("capacity", M::U32, 8),
            ("length", M::U32, 12),
        ],
    ),
    (
        "js::Shape",
        24,
        &[
            ("base_", M::Ptr("js::BaseShape"), 0),
            ("immutableFlags", M::U32, SHAPE_IMMUTABLE_FLAGS_OFFSET as u64),
            ("objectFlags_", M::U32, 8),
            ("cache_", M::U32, 12),
            ("propMap_", M::Ptr("js::PropMap"), SHAPE_PROPMAP_OFFSET as u64),
        ],
    ),
    (
        "js::BaseShape",
        16,
        &[
            ("clasp_", M::Ptr("JSClass"), 0),
            ("realm_", M::U32, 4),
            ("proto_", M::Ptr("js::NativeObject"), 8),
        ],
    ),
    (
        "JSClass",
        24,
        &[("name", M::Ptr("char"), 0), ("flags", M::U32, 4)],
    ),
    (
        "js::PropMap",
        36,
        &[
            ("flags_", M::U32, 0),
            ("keys_", M::Array("uint32_t", PROPMAP_CAPACITY as u64), PROPMAP_KEYS_OFFSET as u64),
        ],
    ),
    (
        "js::CompactPropMap",
        64,
        &[
            ("flags_", M::U32, 0),
            ("keys_", M::Array("uint32_t", PROPMAP_CAPACITY as u64), PROPMAP_KEYS_OFFSET as u64),
            (
                "propInfos_",
                M::Array("uint16_t", PROPMAP_CAPACITY as u64),
                COMPACT_PROPINFOS_OFFSET as u64,
            ),
        ],
    ),
    (
        "js::LinkedPropMap",
        80,
        &[
            ("flags_", M::U32, 0),
            ("keys_", M::Array("uint32_t", PROPMAP_CAPACITY as u64), PROPMAP_KEYS_OFFSET as u64),
            ("previous_", M::Ptr("js::PropMap"), LINKED_PREVIOUS_OFFSET as u64),
            ("table_", M::U32, 40),
            (
                "propInfos_",
                M::Array("uint32_t", PROPMAP_CAPACITY as u64),
                LINKED_PROPINFOS_OFFSET as u64,
            ),
        ],
    ),
    (
        "JSString",
        16,
        &[
            ("flags_", M::U32, 0),
            ("length_", M::U32, 4),
            ("inlineStorage_", M::Array("uint8_t", 0), 8),
            ("nonInlineChars_", M::Ptr("uint8_t"), 8),
            ("left_", M::Ptr("JSString"), 8),
            ("right_", M::Ptr("JSString"), 12),
            ("base_", M::Ptr("JSString"), 12),
        ],
    ),
    (
        "JS::Symbol",
        16,
        &[
            ("description_", M::Ptr("JSString"), 0),
            ("code_", M::U32, 4),
            ("hash_", M::U32, 8),
        ],
    ),
    (
        "JS::BigInt",
        16,
        &[
            ("flags_", M::U32, 0),
            ("digitLength_", M::U32, 4),
            ("inlineDigits_", M::Array("uint32_t", 2), 8),
            ("heapDigits_", M::Ptr("uint32_t"), 8),
        ],
    ),
    (
        "JSFunction",
        48,
        &[
            ("shape_", M::Ptr("js::Shape"), 0),
            ("flagsAndArgCount_", M::Named("JS::Value"), FIXED_SLOTS_BASE as u64),
            ("environment_", M::Named("JS::Value"), FUNCTION_ENV_OFFSET as u64),
            ("script_", M::Named("JS::Value"), FIXED_SLOTS_BASE as u64 + 16),
            ("atom_", M::Named("JS::Value"), FIXED_SLOTS_BASE as u64 + 24),
        ],
    ),
    (
        "js::GetterSetter",
        8,
        &[
            ("getter_", M::Ptr("js::NativeObject"), 0),
            ("setter_", M::Ptr("js::NativeObject"), 4),
        ],
    ),
];

/// Enumeration types (all u32): the engine's tags and flag bits.
const ENUMS: &[(&str, &[(&str, i64)])] = &[
    (
        "JSValueTag",
        &[
            ("JSVAL_TAG_SHIFT", 32),
            ("JSVAL_TAG_CLEAR", 0xFFFF_FF80),
            ("JSVAL_TAG_INT32", 0xFFFF_FF81),
            ("JSVAL_TAG_BOOLEAN", 0xFFFF_FF82),
            ("JSVAL_TAG_UNDEFINED", 0xFFFF_FF83),
            ("JSVAL_TAG_NULL", 0xFFFF_FF84),
            ("JSVAL_TAG_MAGIC", 0xFFFF_FF85),
            ("JSVAL_TAG_STRING", 0xFFFF_FF86),
            ("JSVAL_TAG_SYMBOL", 0xFFFF_FF87),
            ("JSVAL_TAG_PRIVATE_GCTHING", 0xFFFF_FF88),
            ("JSVAL_TAG_BIGINT", 0xFFFF_FF89),
            ("JSVAL_TAG_OBJECT", TAG_OBJECT as i64),
        ],
    ),
    (
        "JSWhyMagic",
        &[
            ("JS_ELEMENTS_HOLE", 0),
            ("JS_NO_ITER_VALUE", 1),
            ("JS_GENERATOR_CLOSING", 2),
            ("JS_ARG_POISON", 3),
            ("JS_SERIALIZE_NO_NODE", 4),
            ("JS_IS_CONSTRUCTING", 5),
            ("JS_HASH_KEY_EMPTY", 6),
            ("JS_ION_ERROR", 7),
            ("JS_ION_BAILOUT", 8),
            ("JS_OPTIMIZED_OUT", 9),
            ("JS_UNINITIALIZED_LEXICAL", 10),
            ("JS_MISSING_ARGUMENTS", 11),
        ],
    ),
    (
        "js::ShapeFlags",
        &[
            ("MAP_LENGTH_MASK", SHAPE_MAP_LENGTH_MASK as i64),
            ("KIND_SHIFT", 4),
            ("KIND_MASK", 3),
            ("KIND_DICTIONARY", 3),
            // Shared and dictionary shapes (native objects) have it;
            // proxy and Wasm GC shapes do not.
            ("IS_NATIVE_BIT", 1 << 4),
            ("FIXED_SLOTS_SHIFT", SHAPE_FIXED_SLOTS_SHIFT as i64),
            ("FIXED_SLOTS_MASK", SHAPE_FIXED_SLOTS_MASK_BITS as i64),
        ],
    ),
    (
        "js::PropMapFlags",
        &[
            ("IsCompact", PROPMAP_IS_COMPACT as i64),
            ("HasPrev", PROPMAP_HAS_PREV as i64),
            ("IsDictionary", PROPMAP_IS_DICTIONARY as i64),
            ("Capacity", PROPMAP_CAPACITY as i64),
        ],
    ),
    (
        "js::PropertyFlags",
        &[
            ("Configurable", 0x1),
            ("Enumerable", 0x2),
            ("Writable", 0x4),
            ("AccessorProperty", PROPINFO_ACCESSOR as i64),
            ("CustomDataProperty", PROPINFO_CUSTOM_DATA as i64),
            ("SlotShift", PROPINFO_SLOT_SHIFT as i64),
        ],
    ),
    (
        "js::PropertyKeyTags",
        &[
            ("TypeMask", 7),
            ("StringTypeTag", 0),
            ("IntTagBit", 1),
            ("VoidTypeTag", JSID_VOID as i64),
            ("SymbolTypeTag", 4),
        ],
    ),
    (
        "js::StringFlags",
        &[
            ("ATOM_BIT", STRING_ATOM_BIT as i64),
            ("LINEAR_BIT", STRING_LINEAR_BIT as i64),
            ("DEPENDENT_BIT", STRING_DEPENDENT_BIT as i64),
            ("INLINE_CHARS_BIT", STRING_INLINE_CHARS_BIT as i64),
            ("LATIN1_CHARS_BIT", STRING_LATIN1_CHARS_BIT as i64),
        ],
    ),
    (
        "js::FunctionFlags",
        &[
            ("FUNCTION_KIND_MASK", 7),
            ("ARROW_KIND", 1),
            ("METHOD_KIND", 2),
            ("CLASSCONSTRUCTOR_KIND", 3),
            ("GETTER_KIND", 4),
            ("SETTER_KIND", 5),
            ("BASESCRIPT", 1 << 5),
            ("SELFHOSTLAZY", 1 << 6),
            ("CONSTRUCTOR", 1 << 8),
            ("FLAGS_MASK", 0xffff),
            ("ARGCOUNT_SHIFT", 16),
        ],
    ),
    (
        "js::ObjectElementsFlags",
        &[("NON_PACKED", 0x80), ("FROZEN", 0x40)],
    ),
];

/// Emit the heap layout's types into the unit.
pub fn emit_types(dwarf: &mut DwarfUnit) -> Types {
    let root = dwarf.unit.root();
    let mut named = std::collections::HashMap::new();
    let base = |dwarf: &mut DwarfUnit, name: &'static str, enc: gimli::DwAte, size: u8| {
        let id = dwarf.unit.add(root, gimli::DW_TAG_base_type);
        let e = dwarf.unit.get_mut(id);
        e.set(gimli::DW_AT_name, AttributeValue::String(name.as_bytes().to_vec()));
        e.set(gimli::DW_AT_encoding, AttributeValue::Encoding(enc));
        e.set(gimli::DW_AT_byte_size, AttributeValue::Data1(size));
        id
    };
    for (name, enc, size) in [
        ("uint8_t", gimli::DW_ATE_unsigned, 1),
        ("uint16_t", gimli::DW_ATE_unsigned, 2),
        ("uint32_t", gimli::DW_ATE_unsigned, 4),
        ("uint64_t", gimli::DW_ATE_unsigned, 8),
        ("char", gimli::DW_ATE_signed_char, 1),
        ("char16_t", gimli::DW_ATE_UTF, 2),
        ("double", gimli::DW_ATE_float, 8),
    ] {
        let id = base(dwarf, name, enc, size);
        named.insert(name, id);
    }
    // Declare every struct first, so members can point at any of them.
    for &(name, size, _) in STRUCTS {
        let id = dwarf.unit.add(root, gimli::DW_TAG_structure_type);
        let e = dwarf.unit.get_mut(id);
        e.set(gimli::DW_AT_name, AttributeValue::String(name.as_bytes().to_vec()));
        e.set(gimli::DW_AT_byte_size, AttributeValue::Udata(size));
        named.insert(name, id);
    }
    let mut ptrs = std::collections::HashMap::new();
    for &(name, _, members) in STRUCTS {
        let parent = named[name];
        for (mname, mty, off) in members {
            let ty = match mty {
                M::U32 => named["uint32_t"],
                M::U64 => named["uint64_t"],
                M::Named(n) => named[n],
                M::Ptr(n) => *ptrs.entry(*n).or_insert_with(|| {
                    let p = dwarf.unit.add(root, gimli::DW_TAG_pointer_type);
                    let e = dwarf.unit.get_mut(p);
                    e.set(gimli::DW_AT_type, AttributeValue::UnitRef(named[n]));
                    e.set(gimli::DW_AT_byte_size, AttributeValue::Data1(4));
                    p
                }),
                M::Array(n, len) => {
                    let a = dwarf.unit.add(root, gimli::DW_TAG_array_type);
                    dwarf
                        .unit
                        .get_mut(a)
                        .set(gimli::DW_AT_type, AttributeValue::UnitRef(named[n]));
                    let sub = dwarf.unit.add(a, gimli::DW_TAG_subrange_type);
                    if *len > 0 {
                        dwarf
                            .unit
                            .get_mut(sub)
                            .set(gimli::DW_AT_count, AttributeValue::Udata(*len));
                    }
                    a
                }
            };
            let m = dwarf.unit.add(parent, gimli::DW_TAG_member);
            let e = dwarf.unit.get_mut(m);
            e.set(gimli::DW_AT_name, AttributeValue::String(mname.as_bytes().to_vec()));
            e.set(gimli::DW_AT_type, AttributeValue::UnitRef(ty));
            e.set(gimli::DW_AT_data_member_location, AttributeValue::Udata(*off));
        }
    }
    for &(name, enumerators) in ENUMS {
        let id = dwarf.unit.add(root, gimli::DW_TAG_enumeration_type);
        let e = dwarf.unit.get_mut(id);
        e.set(gimli::DW_AT_name, AttributeValue::String(name.as_bytes().to_vec()));
        e.set(gimli::DW_AT_byte_size, AttributeValue::Data1(4));
        e.set(gimli::DW_AT_type, AttributeValue::UnitRef(named["uint32_t"]));
        for &(ename, value) in enumerators {
            let en = dwarf.unit.add(id, gimli::DW_TAG_enumerator);
            let e = dwarf.unit.get_mut(en);
            e.set(gimli::DW_AT_name, AttributeValue::String(ename.as_bytes().to_vec()));
            e.set(gimli::DW_AT_const_value, AttributeValue::Udata(value as u64));
        }
    }
    Types {
        value: named["JS::Value"],
    }
}

// --- location expressions -----------------------------------------------------

/// Given an environment object's address on the stack, replace it with
/// its enclosing environment's address.
pub fn env_enclosing(e: &mut Expression) {
    e.op_plus_uconst(u64::from(FIXED_SLOTS_BASE + 8 * ENCLOSING_ENV_SLOT));
    e.op_deref_size(4);
}

/// Given a native object's address on the stack, replace it with the
/// address of its slot `slot`, for an object with `nfixed` fixed slots.
pub fn object_slot(e: &mut Expression, slot: u32, nfixed: u32) {
    if slot < nfixed {
        e.op_plus_uconst(u64::from(FIXED_SLOTS_BASE + 8 * slot));
    } else {
        e.op_plus_uconst(u64::from(NATIVE_SLOTS_OFFSET));
        e.op_deref_size(4);
        e.op_plus_uconst(u64::from(8 * (slot - nfixed)));
    }
}

// --- the snapshot image -------------------------------------------------------

/// Where an object's own data property lives.
#[derive(Clone, Copy, Debug)]
pub struct SlotLoc {
    pub slot: u32,
    /// The object's fixed-slot count (from its shape).
    pub nfixed: u32,
}

/// The fixed-slot count of the object at `obj`.
pub fn nfixed(image: &dyn Image, obj: u32) -> Option<u32> {
    let shape = image.read_u32(obj)?;
    let flags = image.read_u32(shape + SHAPE_IMMUTABLE_FLAGS_OFFSET)?;
    Some((flags >> SHAPE_FIXED_SLOTS_SHIFT) & SHAPE_FIXED_SLOTS_MASK_BITS)
}

/// The own data property `name` of the native object at `obj`.
pub fn own_property_slot(image: &dyn Image, obj: u32, name: &str) -> Option<SlotLoc> {
    let shape = image.read_u32(obj)?;
    let flags = image.read_u32(shape + SHAPE_IMMUTABLE_FLAGS_OFFSET)?;
    let nfixed = (flags >> SHAPE_FIXED_SLOTS_SHIFT) & SHAPE_FIXED_SLOTS_MASK_BITS;
    let mut map = image.read_u32(shape + SHAPE_PROPMAP_OFFSET)?;
    let mut len = flags & SHAPE_MAP_LENGTH_MASK;
    let want: Vec<u16> = name.encode_utf16().collect();
    // Bounded: a corrupt chain must not loop forever.
    for _ in 0..1_000_000 {
        if map == 0 || len == 0 {
            return None;
        }
        let mflags = image.read_u32(map)?;
        for i in (0..len).rev() {
            let key = image.read_u32(map + PROPMAP_KEYS_OFFSET + 4 * i)?;
            if key == JSID_VOID || key & 7 != 0 {
                continue;
            }
            if read_atom(image, key).as_deref() != Some(&want[..]) {
                continue;
            }
            let info = if mflags & PROPMAP_IS_COMPACT != 0 {
                u32::from(image.read_u16(map + COMPACT_PROPINFOS_OFFSET + 2 * i)?)
            } else {
                image.read_u32(map + LINKED_PROPINFOS_OFFSET + 4 * i)?
            };
            if info & (PROPINFO_ACCESSOR | PROPINFO_CUSTOM_DATA) != 0 {
                return None;
            }
            return Some(SlotLoc {
                slot: info >> PROPINFO_SLOT_SHIFT,
                nfixed,
            });
        }
        if mflags & PROPMAP_HAS_PREV == 0 {
            return None;
        }
        map = image.read_u32(map + LINKED_PREVIOUS_OFFSET)?;
        len = PROPMAP_CAPACITY;
    }
    None
}

/// The name in a function object's atom slot: its explicit name, or the
/// name the frontend guessed for an anonymous function from where it is
/// assigned (`Scheduler.prototype.schedule`).
pub fn function_atom(image: &dyn Image, fun: u32) -> Option<String> {
    // JSFunction::AtomSlot (fixed slot 3).
    let slot = FIXED_SLOTS_BASE + 8 * 3;
    let (payload, tag) = (image.read_u32(fun + slot)?, image.read_u32(fun + slot + 4)?);
    // JSVAL_TAG_STRING.
    if tag != 0xFFFF_FF86 || payload == 0 {
        return None;
    }
    read_atom(image, payload).map(|c| String::from_utf16_lossy(&c))
}

/// The characters of the flat string (an atom) at `s`.
fn read_atom(image: &dyn Image, s: u32) -> Option<Vec<u16>> {
    let flags = image.read_u32(s)?;
    if flags & STRING_LINEAR_BIT == 0 {
        return None;
    }
    let len = image.read_u32(s + 4)?;
    if len > 4096 {
        return None;
    }
    let chars = if flags & STRING_INLINE_CHARS_BIT != 0 {
        s + 8
    } else {
        image.read_u32(s + 8)?
    };
    let mut out = Vec::with_capacity(len as usize);
    for i in 0..len {
        out.push(if flags & STRING_LATIN1_CHARS_BIT != 0 {
            u16::from(image.read_u8(chars + i)?)
        } else {
            image.read_u16(chars + 2 * i)?
        });
    }
    Some(out)
}

/// The global lexical environment: the environment of any top-level
/// function (its scope's enclosing scope is the global scope).
pub fn global_lexical_env(
    image: &dyn Image,
    source: &Source,
    object_addr: &dyn Fn(u32) -> Option<u32>,
) -> Option<u32> {
    // ScopeKind::Global (vm/ScopeKind.h).
    const SK_GLOBAL: u8 = 12;
    for (i, o) in source.objects.iter().enumerate() {
        let SourceObject::Object(od) = o else { continue };
        let Some(sc) = od.script else { continue };
        let SourceObject::Script(script) = source.object(sc) else {
            continue;
        };
        let Some(body) = script.body_scope else {
            continue;
        };
        let SourceObject::Scope(ScopeData {
            enclosing: Some(enc),
            ..
        }) = source.object(body)
        else {
            continue;
        };
        if !matches!(source.object(*enc), SourceObject::Scope(ScopeData { kind: SK_GLOBAL, .. })) {
            continue;
        }
        let Some(addr) = object_addr(u32::try_from(i).unwrap()) else {
            continue;
        };
        let (payload, tag) = (
            image.read_u32(addr + FUNCTION_ENV_OFFSET)?,
            image.read_u32(addr + FUNCTION_ENV_OFFSET + 4)?,
        );
        if tag == TAG_OBJECT && payload != 0 {
            return Some(payload);
        }
    }
    None
}
