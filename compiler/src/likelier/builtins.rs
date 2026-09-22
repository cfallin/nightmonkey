/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! What the analysis knows about the JavaScript builtins it does not have
//! bytecode for.
//!
//! The snapshot walker transcribes registered heap objects, so a native
//! function arrives as an opaque value with a name and nothing else. Three
//! kinds of spec knowledge fill that in, and they all live here so that
//! adding a builtin is one edit in one file:
//!
//! - result masks: what a named native returns (`native_result_for`), and
//!   which names preserve integrality (`integral_native` and friends);
//! - namespaces: the synthetic method/constant tables for `Math`, `JSON`
//!   and the rest, which the walker cannot transcribe at all
//!   (`NAMESPACES`);
//! - constructor names: the array and typed-array constructors, whose
//!   calls carry allocation semantics rather than a result mask
//!   (`ta_kind_for_ctor_name`, `is_array_ctor_name`), and the natives the
//!   translator has an inline arm for (`has_translator_arm`).
//!
//! Every claim here is likely, not proven: each consumer guards the callee
//! identity at runtime, so a program that shadows `Math` or replaces
//! `String.prototype.trim` simply misses its fast path.

use super::types::{FnId, NameId};
use crate::opsem::{
    Prims, TaKind, PRIM_BOOLEAN, PRIM_DOUBLE, PRIM_INT32, PRIM_STRING, PRIM_SYMBOL, PRIM_UNDEFINED,
};
use rustc_hash::FxHashMap as HashMap;

/// Which receiver a native name was resolved against. The receiver-typed
/// tables overlay the bare one, which is what lets `slice` mean
/// `String.prototype.slice` off a known-string receiver while staying
/// unmodeled off an unknown one.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum NativeKind {
    /// A bare name: a captured global native or a namespace member.
    Bare,
    /// A method called on a known-string receiver.
    StringMethod,
    /// A method called on a known-numeric receiver.
    NumberMethod,
}

/// Spec-derived call result masks for named natives (the EcmaScript spec
/// tells us these; modeling them beats teaching the rest of the analysis
/// to tolerate their absence). Only primitive-returning natives belong
/// here; object-returning or ambiguously-named natives (slice, concat,
/// split, exec, valueOf, ...) stay out and raise unresolved evidence at calls.
/// Names are matched on the native's own function name, which cannot
/// collide with user functions (those always carry scripts).
const NUM: Prims = PRIM_INT32.or(PRIM_DOUBLE);
const NATIVE_RESULTS: &[(&str, Prims)] = &[
    // Math.* (floor/ceil/round return integer-valued doubles the engine
    // may box as int32; random can yield 0 -> int32 box).
    ("abs", NUM),
    ("floor", NUM),
    ("ceil", NUM),
    ("round", NUM),
    ("trunc", NUM),
    ("sqrt", NUM),
    ("cbrt", NUM),
    ("pow", NUM),
    ("exp", NUM),
    ("expm1", NUM),
    ("log", NUM),
    ("log2", NUM),
    ("log10", NUM),
    ("log1p", NUM),
    ("sin", NUM),
    ("cos", NUM),
    ("tan", NUM),
    ("asin", NUM),
    ("acos", NUM),
    ("atan", NUM),
    ("atan2", NUM),
    ("sinh", NUM),
    ("cosh", NUM),
    ("tanh", NUM),
    ("asinh", NUM),
    ("acosh", NUM),
    ("atanh", NUM),
    ("min", NUM),
    ("max", NUM),
    ("random", NUM),
    ("sign", NUM),
    ("fround", NUM),
    ("hypot", NUM),
    ("imul", PRIM_INT32),
    ("clz32", PRIM_INT32),
    // Self-hosted intrinsics (GetIntrinsic references): spec-primitive
    // kernels the self-hosted string code bottoms out in.
    ("Substring", PRIM_STRING),
    ("ToString", PRIM_STRING),
    ("IsObject", PRIM_BOOLEAN),
    ("ToLength", NUM),
    ("ToInteger", NUM),
    ("Number_isNaN", PRIM_BOOLEAN),
    ("UnsafeGetStringFromReservedSlot", PRIM_STRING),
    ("UnsafeGetInt32FromReservedSlot", PRIM_INT32),
    ("RegExpSearcher", PRIM_INT32),
    ("RegExpSearcherLastLimit", PRIM_INT32),
    ("RegExpHasCaptureGroups", PRIM_BOOLEAN),
    ("RegExpGetSubstitution", PRIM_STRING),
    ("IsOptimizableRegExpObject", PRIM_BOOLEAN),
    ("SubstringKernel", PRIM_STRING),
    ("IsCallable", PRIM_BOOLEAN),
    ("AdvanceStringIndex", NUM),
    ("ThrowIncompatibleMethod", PRIM_UNDEFINED),
    ("ThrowTypeError", PRIM_UNDEFINED),
    ("print", PRIM_UNDEFINED),
    // Global value converters and predicates.
    ("parseInt", NUM),
    ("parseFloat", NUM),
    ("isNaN", PRIM_BOOLEAN),
    ("isFinite", PRIM_BOOLEAN),
    ("isInteger", PRIM_BOOLEAN),
    ("isSafeInteger", PRIM_BOOLEAN),
    ("Number", NUM),
    ("String", PRIM_STRING),
    ("Boolean", PRIM_BOOLEAN),
    ("Symbol", PRIM_SYMBOL),
    ("for", PRIM_SYMBOL),
    // Date called as a function returns a string (construct is handled
    // separately and yields unknown).
    ("Date", PRIM_STRING),
    ("escape", PRIM_STRING),
    ("unescape", PRIM_STRING),
    ("encodeURI", PRIM_STRING),
    ("decodeURI", PRIM_STRING),
    ("encodeURIComponent", PRIM_STRING),
    ("decodeURIComponent", PRIM_STRING),
    // String.prototype (and statics).
    ("charAt", PRIM_STRING),
    ("charCodeAt", NUM),
    ("codePointAt", NUM.or(PRIM_UNDEFINED)),
    ("fromCharCode", PRIM_STRING),
    ("fromCodePoint", PRIM_STRING),
    ("indexOf", NUM),
    ("lastIndexOf", NUM),
    ("search", NUM),
    ("includes", PRIM_BOOLEAN),
    ("startsWith", PRIM_BOOLEAN),
    ("endsWith", PRIM_BOOLEAN),
    ("localeCompare", NUM),
    ("substring", PRIM_STRING),
    ("substr", PRIM_STRING),
    ("toLowerCase", PRIM_STRING),
    ("toUpperCase", PRIM_STRING),
    ("toLocaleLowerCase", PRIM_STRING),
    ("toLocaleUpperCase", PRIM_STRING),
    ("trim", PRIM_STRING),
    ("trimStart", PRIM_STRING),
    ("trimEnd", PRIM_STRING),
    ("repeat", PRIM_STRING),
    ("padStart", PRIM_STRING),
    ("padEnd", PRIM_STRING),
    ("normalize", PRIM_STRING),
    ("replace", PRIM_STRING),
    ("replaceAll", PRIM_STRING),
    // Array.prototype (names not shared with differently-typed peers).
    ("join", PRIM_STRING),
    ("every", PRIM_BOOLEAN),
    ("some", PRIM_BOOLEAN),
    // Number.prototype formatters; every toString returns a string.
    ("toFixed", PRIM_STRING),
    ("toPrecision", PRIM_STRING),
    ("toExponential", PRIM_STRING),
    ("toString", PRIM_STRING),
    ("toLocaleString", PRIM_STRING),
    // Object.prototype predicates.
    ("hasOwnProperty", PRIM_BOOLEAN),
    ("isPrototypeOf", PRIM_BOOLEAN),
    ("propertyIsEnumerable", PRIM_BOOLEAN),
    // Object statics / Array statics (name-unambiguous predicates).
    ("is", PRIM_BOOLEAN),
    ("isArray", PRIM_BOOLEAN),
    ("isFrozen", PRIM_BOOLEAN),
    ("isSealed", PRIM_BOOLEAN),
    ("isExtensible", PRIM_BOOLEAN),
    // RegExp / json. ("parse" stays out: Date.parse is numeric but
    // Json.parse returns anything.)
    ("test", PRIM_BOOLEAN),
    ("stringify", PRIM_STRING.or(PRIM_UNDEFINED)),
    // Date: getters/setters return timestamps or components (NaN for
    // invalid dates -> double side), the to*String family strings.
    ("now", NUM),
    ("UTC", NUM),
    ("getTime", NUM),
    ("getFullYear", NUM),
    ("getMonth", NUM),
    ("getDate", NUM),
    ("getDay", NUM),
    ("getHours", NUM),
    ("getMinutes", NUM),
    ("getSeconds", NUM),
    ("getMilliseconds", NUM),
    ("getTimezoneOffset", NUM),
    ("getYear", NUM),
    ("getUTCFullYear", NUM),
    ("getUTCMonth", NUM),
    ("getUTCDate", NUM),
    ("getUTCDay", NUM),
    ("getUTCHours", NUM),
    ("getUTCMinutes", NUM),
    ("getUTCSeconds", NUM),
    ("getUTCMilliseconds", NUM),
    ("setTime", NUM),
    ("setFullYear", NUM),
    ("setMonth", NUM),
    ("setDate", NUM),
    ("setHours", NUM),
    ("setMinutes", NUM),
    ("setSeconds", NUM),
    ("setMilliseconds", NUM),
    ("setYear", NUM),
    ("toDateString", PRIM_STRING),
    ("toTimeString", PRIM_STRING),
    ("toISOString", PRIM_STRING),
    ("toUTCString", PRIM_STRING),
    ("toGMTString", PRIM_STRING),
    ("toLocaleDateString", PRIM_STRING),
    ("toLocaleTimeString", PRIM_STRING),
    ("toSource", PRIM_STRING),
    ("trimLeft", PRIM_STRING),
    ("trimRight", PRIM_STRING),
    ("isWellFormed", PRIM_BOOLEAN),
    ("toWellFormed", PRIM_STRING),
];

/// String.prototype methods, keyed by a known-string receiver -- which
/// disambiguates names the bare table must skip (slice/concat/at/valueOf
/// all return strings here).
const STRING_METHOD_RESULTS: &[(&str, Prims)] = &[
    ("slice", PRIM_STRING),
    ("concat", PRIM_STRING),
    ("at", PRIM_STRING.or(PRIM_UNDEFINED)),
    ("valueOf", PRIM_STRING),
];

/// Number.prototype methods under a known-numeric receiver.
const NUMBER_METHOD_RESULTS: &[(&str, Prims)] = &[("valueOf", NUM)];

/// Whether a UTF-16 property name equals a source literal.
///
/// Property names arrive from the engine as UTF-16 and every name this
/// module knows is written as a Rust `&str`, so the comparison is the most
/// repeated line in it.
pub(super) fn name_eq(name: &[u16], s: &str) -> bool {
    name.iter().copied().eq(s.encode_utf16())
}

fn lookup(table: &[(&str, Prims)], name: &[u16]) -> Option<Prims> {
    table
        .iter()
        .find(|(n, _)| name_eq(name, n))
        .map(|&(_, m)| m)
}

/// Integral-result natives: the value, when a Number, is an integer. These
/// are what carry an i53 claim through a `Math.floor` chain. NaN is the
/// optimism-with-guards case, same as the arith ladder.
pub(super) fn integral_native(name: &[u16]) -> bool {
    ["floor", "ceil", "round", "trunc", "parseInt"]
        .iter()
        .any(|n| name_eq(name, n))
}

/// Integrality-preserving natives: the result is integral iff every
/// argument is. abs/min/max are exact; pow's fractional cases (negative
/// or non-integral exponent) are the guarded rare ones at the Likely
/// stance -- pow(int, int>=0) is always integral (every IEEE double at
/// or above 2^52 is an integer; below that the result is exact). Without
/// this, one cold `Math.pow` feeding a bignum constructor ranges every
/// digit cell in the library to Top.
pub(super) fn integral_preserving_native(name: &[u16]) -> bool {
    ["pow", "abs", "min", "max"]
        .iter()
        .any(|n| name_eq(name, n))
}

/// The spec result mask of a native name resolved against `kind`, or
/// `None` for names this module does not model.
pub(super) fn native_result_for(kind: NativeKind, name: &[u16]) -> Option<Prims> {
    let overlay = match kind {
        NativeKind::StringMethod => lookup(STRING_METHOD_RESULTS, name),
        NativeKind::NumberMethod => lookup(NUMBER_METHOD_RESULTS, name),
        NativeKind::Bare => None,
    };
    overlay.or_else(|| lookup(NATIVE_RESULTS, name))
}

/// What a modeled native may write to pre-existing heap. `Pure` claims no
/// such writes (fresh allocation is allowed; argument coercion can still
/// reach user code, which is why summary consumers keep only
/// guarded/recoverable state); `Elems` writes only its receiver's
/// elements/length.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NativeEffect {
    Pure,
    Elems,
    Top,
}

/// Effect class of a native name resolved against `kind`: the modeled
/// primitive-returning names are `Pure` (`has_result` carries the
/// interned mask's presence, so mangled intrinsic ids classify by their
/// resolved result rather than by re-looking up the mangled name), the
/// in-place array mutators `Elems`, the allocation-only constructors and
/// object-returning pure kernels `Pure` by name, everything else `Top`
/// (`sort` stays `Top`: the comparator is user code).
pub(super) fn native_effect(kind: NativeKind, name: &[u16], has_result: bool) -> NativeEffect {
    const ELEMS: &[&str] = &[
        "push",
        "pop",
        "shift",
        "unshift",
        "fill",
        "copyWithin",
        "splice",
        "reverse",
    ];
    // No writes to pre-existing heap: fresh allocations and coercion
    // kernels (argument coercion reaching user code is tolerated by the
    // summary contract, same as every other Pure name).
    const PURE: &[&str] = &[
        "Error",
        "TypeError",
        "RangeError",
        "ReferenceError",
        "SyntaxError",
        "EvalError",
        "URIError",
        "RegExp",
        "ArrayBuffer",
        "create",
        "keys",
        "values",
        "entries",
        "freeze",
        "seal",
        "getPrototypeOf",
        "getOwnPropertyNames",
        "getOwnPropertyDescriptor",
        "%ToObject",
        "%RegExpMatcher",
        "%StringSplitString",
        "%GuardToSetObject",
        "%GuardToMapObject",
    ];
    if ELEMS.iter().any(|n| name_eq(name, n)) {
        NativeEffect::Elems
    } else if has_result
        || native_result_for(kind, name).is_some()
        || PURE.iter().any(|n| name_eq(name, n))
    {
        NativeEffect::Pure
    } else {
        NativeEffect::Top
    }
}

/// Whether a name is a plausible method of the given prim-receiver kind
/// (drives callee-position resolution off string/number receivers; only
/// modeled names resolve -- an absent name leaves the cell Empty).
pub(super) fn prim_method(kind: NativeKind, name: &[u16]) -> bool {
    native_result_for(kind, name).is_some()
        && match kind {
            NativeKind::StringMethod => {
                lookup(STRING_METHOD_RESULTS, name).is_some()
                    || STRING_PROTO_NAMES.iter().any(|n| name_eq(name, n))
            }
            NativeKind::NumberMethod => {
                lookup(NUMBER_METHOD_RESULTS, name).is_some()
                    || NUMBER_PROTO_NAMES.iter().any(|n| name_eq(name, n))
            }
            NativeKind::Bare => false,
        }
}

/// The bare-table names that genuinely live on String.prototype (the
/// bare table also holds Math/Date/... names a string receiver must not
/// resolve).
const STRING_PROTO_NAMES: &[&str] = &[
    "charAt",
    "charCodeAt",
    "codePointAt",
    "indexOf",
    "lastIndexOf",
    "search",
    "includes",
    "startsWith",
    "endsWith",
    "localeCompare",
    "substring",
    "substr",
    "toLowerCase",
    "toUpperCase",
    "toLocaleLowerCase",
    "toLocaleUpperCase",
    "trim",
    "trimStart",
    "trimEnd",
    "trimLeft",
    "trimRight",
    "repeat",
    "padStart",
    "padEnd",
    "normalize",
    "replace",
    "replaceAll",
    "toString",
    "isWellFormed",
    "toWellFormed",
];

const NUMBER_PROTO_NAMES: &[&str] = &[
    "toFixed",
    "toPrecision",
    "toExponential",
    "toString",
    "toLocaleString",
];

/// Synthesized builtin namespaces: the walker transcribes only registered
/// heap objects, so `Math` and friends arrive as other values. When the
/// global's binding is absent-or-other we seed a synthetic abstraction
/// whose field cells hold native fn ids (methods) and prim masks
/// (constants); program monkeypatches join into the same cells. `ctor`
/// gives the namespace value itself a callable native id (String(x),
/// Number(x), Date() -> string).
pub(super) struct NsSpec {
    pub global: &'static str,
    /// The namespace value is itself callable (`String(x)`, `Number(x)`).
    pub ctor: bool,
    pub methods: &'static [&'static str],
    pub consts: &'static [(&'static str, Prims)],
}

const D: Prims = PRIM_DOUBLE;
pub(super) const NAMESPACES: &[NsSpec] = &[
    NsSpec {
        global: "Math",
        ctor: false,
        methods: &[
            "abs", "floor", "ceil", "round", "trunc", "sqrt", "cbrt", "pow", "exp", "expm1", "log",
            "log2", "log10", "log1p", "sin", "cos", "tan", "asin", "acos", "atan", "atan2", "sinh",
            "cosh", "tanh", "asinh", "acosh", "atanh", "min", "max", "random", "sign", "fround",
            "hypot", "imul", "clz32",
        ],
        consts: &[
            ("E", D),
            ("LN10", D),
            ("LN2", D),
            ("LOG10E", D),
            ("LOG2E", D),
            ("PI", D),
            ("SQRT1_2", D),
            ("SQRT2", D),
        ],
    },
    NsSpec {
        global: "JSON",
        ctor: false,
        methods: &["stringify"],
        consts: &[],
    },
    NsSpec {
        global: "String",
        ctor: true,
        methods: &["fromCharCode", "fromCodePoint"],
        consts: &[],
    },
    NsSpec {
        global: "Number",
        ctor: true,
        methods: &[
            "isInteger",
            "isNaN",
            "isFinite",
            "isSafeInteger",
            "parseInt",
            "parseFloat",
        ],
        consts: &[
            ("POSITIVE_INFINITY", D),
            ("NEGATIVE_INFINITY", D),
            ("MAX_VALUE", D),
            ("MIN_VALUE", D),
            ("MAX_SAFE_INTEGER", D),
            ("MIN_SAFE_INTEGER", D),
            ("EPSILON", D),
            ("NaN", D),
        ],
    },
    NsSpec {
        global: "Boolean",
        ctor: true,
        methods: &[],
        consts: &[],
    },
    NsSpec {
        global: "Symbol",
        ctor: true,
        methods: &["for"],
        consts: &[],
    },
    NsSpec {
        global: "Date",
        ctor: true,
        methods: &["now", "UTC"],
        consts: &[],
    },
    NsSpec {
        global: "performance",
        ctor: false,
        methods: &["now"],
        consts: &[],
    },
    // defineProperty feeds the accessor table (calls.rs
    // eval_define_property); the other statics resolve to Bare natives
    // whose calls yield unknown evidence -- an unresolved callee left
    // the ret cell EMPTY, and Empty is worse than unknown (pdfjs builds
    // its dicts with Object.create; every consumer read as no-value).
    NsSpec {
        global: "Object",
        ctor: true,
        methods: &[
            "defineProperty",
            "create",
            "keys",
            "values",
            "entries",
            "assign",
            "freeze",
            "seal",
            "getPrototypeOf",
            "getOwnPropertyNames",
            "getOwnPropertyDescriptor",
        ],
        consts: &[],
    },
];

/// One modeled native, as the analysis knows it: a single struct rather
/// than parallel vectors indexed by a shared offset, so kind, name and
/// result cannot fall out of step.
pub struct NativeInfo {
    pub kind: NativeKind,
    pub name: NameId,
    /// The spec result mask, or `None` for a native this module does not
    /// model (whose calls raise unresolved evidence).
    pub result: Option<Prims>,
}

/// The reserved function ids minted for named natives.
#[derive(Default)]
pub struct Natives {
    /// Indexed by [`FnId::native_index`].
    by_index: Vec<NativeInfo>,
    ids: HashMap<(NativeKind, NameId), FnId>,
}

impl Natives {
    /// Get-or-mint the reserved id for a `(kind, name)` native, resolving
    /// its spec result mask once.
    pub fn intern(&mut self, kind: NativeKind, name: NameId, chars: &[u16]) -> FnId {
        if let Some(&id) = self.ids.get(&(kind, name)) {
            return id;
        }
        let id = FnId::native(u32::try_from(self.by_index.len()).unwrap());
        self.by_index.push(NativeInfo {
            kind,
            name,
            result: native_result_for(kind, chars),
        });
        self.ids.insert((kind, name), id);
        id
    }

    pub fn get(&self, f: FnId) -> Option<&NativeInfo> {
        self.by_index.get(f.native_index()? as usize)
    }
}

/// The typed-array constructor a name denotes, if any.
pub(super) fn ta_kind_for_ctor_name(name: &[u16]) -> Option<TaKind> {
    const NAMES: [(&str, TaKind); 9] = [
        ("Int8Array", TaKind::Int8),
        ("Uint8Array", TaKind::Uint8),
        ("Uint8ClampedArray", TaKind::Uint8Clamped),
        ("Int16Array", TaKind::Int16),
        ("Uint16Array", TaKind::Uint16),
        ("Int32Array", TaKind::Int32),
        ("Uint32Array", TaKind::Uint32),
        ("Float32Array", TaKind::Float32),
        ("Float64Array", TaKind::Float64),
    ];
    NAMES
        .iter()
        .find(|(s, _)| name_eq(name, s))
        .map(|&(_, k)| k)
}

/// Whether a name denotes the `Array` constructor.
pub(super) fn is_array_ctor_name(name: &[u16]) -> bool {
    name_eq(name, "Array")
}

/// Whether the translator has an inline arm for this bare-name native.
/// A site that resolves to one of these gets the `native_calls` fact; the
/// rest keep their spec result mask but go through the generic call path.
pub(super) fn has_translator_arm(name: &[u16]) -> bool {
    const ARMED: [&str; 14] = [
        "max", "min", "pow", "sqrt", "abs", "floor", "ceil", "trunc", "fround", "imul", "clz32",
        "sin", "cos", "parseInt",
    ];
    ARMED.iter().any(|n| name_eq(name, n))
}
