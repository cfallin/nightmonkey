/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Abstractions around the input to the AOT translator (the "source").
//!
//! The source is an object graph, with various kinds of objects (what
//! SpiderMonkey calls "GC things"):
//!
//! - native JS objects (including functions and plain objects with
//!   properties/elements)
//! - JS strings/atoms
//! - Bytecode hanging off of JS function objects
//!
//! Starting from one function with bytecode (the script toplevel), the
//! translator compiles the scripts reachable from it, together with a
//! snapshot of the heap they build.
//!
//! This source is built on the SpiderMonkey side before translation runs.
//! The `Source` struct below is the sole input; we do not accept any other
//! information via side-paths.

use crate::bytecode;
use crate::ids::JsString;
use crate::ids::ScriptId;

pub mod dump;
pub mod ffi;

/// Program source (including object graph and nested scripts) for
/// analysis.
#[derive(Debug)]
pub struct Source {
    pub objects: Vec<SourceObject>,
    /// The live global object (post-setup snapshot ingestion), if this
    /// source was built by the live-heap walk. Its own properties seed
    /// the `Global(name)` bindings (global-from-live).
    pub global_object: Option<SourceObjectId>,
    /// Self-hosted function scripts included beyond the user program tree:
    /// `(script id, dotted global path, e.g. "Array.prototype.forEach")`.
    /// They get no tree ordinal; the merge emits name-keyed patch entries
    /// the reactor resolves and arms at startup.
    pub selfhosted: Vec<(SourceObjectId, String)>,
    /// Regex literals found in compiled scripts, deduped by (pattern, flags):
    /// irregexp bytecode programs for AOT compilation to Wasm matchers.
    pub regex_programs: Vec<RegexProgramSrc>,
}

/// One regex literal's irregexp compilation artifacts (both subject
/// encodings), as extracted by the driver at AOT-compile time.
#[derive(Debug)]
pub struct RegexProgramSrc {
    pub pattern: JsString,
    pub flags: u32,
    pub latin1_bytecode: Vec<u8>,
    pub twobyte_bytecode: Vec<u8>,
    /// RegExpShared::getMaxRegisters().
    pub num_registers: u32,
    /// pairCount (whole match + captures); output regs = 2 * pair_count.
    pub pair_count: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceObjectId(u32);
impl SourceObjectId {
    pub const fn new(id: u32) -> SourceObjectId {
        SourceObjectId(id)
    }
    pub fn id(&self) -> u32 {
        self.0
    }
    pub fn is_other(&self) -> bool {
        *self == Self::other()
    }
    pub const fn other() -> Self {
        Self(u32::MAX)
    }
}

impl Source {
    pub fn object(&self, id: SourceObjectId) -> &SourceObject {
        &self.objects[usize::try_from(id.id()).unwrap()]
    }

    /// The script behind a scripted function object: `None` for a native
    /// (which has no script), a non-function, or an untranscribed
    /// reference.
    pub fn fn_script(&self, id: SourceObjectId) -> Option<ScriptId> {
        if id.is_other() {
            return None;
        }
        let SourceObject::Object(ObjectData {
            kind: ObjectKind::Function,
            script: Some(s),
            ..
        }) = self.object(id)
        else {
            return None;
        };
        Some(ScriptId::new(s.id()))
    }

    pub fn object_mut(&mut self, id: SourceObjectId) -> &mut SourceObject {
        &mut self.objects[usize::try_from(id.id()).unwrap()]
    }

    pub fn push(&mut self, obj: SourceObject) -> SourceObjectId {
        let id = u32::try_from(self.objects.len()).unwrap();
        let id = SourceObjectId(id);
        self.objects.push(obj);
        id
    }

    pub fn objects(&self) -> impl Iterator<Item = (SourceObjectId, &'_ SourceObject)> + '_ {
        self.objects
            .iter()
            .enumerate()
            .map(|(i, obj)| (SourceObjectId::new(u32::try_from(i).unwrap()), obj))
    }
}

#[derive(Debug)]
pub enum SourceObject {
    Object(ObjectData),
    Script(bytecode::Script),
    String(JsString),
    Primitive(Primitive),
    Scope(ScopeData),
    /// A symbol value; one node per distinct symbol (the walker dedups by
    /// address), so the id is its identity.
    Symbol,
}

/// A native JS object gcthing: a plain object, an array, or a function.
#[derive(Debug)]
pub struct ObjectData {
    pub non_native: bool,
    pub kind: ObjectKind,
    /// Heap-oracle certification (kind bit 8 on the wire): the object's
    /// own properties are exactly data-atom properties at slots 0..n-1,
    /// all fixed, non-dictionary -- the precondition for stamping the
    /// image object with a SLOTS-carrying layout word.
    pub slots_exact: bool,
    pub script: Option<SourceObjectId>,
    /// For functions: the function's explicit name, used by declaration
    /// instantiation.
    pub name: Option<SourceObjectId>,
    /// The object's concrete `[[Prototype]]`, recorded from the live heap
    /// (post-setup snapshot ingestion). `None` for the static gcthing walk,
    /// where the proto is synthesized from `kind`. Only set for
    /// non-primordial protos; a primordial (or null) proto is left `None` so
    /// transcription falls back to the `kind`-based builtin proto.
    pub proto: Option<SourceObjectId>,
    /// If this live object is a recognized primordial (its raw `BuiltinId` as
    /// u8): the identity overlay -- transcription reuses the described builtin
    /// abstraction (with its effect / pinned summary) instead of allocating a
    /// fresh one, and does not transcribe its fields (the description provides
    /// them).
    pub builtin_id: Option<u8>,
    pub properties: Vec<(SourceObjectId, SourceObjectId)>,
    pub elements: Vec<(u32, SourceObjectId)>,
}

/// A static scope (js::Scope). Scopes form a static chain via `enclosing`
/// that crosses script boundaries; a scope with `has_environment` creates a
/// runtime environment object (CallObject, lexical env, ...) on every entry,
/// holding its aliased bindings.
#[derive(Debug)]
pub struct ScopeData {
    /// Raw js::ScopeKind, for debugging.
    pub kind: u8,
    pub has_environment: bool,
    pub enclosing: Option<SourceObjectId>,
    /// (name, is_var, environment slot if the binding is closed-over) for each
    /// binding declared in the scope; used by declaration-instantiation and
    /// named-lambda modeling.
    pub bindings: Vec<(SourceObjectId, bool, Option<u32>)>,
    /// (env slot, value) pairs read from a live environment object
    /// (CallObject) captured by the post-setup snapshot. Seeds the scope's
    /// environment abstraction with the concrete values a setup-created
    /// closure holds, so steady-state `GetAliasedVar` resolves to them.
    pub env_slot_values: Vec<(u32, SourceObjectId)>,
    /// Whether this is a (Strict)NamedLambda scope: the scope holding a named
    /// function expression's self-name binding, which the VM initializes to
    /// the closure at creation.
    pub is_named_lambda: bool,
    /// `numFixedSlots` of the scope's environment shape (the template every
    /// environment object of this scope is created from), when the snapshot
    /// carried one. Lets an aliased-var access address its slot statically
    /// instead of decoding the fixed/dynamic split from the live shape.
    pub env_nfixed: Option<u32>,
}

/// The static scope an aliased-var access at `pc` in `script` names:
/// the innermost scope note covering `pc` (else the body scope), then
/// `hops` environment-creating scopes outward. Shared by the analysis and
/// the emitter so both address the same environment object.
pub fn aliased_scope_at(
    source: &Source,
    script: &bytecode::Script,
    pc: crate::ids::Pc,
    hops: u16,
) -> Option<SourceObjectId> {
    let mut cur: Option<SourceObjectId> = None;
    let mut best_len = u32::MAX;
    for n in &script.scope_notes {
        if n.gcthing_index == u32::MAX {
            continue;
        }
        if pc >= n.start && pc < n.start + n.length && n.length < best_len {
            if let Some(&gc) = script.gcthings.get(n.gcthing_index as usize) {
                if !gc.is_other() {
                    cur = Some(gc);
                    best_len = n.length;
                }
            }
        }
    }
    let mut cur = cur.or(script.body_scope)?;
    let mut remaining = i32::from(hops);
    loop {
        let SourceObject::Scope(ScopeData {
            has_environment,
            enclosing,
            ..
        }) = source.object(cur)
        else {
            return None;
        };
        if *has_environment {
            if remaining == 0 {
                return Some(cur);
            }
            remaining -= 1;
        }
        cur = (*enclosing)?;
    }
}

impl SourceObject {
    /// Unwrap as an `Object`, panicking otherwise.
    pub fn as_object_mut(&mut self) -> &mut ObjectData {
        let SourceObject::Object(obj) = self else {
            panic!("not an object");
        };
        obj
    }

    /// Unwrap as a `Scope`, panicking otherwise.
    pub fn as_scope_mut(&mut self) -> &mut ScopeData {
        let SourceObject::Scope(scope) = self else {
            panic!("not a scope");
        };
        scope
    }

    /// Unwrap as a `Script`, panicking otherwise.
    pub fn as_script_mut(&mut self) -> &mut bytecode::Script {
        let SourceObject::Script(script) = self else {
            panic!("not a script");
        };
        script
    }
}

/// The class of an object gcthing, as far as the analysis needs to
/// distinguish: it determines the object's `[[Prototype]]` and exotic
/// behaviors. Mirrors the `NIGHT_OBJECT_KIND_*` constants in
/// night_compiler.h.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectKind {
    /// Any class we don't model (Date, RegExp, Proxy, ...):
    /// conservatively unknown contents and proto.
    Other,
    Plain,
    Array,
    Function,
    /// A fixed-length typed-array view, with its element kind's 1-based
    /// code (the `opsem::TaKind` order). Transcribed by the oracle for
    /// receiver homing; no properties or elements ride it.
    TypedArray(u8),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Primitive {
    Undefined,
    Null,
    Boolean(bool),
    Int32(i32),
    Double(f64),
}
