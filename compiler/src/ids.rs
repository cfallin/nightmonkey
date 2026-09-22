/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Identifier newtypes for the analysis/translator contract.
//!
//! These exist so the compiler catches what review cannot: the fact tables
//! are keyed by pairs of small integers, and a swapped script/pc or a class
//! key used where a slot index belongs are mistakes a `u32` cannot report.

use crate::source::SourceObjectId;

/// A compiled script, named by its id in the source object graph.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ScriptId(u32);

impl ScriptId {
    pub const fn new(id: u32) -> ScriptId {
        ScriptId(id)
    }

    pub const fn get(self) -> u32 {
        self.0
    }

    pub const fn source(self) -> SourceObjectId {
        SourceObjectId::new(self.0)
    }
}

impl std::fmt::Display for ScriptId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A bytecode offset within one script.
///
/// Offsets carry their own type all the way through the analysis and the
/// lowering, so an offset can never be passed where a script id, an
/// argument position or a slot index belongs -- the mistakes a `u32` cannot
/// report. The arithmetic an offset genuinely needs is spelled out on the
/// type: advance by an instruction length, rebase into a spliced segment,
/// and resolve a relative branch.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Pc(u32);

impl Pc {
    pub const fn new(pc: u32) -> Pc {
        Pc(pc)
    }

    pub const fn get(self) -> u32 {
        self.0
    }

    /// The absolute target of a relative branch here with signed offset
    /// `off` -- the interpreter's own wrapping arithmetic.
    pub fn branch(self, off: i32) -> Pc {
        Pc((i64::from(self.0) + i64::from(off)) as u32)
    }
}

/// Advance by an instruction length (`pc + op.len()`): the only arithmetic
/// bytecode offsets need, and it stays within one script by construction.
impl std::ops::Add<u32> for Pc {
    type Output = Pc;
    fn add(self, rhs: u32) -> Pc {
        Pc(self.0 + rhs)
    }
}

/// Rebase into a spliced segment's local offset space (`pc - seg.base`).
impl std::ops::Sub<u32> for Pc {
    type Output = Pc;
    fn sub(self, rhs: u32) -> Pc {
        Pc(self.0 - rhs)
    }
}

impl std::ops::AddAssign<u32> for Pc {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs;
    }
}

impl std::fmt::Display for Pc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// One bytecode operation in the whole program: the key of every per-site
/// fact table.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Site {
    pub script: ScriptId,
    pub pc: Pc,
}

impl Site {
    pub const fn new(script: ScriptId, pc: Pc) -> Site {
        Site { script, pc }
    }

    /// From raw ids, for the FFI and dump boundaries that carry loose
    /// integers.
    pub const fn from_raw(script: u32, pc: u32) -> Site {
        Site::new(ScriptId::new(script), Pc::new(pc))
    }
}

impl std::fmt::Display for Site {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.script, self.pc)
    }
}

/// A predicted instance layout, named by the dense key a compiled
/// allocation stamps into an object's class word. Distinct from
/// `likelier::heap::ClassKey`, which names a class by its identity
/// (prototype object, constructor script, or allocation site) inside the
/// analysis; this is the emitted, translator-facing id. Keys of one predictor group are
/// contiguous, which is what lets a range guard cover a whole group.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct LayoutKey(u32);

impl LayoutKey {
    /// One past the last usable key.
    ///
    /// A stamped object carries its key in a 15-bit field of its class
    /// word, so the key space is an ABI limit shared by the analysis (which
    /// stops minting), the environment layout (which asserts) and the
    /// lowering (which range-guards on it) -- not a tuning parameter any
    /// one of them may raise alone.
    pub const LIMIT: u32 = 0x7FFF;

    pub const fn new(key: u32) -> LayoutKey {
        LayoutKey(key)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for LayoutKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The identity half of an object's stamp word: a [`LayoutKey`] biased by
/// one, so that 0 means "unstamped" and every real layout has a nonzero key.
///
/// This is the number a compiled allocation writes, a ctor-exit stamp
/// carries, and every class-fact guard compares against -- and it is off by
/// one from the [`LayoutKey`] the analysis and the layout tables use. The two
/// are both small integers naming the same layout, which is exactly why they
/// carry different types: a guard emitted against an unbiased key silently
/// tests the neighbouring layout.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct StampKey(u32);

impl StampKey {
    /// The unstamped word: no compiled allocation ever writes it.
    pub const NONE: StampKey = StampKey(0);

    pub const fn new(k: u32) -> StampKey {
        StampKey(k)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

impl LayoutKey {
    /// The stamp this layout's objects carry.
    pub const fn stamp(self) -> StampKey {
        StampKey(self.0 + 1)
    }
}

impl std::fmt::Display for StampKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The position of a field within a predicted instance layout: an index
/// into the layout row, which is also the object's fixed-slot index.
///
/// Distinct from [`LayoutKey`], which names the layout as a whole. The two
/// are both small integers and both appear in the same fact rows, which is
/// exactly why they carry different types.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct SlotIndex(u32);

impl SlotIndex {
    pub const fn new(i: u32) -> SlotIndex {
        SlotIndex(i)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for SlotIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An argument position within one script as the *fact tables* number
/// them: 0 is `this`, `1 + n` is formal `n`. Deliberately not a [`Pc`]:
/// the arg tables are keyed by position, and a bare `(u32, u32)` key here
/// is indistinguishable from the per-site tables' `(script, pc)` while
/// meaning something else entirely. The analysis's own numbering is
/// [`FormalIndex`], which counts formals from 0 and keeps the receiver in
/// a cell of its own.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ArgIndex(u32);

impl ArgIndex {
    /// The receiver.
    pub const THIS: ArgIndex = ArgIndex(0);

    pub const fn new(i: u32) -> ArgIndex {
        ArgIndex(i)
    }

    /// Formal `n` (which is index `1 + n`).
    pub const fn formal(n: u32) -> ArgIndex {
        ArgIndex(1 + n)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for ArgIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A formal parameter's position within one script, counted from 0
/// (`function f(a, b)`: `a` is 0). This is the analysis's numbering, where
/// the receiver is not an argument at all but its own cell; the emitted
/// fact tables use [`ArgIndex`], which numbers the receiver 0 and formal
/// `n` as `n + 1`. Two spaces one apart is exactly the confusion a
/// shared `u32` cannot report.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct FormalIndex(u32);

impl FormalIndex {
    pub const fn new(i: u32) -> FormalIndex {
        FormalIndex(i)
    }

    pub const fn get(self) -> u32 {
        self.0
    }

    /// The same position in the fact tables' numbering.
    pub const fn as_arg_index(self) -> ArgIndex {
        ArgIndex::formal(self.0)
    }
}

impl std::fmt::Display for FormalIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A slot in a closure environment (`CallObject`) -- the index an
/// aliased-variable access names within its scope. Not a [`VarId`]: the
/// scanner's variable numbering and a scope's slot numbering are different
/// spaces that share `u32`'s shape.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct EnvSlot(u32);

impl EnvSlot {
    pub const fn new(slot: u32) -> EnvSlot {
        EnvSlot(slot)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for EnvSlot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The union-find root of a class region: sibling allocation sites whose
/// values flowed together share one root, and therefore one array claim.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct RegionRoot(u32);

impl RegionRoot {
    pub const fn new(r: u32) -> RegionRoot {
        RegionRoot(r)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for RegionRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A local/temporary slot in the analysis's per-script variable numbering
/// (`engine::CKey::Var`). Not a [`Pc`] and not an [`ArgIndex`]: the solver's
/// callee-tracking tables are keyed by script and variable, which is a
/// different space that happened to share `(u32, u32)`'s shape.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct VarId(u32);

impl VarId {
    pub const fn new(v: u32) -> VarId {
        VarId(v)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for VarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A JavaScript string: property and binding names, string literals in the
/// source object graph, regex patterns.
///
/// JS strings are sequences of UTF-16 code units, not Rust `str`s -- they may
/// hold unpaired surrogates, so they do not always round-trip through UTF-8,
/// which is why the whole compiler carries them as code units. Naming the
/// type is what keeps a *string* distinct from the many other `Vec<u16>`
/// buffers around it, gives the name-keyed fact tables a key type that says
/// so, and gives every diagnostic one `Display` instead of a lossy conversion
/// open-coded at each site.
///
/// Ordering, hashing and `Borrow<[u16]>` are the underlying buffer's, so a
/// `JsString` key hashes exactly as the `Vec<u16>` it replaced.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
pub struct JsString(Vec<u16>);

impl JsString {
    pub fn from_chars(chars: Vec<u16>) -> JsString {
        JsString(chars)
    }

    pub fn chars(&self) -> &[u16] {
        &self.0
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Whether this is the name `s`, which is always ASCII at the call sites
    /// that ask (`length`, `charCodeAt`, the well-known method names).
    pub fn is(&self, s: &str) -> bool {
        self.0.iter().copied().eq(s.encode_utf16())
    }
}

/// So a `HashMap<JsString, _>` can be probed with a bare `&[u16]`. Sound
/// because the derived `Hash` and `Eq` are the code-unit slice's own.
impl std::borrow::Borrow<[u16]> for JsString {
    fn borrow(&self) -> &[u16] {
        &self.0
    }
}

/// Names deref to their code units, the way `String` derefs to `str`: the
/// slice operations are the same ones, and a `&JsString` passed where a
/// `&[u16]` is wanted coerces.
impl std::ops::Deref for JsString {
    type Target = [u16];
    fn deref(&self) -> &[u16] {
        &self.0
    }
}

impl From<&str> for JsString {
    fn from(s: &str) -> JsString {
        JsString(s.encode_utf16().collect())
    }
}

impl std::fmt::Display for JsString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for c in char::decode_utf16(self.0.iter().copied()) {
            write!(f, "{}", c.unwrap_or(char::REPLACEMENT_CHARACTER))?;
        }
        Ok(())
    }
}

/// A JS string interned in the compilation's one string table.
///
/// Every UTF-16 string the compiler names -- property names, global
/// bindings, layout field names -- gets one id here, assigned once and used
/// from the analysis through to emission. Comparing or keying by `NameId` is
/// an integer compare rather than a code-unit-buffer hash, and a name that
/// crosses the analysis/translator boundary crosses it as an id rather than
/// as a copy.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
pub struct NameId(pub u32);

/// The compilation's one string table: `NameId <-> JsString`.
///
/// Built before the analysis (the syntactic global-binding scan seeds it),
/// filled by the analysis, handed to the translator in `LikelyFacts`, and
/// finally owned by the `AtomTable`, which adds the emitted table's dense
/// numbering on top without a second copy of the strings.
#[derive(Default)]
pub struct Names {
    by_val: std::collections::HashMap<JsString, NameId, rustc_hash::FxBuildHasher>,
    vals: Vec<JsString>,
}

impl Names {
    /// Intern a Rust literal, without the caller materializing the UTF-16
    /// buffer itself.
    pub fn intern_str(&mut self, s: &str) -> NameId {
        let chars = JsString::from(s);
        self.intern(&chars)
    }

    pub fn intern(&mut self, n: &[u16]) -> NameId {
        if let Some(&id) = self.by_val.get(n) {
            return id;
        }
        let id = NameId(u32::try_from(self.vals.len()).unwrap());
        self.vals.push(JsString::from_chars(n.to_vec()));
        self.by_val.insert(JsString::from_chars(n.to_vec()), id);
        id
    }

    pub fn get(&self, id: NameId) -> &JsString {
        &self.vals[id.0 as usize]
    }

    pub fn lookup(&self, n: &[u16]) -> Option<NameId> {
        self.by_val.get(n).copied()
    }

    pub fn lossy(&self, id: NameId) -> String {
        String::from_utf16_lossy(self.get(id))
    }

    pub fn len(&self) -> usize {
        self.vals.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vals.is_empty()
    }
}
