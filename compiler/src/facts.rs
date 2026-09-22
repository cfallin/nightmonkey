/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! The likely-facts contract between the analysis (`likelier`) and the
//! translator: the output tables and their caps. Every fact is a
//! *prediction* that codegen re-checks at runtime; a wrong fact costs a
//! failed guard, never correctness.

use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;

use crate::ids::{ArgIndex, LayoutKey, NameId, Names, RegionRoot, ScriptId, Site, SlotIndex};
pub use crate::opsem::ValueRange;
use crate::opsem::{Prims, TaKind};

/// A likely type claim about one value, as it travels from the analysis to
/// the translator.
///
/// A claim is a *prediction*. The translator consumes every one of them
/// behind a runtime guard whose miss arm is correct for any value, so a
/// wrong claim costs a failed guard and a slower path, never correctness.
///
/// A claim says one of three things:
///
/// - nothing ([`Claim::NONE`]) -- no prediction was reached;
/// - the value is one of a set of primitive classes (in practice always a
///   purely numeric set: int32, double, or both);
/// - the value is an object or function, with no primitive component
///   ([`Claim::OBJECT`]).
///
/// Boolean- and string-only claims are representable here but are neither
/// emitted nor consumed by this type.
///
/// Primitive claims may additionally carry the *double-first* hint, which
/// is a hint about arm order rather than an extra type: the site's double
/// evidence is fractional-reachable (its cell range is Top with a real
/// double class), so a genuine double population is live at runtime -- a
/// fractional value has no int32 form and must double-tag, the i53 law's
/// contrapositive -- and the typed-load ladder should try the exact-double
/// form first even though int32 is in the set.
///
/// The wire representation packs all of this into one `u16`, which is why
/// it is a type and not a bare integer: the object claim and the
/// double-first hint live in bits the primitive alphabet does not use, and
/// every consumer that wants the primitive set must go through
/// [`Claim::prims`] rather than reading the word.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct Claim(u16);

impl Claim {
    /// No prediction.
    pub const NONE: Claim = Claim(0);

    /// The value is an object or function (no primitive component).
    pub const OBJECT: Claim = Claim(Self::OBJECT_BIT);

    const OBJECT_BIT: u16 = 1 << 15;
    const DOUBLE_FIRST_BIT: u16 = 1 << 14;
    /// Typed-array kind code (`TaKind::code`, 1..=9; 0 = none) beside an
    /// object claim: the value is a fixed-length typed array of that kind.
    const TA_SHIFT: u16 = 8;
    const TA_MASK: u16 = 0xF << Self::TA_SHIFT;

    /// A claim that the value is one of `prims`.
    pub fn of_prims(prims: Prims) -> Claim {
        Claim(prims.bits())
    }

    /// The serialized word (for the fact dump and the diagnostic views).
    pub const fn bits(self) -> u16 {
        self.0
    }

    /// Rebuild from a serialized word.
    pub const fn from_bits(bits: u16) -> Claim {
        Claim(bits)
    }

    pub const fn is_none(self) -> bool {
        self.0 == 0
    }

    pub const fn is_object(self) -> bool {
        self.0 & !Self::TA_MASK == Self::OBJECT_BIT
    }

    /// The typed-array kind of an object claim, when it names one.
    pub const fn ta_kind(self) -> Option<crate::opsem::TaKind> {
        if !self.is_object() {
            return None;
        }
        crate::opsem::TaKind::from_code(((self.0 & Self::TA_MASK) >> Self::TA_SHIFT) as u8)
    }

    /// An object claim narrowed to typed arrays of kind `k`.
    pub const fn object_of_ta(k: crate::opsem::TaKind) -> Claim {
        Claim(Self::OBJECT_BIT | ((k.code() as u16) << Self::TA_SHIFT))
    }

    /// The claim without its typed-array kind: what a read's own tag
    /// ladder proves (the kind is proven by the element op's clasp guard).
    pub const fn sans_ta(self) -> Claim {
        Claim(self.0 & !Self::TA_MASK)
    }

    /// The primitive classes claimed, with the flag bits stripped. Empty
    /// for [`Claim::NONE`] and [`Claim::OBJECT`].
    pub const fn prims(self) -> Prims {
        Prims::from_bits(self.0)
    }

    /// Whether the typed-load ladder should take the exact-double form
    /// first (see the type docs).
    pub const fn double_first(self) -> bool {
        self.0 & Self::DOUBLE_FIRST_BIT != 0
    }

    /// This claim with the double-first hint set.
    pub const fn with_double_first(self) -> Claim {
        Claim(self.0 | Self::DOUBLE_FIRST_BIT)
    }
}

impl std::fmt::Debug for Claim {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_none() {
            return f.write_str("none");
        }
        if self.is_object() {
            return match self.ta_kind() {
                Some(k) => write!(f, "object[{k:?}]"),
                None => f.write_str("object"),
            };
        }
        write!(f, "{:?}", self.prims())?;
        if self.double_first() {
            f.write_str("+dblfirst")?;
        }
        Ok(())
    }
}

/// Which of the two delegating call forms a call site spells.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CallForm {
    /// `T.call(this, a, b)`: the arguments are written out at the site.
    Call,
    /// `T.apply(this, args)`: the arguments arrive as one array value.
    Apply,
}

/// The predicted contents of one field position in a class's instance
/// layout.
#[derive(Clone, Debug, Default)]
pub struct ClassFieldFacts {
    /// The field's name. Its position in [`ClassFacts::fields`] is the
    /// predicted fixed-slot index: SpiderMonkey assigns slots in
    /// property-creation order, so the order of first writes is the
    /// prediction.
    pub name: NameId,
    /// Predicted value type. Only purely-numeric fields carry one.
    /// Consumed by the shallow-conformance machinery: checked stores
    /// maintain "this field holds a value of this type", the
    /// shallow-conforming flag asserts it, and conforming loads then skip
    /// the value tag check.
    pub prims: Prims,
    /// Predicted value range. A range rides its own stamp bit (RANGES)
    /// rather than TYPES, because it is consumed checklessly and so cannot
    /// survive the engine choke's numberness-only maintenance. Claimed
    /// only at positions that also carry a `prims` claim: the range is the
    /// value's magnitude and `prims` is its tag, and no consumer wants one
    /// without the other.
    pub range: Option<ValueRange>,
    /// The effective claim in fullword/dims mode: `prims` where the write
    /// tier claimed one, otherwise the name-keyed claim filled in from the
    /// typed tier. Equal to `prims` when the typed tier adds nothing.
    pub typed_prims: Prims,
}

/// The predicted instance layout of one class, keyed in
/// [`LikelyFacts::classes`] by its [`LayoutKey`] -- which is what
/// `ctor_stamps`, `this_layouts` and `deleg_restamps` point at, not the
/// constructor script.
///
/// Consumed via guard cells that the C++ validator checks at runtime, so a
/// wrong layout costs the fast path and never correctness.
#[derive(Clone, Debug, Default)]
pub struct ClassFacts {
    pub fields: Vec<ClassFieldFacts>,
}

/// How the analysis resolved one call site.
///
/// The arms are mutually exclusive outcomes, not flags: a site whose every
/// evaluation agreed on one modeled native has no scripted callee to offer,
/// and a site with scripted callees never settled on a native. Making that
/// an enum rather than two parallel tables is what keeps a consumer from
/// having to ask both and decide which wins.
#[derive(Clone, Debug)]
pub enum CallResolution {
    /// Every evaluation agreed on one modeled bare-name native the
    /// translator has an inline arm for. *Which* native is not part of the
    /// fact: the arm is selected at emission from the callee itself, so
    /// this only says the site has a single modeled native behind it, and
    /// the runtime callee-identity guard makes a wrong answer a missed fast
    /// path rather than a miscompile.
    Native,
    /// `1..=MAX_SITE_TARGETS` scripted callees, for the guarded dispatch
    /// and inlining arms. A singleton also arms the guarded direct call; a
    /// small polymorphic set arms the guard chain.
    Scripted(Vec<ScriptId>),
}

/// Post-fixpoint per-script effect summary: what a call to this script,
/// its resolved callees folded in transitively, may write to pre-existing
/// heap. Produced from the solved state only, never fed into the solve.
/// `top` means the walk met an op or a call edge it could not classify;
/// the other fields are meaningless then. Call resolution is likely, not
/// proven, so the summary shares the facts contract: a consumer keeps
/// only guarded/recoverable state on its strength.
#[derive(Clone, Debug, Default)]
pub struct EffectSummary {
    pub top: bool,
    /// What saturated the summary (an op name, "cap", a call-edge reason).
    /// Diagnostic only: excluded from equality, so the summary fixpoint
    /// cannot churn on why-strings propagating around a recursive cycle.
    pub top_why: Option<String>,
    /// Property writes: the write-site receiver's layout-key range when
    /// its receivers agreed on a planned class, else None = unknown
    /// receiver.
    pub field_writes: Vec<(Option<(LayoutKey, LayoutKey)>, NameId)>,
    pub gname_writes: Vec<NameId>,
    pub elems_write: bool,
    pub env_write: bool,
}

impl PartialEq for EffectSummary {
    fn eq(&self, other: &EffectSummary) -> bool {
        self.top == other.top
            && self.field_writes == other.field_writes
            && self.gname_writes == other.gname_writes
            && self.elems_write == other.elems_write
            && self.env_write == other.env_write
    }
}
impl Eq for EffectSummary {}

impl EffectSummary {
    pub fn saturate(&mut self, why: impl Into<String>) {
        if !self.top {
            self.top = true;
            self.top_why = Some(why.into());
        }
    }

    pub fn is_write_free(&self) -> bool {
        !self.top
            && self.field_writes.is_empty()
            && self.gname_writes.is_empty()
            && !self.elems_write
            && !self.env_write
    }

    /// One-token diagnostic label: `wf`, `w:<fields>f/<gnames>g/<e>/<v>`,
    /// or `top:<why>`.
    pub fn label(&self) -> String {
        if self.top {
            format!("top:{}", self.top_why.as_deref().unwrap_or("?"))
        } else if self.is_write_free() {
            "wf".to_string()
        } else {
            format!(
                "w:{}f/{}g/{}/{}",
                self.field_writes.len(),
                self.gname_writes.len(),
                u8::from(self.elems_write),
                u8::from(self.env_write),
            )
        }
    }
}

/// Everything the analysis tells the translator: the whole contract
/// between `likelier` and `wasm`, and the only channel between them.
///
/// Every field is a *prediction*. The translator emits each one behind a
/// runtime guard with a generic fallback, so a wrong entry costs a failed
/// guard and a slower path, never a wrong answer -- which is what lets the
/// analysis be as aggressive as it likes.
/// The slot half of a `local_restamps` entry names a formal (the low bits
/// its index) when this bit is set, else a local.
pub const RESTAMP_FORMAL: u32 = 1 << 31;

/// A builtin an apply-form site forwards to (see `LikelyFacts::apply_natives`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ApplyNative {
    HasOwnProperty,
}

#[derive(Default)]
pub struct LikelyFacts {
    /// The compilation's string table, handed on to the translator: every
    /// `NameId` in the tables below resolves through it, and the emitted
    /// atom table is built on top of it rather than as a second copy.
    pub names: Names,
    /// Per-property-site resolved accessor: (target
    /// getter/setter script, kind 0 = get / 1 = set). Produced from the
    /// modeled `Object.defineProperty` class accessor table at sites
    /// whose receivers agree on one class. Consumed by the accessor-call
    /// arm (a runtime-primed (shape, atom) cache guards receiver and
    /// callee identity, so a wrong likely only misses to the IC path).
    pub accessor_sites: HashMap<Site, (ScriptId, u8)>,
    /// Names registered as accessors on any class: sites reading/writing
    /// these names whose receivers did not classify still emit the
    /// (fully dynamically guarded) accessor arm, without a static target.
    pub accessor_names: HashSet<NameId>,
    /// How each call site resolved (see [`CallResolution`]). Absent = the
    /// site did not resolve and takes the generic dispatch.
    pub call_sites: HashMap<Site, CallResolution>,
    /// Every syntactic apply/call-shaped call site (the callee node is an
    /// `.apply`/`.call` property read), resolved or not, with the form it
    /// spells. The apply-forward flow check keys on this -- the forward
    /// helper reads the real callee/target from the stack at runtime, so
    /// compile-time target resolution is not required for soundness.
    pub apply_sites: HashMap<Site, CallForm>,
    /// The single scripted target of an apply/call-shaped site, where the
    /// receiver of the `.apply`/`.call` resolved mono. The forward helper
    /// does not need this -- it reads the real target off the stack -- but a
    /// site that wants to call the target DIRECTLY does, and the direct call
    /// is what would give an apply-forward site a truthful effect word
    /// instead of the opaque helper's saturation.
    pub apply_targets: HashMap<Site, ScriptId>,
    /// `apply_targets` resolved per entry: (the call/construct site that
    /// entered the apply site's body, the apply site) -> the single target
    /// under that entry. A shared wrapper's `this.initialize.apply` is
    /// multi at the body and mono per `new` site; a splice of the body at
    /// that site reads its target here.
    pub apply_targets_in: HashMap<(Site, Site), ScriptId>,
    /// Every scripted target an apply/call-shaped site is known to reach:
    /// the body-level set where it stayed within bound, plus every
    /// per-entry resolution. Sorted. A site with no single target still
    /// calls each of these directly, by callee identity.
    pub apply_target_sets: HashMap<Site, Vec<ScriptId>>,
    /// Per apply-form site: the builtin its mono target is, for the
    /// codegen's native forward arms (`hasOwnProperty.call(o, k)`).
    /// Guarded by callee identity at runtime, so a wrong resolution is a
    /// missed fast path.
    pub apply_natives: HashMap<Site, ApplyNative>,
    /// Per-script transitive effect summaries (see [`EffectSummary`]).
    /// Every script the source carries has an entry.
    pub script_effects: HashMap<ScriptId, EffectSummary>,
    /// Method script -> (lo key, hi key) of the predicted `this` class:
    /// lo == hi = an exact ctor-class home (the narrowed subclass view);
    /// lo < hi = a predictor-class home consumed with a range guard and
    /// the group table.
    pub this_layouts: HashMap<ScriptId, (LayoutKey, LayoutKey)>,
    /// Predicted instance layout per class, keyed by layout key.
    pub classes: HashMap<LayoutKey, ClassFacts>,
    /// Array element claims, keyed by the array class-region root (the
    /// union-find root, so sibling alloc sites that flowed together share
    /// one claim): root -> (element type, element range). Arrays carry the same
    /// stamp word objects do; the claim covers a non-hole element's value,
    /// which is all a reader ever sees -- the dense read hole-checks before
    /// the value reaches any consumer.
    pub array_elem_claims: HashMap<RegionRoot, (Prims, ValueRange)>,
    /// Array allocation site its class-region root: where
    /// a compiled allocation stamps the fresh array.
    pub array_alloc_sites: HashMap<Site, RegionRoot>,
    /// Element site the predicted receiver's class-region
    /// root, for reads (the fold) and writes (the maintenance duty).
    pub array_elem_recv: HashMap<Site, RegionRoot>,
    /// Per-property-site likely receiver: (lo key, hi
    /// key, predicted slot, mask). lo == hi = exact ctor-class fact
    /// (narrowed `this`); lo < hi = range fact over the group table OR a
    /// per-name sub-range of agreeing contiguous member keys. The mask is
    /// computed at emission (per-ctor for exact, all-members-claim for
    /// ranges) because sub-range los are not group los -- consumers must
    /// not recompute it from group tables.
    pub prop_sites: HashMap<Site, (LayoutKey, LayoutKey, SlotIndex, Claim)>,
    /// Per-element-read-site likely value prims: at a GetElem,
    /// the receiver class's merged `[]` element node prim mask, exported
    /// only when purely numeric (Int32|Double). Consumed by loop versioning
    /// as a per-read value-tag-guarded assumption (a wrong likely deopts
    /// that read to the generic loop copy; never correctness).
    pub elem_sites: HashMap<Site, Claim>,
    /// Per-element-WRITE-site: the receiver array region's merged `[]`
    /// element node prim mask (the mask the region's reads claim),
    /// exported only when purely numeric. A store site whose mask admits
    /// Double may box an integral double as a double: every read of that
    /// node already admits the tag, so the int32 canonicalisation buys
    /// nothing there.
    pub elem_write_sites: HashMap<Site, Claim>,
    /// Per-script likely this/arg types (the guard-at-defs family: the Opt
    /// track is kept aligned with the likelier's predictions by guarding at
    /// defs whose produced type does not already imply the claim):
    /// (script, arg index) -> claim. Bits 0-5 = a purely-numeric PRIM_* mask;
    /// 0x8000 = object-only (no primitive component). Joined over live
    /// analysis ctxs; P_UNKNOWN or mixed prim/object evidence emits no
    /// claim. Consumed at GetArg as a one-tag-test guard whose positive
    /// side continues with the fact; a def whose type already implies
    /// the claim takes no guard and keeps the tighter type.
    pub arg_types: HashMap<(ScriptId, ArgIndex), Claim>,
    /// Per-formal VALUE class range (emitted layout-key space), the
    /// advisory sibling of `arg_types`: the entry ctx carries it as a
    /// `likely_cls` hint, unguarded; the first use that needs the identity
    /// guards it (the lazy tier). Index convention follows `arg_types`
    /// (1 + formal; `this` resolves through `this_layouts` instead).
    pub arg_cls: HashMap<(ScriptId, ArgIndex), (LayoutKey, LayoutKey)>,
    /// Per-call-site likely result types (guard-at-defs, the call
    /// family): numeric mask or 0x8000 object-only,
    /// from the call's ret cell joined over live ctxs. Object claims
    /// only under receiver demand (the result feeds a property/element
    /// access); consumed at the generic call continuation as a
    /// one-tag-test ladder.
    pub call_types: HashMap<Site, Claim>,
    /// Per-GetAliasedVar-site likely value prims: the
    /// resolved (scope, slot) cell's prim mask, exported under the same
    /// purely-numeric gate as `elem_sites`. Env slots are written through
    /// SetAliasedVar barriers by any closure sharing the scope, so the
    /// fact is likely only -- consumed as a tag-guarded arm-order hint.
    pub aliased_sites: HashMap<Site, Claim>,
    /// Per-global-name likely value types (the guard-at-defs family
    /// applied to the global store): name -> claim, projected from the
    /// engine's context-free GName cells -- the snapshot global's initial
    /// value joined with every statically-seen SetGName write. Numeric
    /// claims are demand-free; object claims only under element-receiver
    /// demand (the arg_types discipline). Likely, never proof: writes the
    /// scan cannot see (eval'd scripts, computed-key global stores) make
    /// the consumer's per-read tag guard miss, never a miscompile -- so
    /// unlike the fused-literal machinery this table needs no fuses.
    pub gname_types: HashMap<NameId, Claim>,
    /// Arith sites whose RESULT cell is fractional-reachable (double
    /// evidence at range Top -- the i53 law's contrapositive): a real
    /// runtime double population flows through the op, so its
    /// both-number f64 arm keeps the Opt track (the numeric-category
    /// policy). Sites absent here keep the track step: their f64 arm is
    /// cold, and letting its numeric result join the successor would
    /// degrade a pure-int32 chain's facts.
    pub fractional_arith_sites: HashSet<Site>,
    /// Arith (`+`) sites whose result cell carries string evidence: a real
    /// string population flows through the op, so the both-string concat
    /// arm keeps the Opt track (the string analog of the numeric-category
    /// policy). Sites absent here keep the track step for the same
    /// join-degradation reason as `fractional_arith_sites`.
    pub string_arith_sites: HashSet<Site>,
    /// Per-element-site likely typed-array kind: at a GetElem/SetElem,
    /// the receiver class's element kind when it settled on a single one. Consumed as a guarded-monomorphic inline
    /// read/store arm (clasp guard + kind-specific access); a wrong prediction
    /// just misses to the generic helper, never a correctness issue.
    pub ta_elem_sites: HashMap<Site, TaKind>,
    /// Elem sites that get the polymorphic TA arm (shared in-module helper):
    /// every elem site in a bundle that references a typed-array constructor
    /// (natives like `subarray()` hand TAs to sites the class analysis tags
    /// non-TA, so per-class gating loses them); Empty for TA-free bundles,
    /// where the arm's cold call would lengthen hot dense-loop live ranges.
    pub elem_poly_sites: HashSet<Site>,
    /// Per-read-site VALUE class range, in the emitted layout-key space:
    /// the object this site loads is likely of a class in [lo, hi]. The
    /// consumer attaches it as an ADVISORY `likely_cls` on the result --
    /// unchecked until a use synthesizes a class-fact row from it, whose
    /// own guard proves (or misses) it lazily.
    pub field_cls_sites: HashMap<Site, (LayoutKey, LayoutKey)>,
    /// Per-field-read-site likely value prims: GetProp the
    /// receiver class's field node prim mask, exported under the same
    /// purely-numeric gate as `elem_sites` and consumed the same way (a
    /// per-read value-tag-guarded assumption inside versioned loops).
    pub field_sites: HashMap<Site, Claim>,
    /// Diagnostic: classes discovered / constraints collected.
    pub n_classes: usize,
    pub n_cons: usize,
    /// Scripts homed as this-forwarded delegates of a class (the
    /// static-init idiom): their `this.f = v` stores are instance inits,
    /// so the layout-set slow tail carries the add-transition arm there
    /// (and only there -- it is pure bloat on method overwrite tails).
    pub deleg_inits: HashSet<ScriptId>,
    /// Ctor-return stamp sites: constructor script -> its own ctor-class
    /// key (contiguous within the predictor group).
    pub ctor_stamps: HashMap<ScriptId, LayoutKey>,
    /// Object-literal stamp sites: the `NewInit`/`NewObject` site -> its
    /// lit-row layout key. The rows always existed in the key space (and
    /// so in the runtime layout tables and the per-site claims); this is
    /// the site mapping that lets the allocation actually STAMP, so the
    /// literal-born population stops being the "receiver never stamped"
    /// class-fact miss bucket.
    pub lit_stamps: HashMap<Site, LayoutKey>,
    /// Construct-site allocation sizing: ctor script -> the full layout
    /// row length (two-phase ctors count the delegate-assigned suffix).
    /// Consumed as the `new`-site nSlots prediction so every predicted
    /// field lands in a fixed slot regardless of the engine's ctor-body
    /// property-count estimate.
    pub ctor_nslots: HashMap<ScriptId, u32>,
    /// Predictor-group tables, keyed by the group's LO key: (universal
    /// prefix field names, per-slot masks claimed by every member).
    /// Consumed by range facts (lo < hi).
    pub group_tables: HashMap<LayoutKey, (Vec<NameId>, Vec<Prims>)>,
    /// Shared-generated-ctor construct sites (the prototype.js
    /// `Class.create()` idiom: many classes, one ctor script, so
    /// script-keyed stamps cannot key them): the layout
    /// key of the class the site's snapshot-resolved callee object
    /// constructs. Derived concretely (callee def-chain -> function
    /// object -> its `.prototype` -> the init delegate the ctor's
    /// `this.<init>.apply` dispatch reaches there); the init delegate
    /// enters `deleg_restamps`/`deleg_inits`/`this_layouts` so the row
    /// stamps and its adds ride the static checks. Consumed by the
    /// construct-site alloc word/size in place of `ctor_stamps`/
    /// `ctor_nslots` when those (script-keyed) miss.
    pub construct_site_keys: HashMap<Site, LayoutKey>,
    /// Two-phase construction re-stamp sites: init-delegate script -> the
    /// full layout key of the two-phase ctor it completes. At each return
    /// of the delegate, an object `this` whose live shape equals the full
    /// row's validated shape is (re-)stamped with the full key -- the
    /// prefix-stamped (or cleared) word from the ctor-exit phase advances
    /// to the full id, so full-only field guards start hitting.
    pub deleg_restamps: HashMap<ScriptId, LayoutKey>,
    /// Formal-receiver fill scripts: script -> (formal index, full layout
    /// key). The `this`-delegate rule's sibling for the `nbi()`-then-fill
    /// idiom, where a fresh prefix-stamped object is completed through an
    /// ARGUMENT (crypto's `multiplyTo(a, r)` writing `r.t`/`r.s`): the
    /// script's own formal-receiver writes contribute a suffix name of the
    /// two-phase full row, so each return re-stamps the formal's object to
    /// the full key under the same validated-shape gates. Without this the
    /// population never advances and every full-key read guard misses.
    pub arg_restamps: HashMap<ScriptId, (u32, LayoutKey)>,
    /// Post-construction fill sites: (script, pc of the last add) ->
    /// (local index, full layout key). The local-receiver sibling of
    /// `arg_restamps`: instances filled after construction by a
    /// straight-line add sequence on a local (box2d's `ccp = c.points[j]`)
    /// are restamped to the full key after the last add.
    pub local_restamps: HashMap<Site, (u32, LayoutKey)>,
    /// Name-keyed type facts (the type dimension, independent of the slot
    /// dimension): (lo key, hi key, mask) for property
    /// read/write sites whose receiver class(es) uniformly claim a numeric
    /// value mask for the accessed name -- including names absent from
    /// every layout (post-init fields) and classes whose slot prediction
    /// never validates. Consumed by the types-only ladder arm (IC-served
    /// load, typed push) and the store-side name-keyed conform mask.
    pub typed_sites: HashMap<Site, (LayoutKey, LayoutKey, Claim)>,
}

impl LikelyFacts {
    /// The scripted callees of a site: empty when it did not resolve, or
    /// resolved to a native instead.
    pub fn scripted_targets(&self, site: Site) -> &[ScriptId] {
        match self.call_sites.get(&site) {
            Some(CallResolution::Scripted(t)) => t,
            _ => &[],
        }
    }

    /// Whether the site resolved to a modeled native with an inline arm.
    pub fn is_native_call(&self, site: Site) -> bool {
        matches!(self.call_sites.get(&site), Some(CallResolution::Native))
    }

    /// Every site that resolved to scripted callees, with them.
    pub fn scripted_call_sites(&self) -> impl Iterator<Item = (Site, &[ScriptId])> {
        self.call_sites.iter().filter_map(|(&site, r)| match r {
            CallResolution::Scripted(t) => Some((site, t.as_slice())),
            CallResolution::Native => None,
        })
    }
}
