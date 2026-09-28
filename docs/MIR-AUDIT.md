# MIR design spec vs implementation audit

Which elements of the design (docs/MIR.md) were never built, or built only
in part, as distinct from deliberate divergences that later decisions
recorded. Companion to docs/MIR-PARITY.md, which audits MIR against the
legacy tier instead. Audited 2026-09-28 at `4e84435`; file:line references
will drift. Items are struck from the ranked table as they land, with the
commit.


Spec: `docs/MIR.md` (rev 6, with §12 decision log and §13 plan, through M5h).
Code: `compiler/src/mir/`, `compiler/src/wasm/mir/`, and the runtime where needed. Line numbers are at `4e84435`.

Method: for each opcode, count `Opcode::X` constructions in `build.rs`, `inline.rs` and `opt.rs`, and its `Opcode::X` match arms in `lower.rs`. `lower.rs:3039` declines any op without an arm ("is not lowered yet"). Type-lattice components were checked the same way, by searching for their construction in the builder and the inliner. Commit messages tell a deliberate change from an omission.

**The constructing refinement is in the type lattice:**
- `LayoutState::{Published, Prefix(n), Constructing(n)}`, with `le`/`join` (`types.rs:370-410`);
- `KillSet::CONSTRUCTING`, and weakening from Constructing to Prefix (`types.rs:800, 885, 953`);
- typing rules for `init_field`, `publish_layout` and `new_object K` → `Obj{Plain, K constructing(0)}` (`ops.rs:1368, 1406, 1431`);
- effect summaries (`ops.rs:1814-1822`) and unit tests.

What is missing is any *producer*: the builder never emits these ops, nothing produces a `Constructing`/`Prefix` state, and the lowering has no arms for them. The finding is "defined and typed, never built or lowered", not "absent from the lattice".

---

## Ranked summary: NEVER BUILT and PARTIAL

| # | Item (§) | Class | Importance | One-line gist |
|---|---|---|---|---|
| 1 | Array/string `length` ops: `length.array`, `length.string` (§7) | NEVER BUILT | high | `a.length` on a proven `Native`/array is a generic `js.getprop` (inline arm only in the lowering). Its effects are Unknown writes plus may-run-JS, so any loop that reads `a.length` blocks `licm`, `cse_loads` and fuse folding. |
| 2 | Globals as `load_gname`/`store_gname` with `Binding` facts and `check.binding` (§3, §7) | NEVER BUILT | high | Global reads and writes are `js.getname`/`js.setname`, generic effects with inline arms in the lowering. The optimizer cannot CSE or hoist a global read, and every global read in a loop is a JS-running fence. The `bindings` table is never populated. |
| 3 | Constructors: the `Obj{constructing K,n}` producer, `init_field`, `publish_layout`, `new_object K` (§2.3, §7) | NEVER BUILT (lattice and typing done) | high | Construction is `create_this`, generic `js.setprop` with inline add-transition replay, `ctor.stamp`, `restamp` and `stamp.fresh`. `this` in a constructor has no layout type, so its field adds are generic, JS-running ops. Class constructors are also declined outright (`build.rs:567`). |
| 4 | `new_object K` / `new_array n` for literals (§7) | NEVER BUILT (divergent substitute) | med-high | `{}` and `[..]` are `js.rt NewObject/NewArray/InitProp/InitElem` (`build.rs:4710-4769`). Their effects are generic (kill ALL, Unknown writes, may-run-JS), even though the lowering allocates inline. The result is `Val{object}` with no kind or layout. |
| 5 | Guard hoisting to the preheader (§10.2) | PARTIAL | med-high | No MIR pass hoists guards: `opt::licm` skips terminators. The builder hoists only `Native`/`Ta(kind)` receiver guards (`HOIST_NATIVE`, `build.rs:2756`). Layout guards and `check.fuse` in loops are never hoisted, and the builder's `Obj ⊔ Val → Val` join at loop headers means a first-use `guard.layout` inside a loop stays there. |
| 6 | LICM / memory optimization over descriptors (§6, §10.5) | PARTIAL | med-high | Built: `licm` for pure non-terminators, and `cse_loads` (field RLE plus store→load forwarding on clean edges). Not built: DSE, element/env/global forwarding, and keeping memory knowledge across `ok_clean` (every generic op clears it). `load_field` is a terminator, so an invariant field load is never hoisted out of a loop. Field kills ignore the key range (`opt.rs`, `Field{keys: None}`). |
| 7 | Prediction witnesses (§4.5, §8) | PARTIAL | medium | Witnesses exist, are printed and parsed, and the validator enforces coverage (`verify.rs:740`). But the builder attaches only `KillPattern::ALL` ("may kill anything") at its 3 sites (`build.rs:1570, 2174, 4768`, `inline.rs:325`), and never draws on likelier's effect summaries. The predicted-or-dynamic rule is therefore vacuous, and a "forbidden kill" (§4.5 case 2) can never be caught. |
| 8 | Effect-flags word threading (§6, M5 "Accurate flags words") | NEVER BUILT | medium | Every MIR body returns `FLAGS_ALL` (`lower.rs:617-621`). `FlagsEffect` is computed per op (`ops.rs`) but never consumed. Clean/dirty inside MIR uses the stamp epoch instead (`clean_or_dirty`, `lower.rs:1643`), which is a deliberate and working substitute for *that* part. |
| 9 | `elements_ptr` / `Raw` values (§2.1, §4.4, §7) | NEVER BUILT | medium | No `Raw`-typed value is ever produced. `load_elem`/`store_elem`/`load_ta` recompute the elements/data pointer inside the lowering, so an interior pointer cannot be hoisted out of a loop. The validator's Raw-across-GC check (`verify.rs:808`) is correct but never exercised outside unit tests. |
| 10 | Alias regions from array class regions (§6) | PARTIAL | medium | `Region::Elements(Some(root))` needs `Layout.elements`, which the builder never sets (only in tests). Every element access is therefore the `Elements(*)` wildcard. The module's `regions` entity table and `intern_region` are unused: regions are inline values, not table entities. |
| 11 | Object component of field claims: kind, function script, singleton (§4.3, §4.6 pt. 1/4) | PARTIAL (acknowledged) | medium | Field claims are `Val(tags)` only (`build.rs:379 claim_ty`). There is no `Obj{kind Plain}` / `Function(s)` from a load, so no guard-free `this.cb(x)` direct calls through fields. The §4.6 Status says "Not yet". |
| 12 | Numeric optimizations (§10.6) | PARTIAL | medium | Built: `.wrap` for Add/Sub under truncating demand (builder, not Mul); int32 induction variables as `I32` block params; the -0 test only on a zero product (lowering). Not built: range-based overflow removal. The builder's `I32` is always `I32_TOP`, so `IRange`/`NumInfo` refinements exist only on constants, `length.ta` and `i32.ushr`. `int.*` arithmetic and `i32.to_int` are lowered but never built. |
| 13 | `str.char_code_at`, `Str`-typed values (§7, §2.1) | NEVER BUILT (substitute in lowering) | medium | `charCodeAt`/`charAt` are call arms in the lowering (M5g), with generic call effects. `unbox.str`/`guard.unbox.str` are never built, so no string value is ever `Str`, except `const.str`. |
| 14 | Ghost facts consumed as operands (§3) | PARTIAL | low-med | `check.fuse` and `check.native` produce `Fact`s (`build.rs:1948, 1356`), but no op takes a fact operand: the fused literal is a bare constant and `math` takes no fact. The validator therefore cannot check that a fence doesn't fall between a check and its reliant use. Today they are adjacent by construction. |
| 15 | `const.obj`, `guard.singleton`, snapshot-object table (§1, §2.1, §7) | NEVER BUILT | low-med | Typed (`ops.rs:833, 922`), and `opt::is_guard` knows `GuardSingleton`, but nothing builds or lowers them. `snap_objs` is never populated (`inline.rs:169` asserts it is empty). `ObjInfo.singleton` is never set. |
| 16 | `call_direct`, `call_native` (§7) | NEVER BUILT (substitute) | low | The direct and likely-callee arms are inside `call`'s lowering (attachment `targets`, `DIRECT_CALLS`), and native routing is `NATIVE_ROUTE`. The effects would be the same, so little is lost. |
| 17 | Kill patterns restricted by key range (§4.1, §4.5) | PARTIAL | low | `KillPattern.keys` exists, but `effects()` only ever emits `of(set)` or `ALL`, with no key restriction. Every fence kills every layout claim. |
| 18 | §10.1 extras: "type disproves → jump to fail, warn"; dead-fail-block removal; sharing identical exits | NEVER BUILT | low | `fold_guards` folds only when proven true. Exits are shared per pc by the builder, not by a pass. |
| 19 | §10 test deliverables: textual before/after tests plus guard-count e2e tests | PARTIAL | low | One optimizer unit test (`tests/mod.rs:584 fold_guards_across_a_fence`), plus `fence_rejoin.mir`. No tests for `licm` or `cse_loads`. The jit-tests (`mir-*.js`) are functional, and none asserts a guard count. |
| 20 | §8 builder assertion "OPT state ≥ prediction at every boundary" | NEVER BUILT | low | There is no per-pc assertion. Guard-at-defs is applied at formals, generic results and field loads only. |
| 21 | §4.3 "LoadField/StoreField attachments carry the slot and IC cell"; §1 IC/call-cell attachments | PARTIAL (divergent) | low | `Attachment.{ic_cell, call_cell, slot}` are always `None` (`build.rs:1142`). The lowering allocates cells itself (`lower.rs:5417`) and finds slots from the module layout. |
| 22 | Text format covers inlining (§1 printer/parser) | PARTIAL | low | The parser has no `exit.inline` template, and neither side prints or parses `inline_frames`/`inst_frame`. Inlined bodies (all real ones since M5c) do not round-trip. |
| 23 | `W32`/`W64` machine-word values (§2.1) | NEVER BUILT | low | Stamp words, lengths and similar exist only inside the lowering. |

---

## Detailed findings by section

### §1 IR structure

- **Module tables.**
  - `layouts`, `atoms`, `fuses`, `natives` and `script_addrs` are populated.
  - `snap_objs` and `bindings` exist (`module.rs`) but the builder never fills them. `inline.rs:169` rejects a callee that has any, so they are dead. **NEVER BUILT** (low-med): it goes with `const.obj`/`guard.singleton`/`check.binding`.
  - The `regions` table (`RegionId`, `intern_region`) is never referenced outside `module.rs`/`entity.rs`. Effects use inline `Region` values. **DELIBERATE-ish / low**: there is no commit note, and it is functionally equivalent.
- **Per-op attachments** (`func.rs:151`).
  - `ic_cell`, `call_cell` and `slot` are never set (always `None`, `build.rs:1142`). The lowering allocates call cells itself (`lower.rs:5417 next_call_cell`) and reads slots from the layout table.
  - What is used: `site` (diagnostics), `targets`, `field_types` (the typed-site field mask, M5b follow-up `4e84435`) and `ta_poly`.
  - **PARTIAL / divergent, low.** The spirit ("nothing downstream reads LikelyFacts") holds: `lower.rs` never touches `ctx.facts`.
- **Printer/parser.** Both exist, with round-trip tests (`tests/mod.rs:60-120`). They do not cover `exit.inline` (the parser's `template()` has no `ExitInline`, and `print.rs` has no frame output) or per-instruction inline frames. **PARTIAL, low.**
- **Validator** (`verify.rs`). All listed checks are implemented, and they run on every compile (`wasm/mir/mod.rs:84`):
  - SSA dominance with a virtual root (`dominance`, CHK idoms);
  - edge arity and subtyping (`types`, around l.562-600);
  - operand types (`signature`);
  - fences at the op and on edges, with the throw-block exemption from M0 (`fences`, `fence_edges`, `is_throw_block`);
  - the predicted-or-dynamic rule (`verify.rs:740`);
  - Raw across may-GC (`raw_across_gc`);
  - exit and root arity against the frame (`boundary`);
  - declared loops (`loops`).

  Nothing to report on the validator itself. The weakness is in the witness *inputs*: see §4.5.

### §2 Type lattice

`types.rs` implements every type and refinement in §2.1: `Val(VSet)`, `I32/Int(IRange)`, `F64(NumInfo)`, `Bool`, `Obj(ObjInfo{kind, singleton, layout{keys, types, state}})`, `Str(StrInfo{atom})`, `Raw(RawKind)`, `W32/W64` and `Fact(FactKind)`. `TagSet` has `magic` (M0b). **What is actually produced** is a small subset:

| Component | Produced by | Status |
|---|---|---|
| `ObjKind::Native`, `TypedArray(k)` | `guard.kind` (builder `Ty::Native`/`Ta`) | built |
| `ObjKind::Function(Some(s))` | `guard.script` (inline guard, known closures, entry callee) | built |
| `ObjKind::Env` | `env.*` (`build.rs:1967`) | built |
| `ObjKind::Plain/Array/Arguments` | nothing | **NEVER BUILT** (low-med): arrays are `Native`; literals are `Val{object}` |
| `ObjInfo.singleton` | nothing (`const.obj`/`guard.singleton` never built) | **NEVER BUILT** |
| `LayoutClaim{Published}` | `guard.layout`, the builder's `Ty::Obj` | built |
| `LayoutState::Constructing/Prefix` | nothing | **NEVER BUILT** (see §2.3) |
| `NumInfo`/`IRange` refinements | constants, `length.ta` (`build.rs:4330`), `i32.ushr` (`build.rs:3815`) | **PARTIAL**: the builder's `Ty::I32` maps to `I32_TOP` (`build.rs:92`), and field claims carry no ranges |
| `Str(StrInfo)` | `const.str` only | **PARTIAL**: `unbox.str`/`guard.unbox.str` are never built |
| `Int` | `i32.ushr` result | **PARTIAL**: `i32.to_int`/`int.*` are lowered (`lower.rs:1817-1838`) but never built |
| `Raw` | nothing (`elements_ptr` never built) | **NEVER BUILT** |
| `W32/W64` | nothing | **NEVER BUILT** (low) |
| `Fact(Fuse)`, `Fact(NativeIntact)` | `check.fuse`, `check.native` | built (but see §3) |
| `Fact(Binding)` | nothing | **NEVER BUILT** |

**Architectural note (not a finding per se).** The builder has its own coarse slot domain `Ty` (`build.rs:49-80`): `I32/F64/Bool/Val(tags)/Obj(keys,types)/ObjHint/Native/Ta/Fn/Dead`. Block-entry types come from a fixpoint over that domain, and MIR types are *declared* from `Ty::mir()`. So the MIR lattice's richer refinements can never reach block params. Two examples: `Ty::Fn(s)` maps to `val{object}`, losing the script, and `Ty::I32` maps to `I32_TOP`. This is the root cause of items 11, 12 and 15.

#### §2.3 Constructors: **NEVER BUILT** (lattice and typing present), high

- **What exists:** the lattice as described in the correction above, plus the M0 decision "`new_object K` yields `Obj{Plain, K constructing(0)}`" (`ops.rs:1431`). The `init_field` rule advances n→n+1 (`ops.rs:1368`), and `publish_layout` has its CONSTRUCTING kill (`ops.rs:1406, 1819`). `inline.rs:69` special-cases `PublishLayout` witnesses.
- **What is missing:** no builder or inliner constructs `InitField`, `PublishLayout` or `NewObject`, and `lower.rs` has no arm for any of them.
- **What replaced it** (§13 M4b/M5d/M5e/M5h, commits `cf83149`, `0c064ea`, `7521f93`, `f6e4207`):
  - `create_this` (generic effects);
  - constructor field adds as `js.setprop` with the set IC's add-transition row replayed inline (M5d "Property ICs", M5e "Stores and stamps");
  - `ctor.stamp` at every return, with `restamp` and `stamp.fresh` (M5h).
- **Consequences.**
  - Inside a constructor, `this` has no layout type, so its adds are generic JS-running ops (Unknown writes, kill ALL) with clean/dirty edges.
  - Class constructors are declined entirely (`build.rs:567`), which §11 does not list.
- §13 M5 still lists "Constructors (`init_field`/`publish_layout`)" as remaining. So this is an omission, not a decision, although the ctor-stamp machinery is a deliberate interim.

### §3 Global facts (ghost values)

- **`Fuse(id)`**: `check.fuse` is built for fused `GetGName` literals (`build.rs:1948`) and folded by `fold_guards`, whose availability dies at may-run-JS ops (`opt.rs:393`, commit `2f7c5db`). **But** the fact is never consumed: the fused literal is an ordinary constant, and there is no `load_gname.fused`. **PARTIAL** (low-med). Soundness today rests on the check and the constant being adjacent.
- **`Binding(id)`**, `check.binding`, `load_gname`, `store_gname`: **NEVER BUILT** (high).
  - Global reads and writes are `js.getname`/`js.bindgname`/`js.setname` (`build.rs:4303-4318`). The value-fuse, slot-row and resolve arms are inline in the lowering (§13 M4b "Inline global reads", M5d "Syntactic global writes are inline").
  - Their effect summary is `Effects::generic` (`ops.rs:1760`), so a global read is opaque to `licm`, `cse_loads` and fuse folding, and every loop that reads a global contains a may-run-JS op.
  - §13 M5 lists "syntactic bindings (`gcell`) remain", so this is not a recorded decision.
- **`NativeIntact`**: `check.native` is built for typed Math (`build.rs:1356`) and lowered. The fact is not consumed by `math`. **PARTIAL** (low).

### §4 Invalidation, weakening, and GC

#### §4.1 Fences
- Built: kill patterns are computed per op (`ops.rs effects`, `kill_site`), and the validator enforces them.
- **PARTIAL (low):** `KillPattern.keys` (key-range-restricted kills) is never used by `effects()`. Every fence kills `ALL` or a single set class. Mostly moot under "facts fixed, a kill exits".

#### §4.2 Weakening / clean-dirty rejoin
- `weaken` and fence-edge params are built (`fence_params`, `build.rs:1159`; `dirty_exit_as` weakens `Obj` params).
- **DELIBERATE DIVERGENCE:** the §8 default "re-guard each weakened value up to the clean edge's type and rejoin" (and §12 Rev 5 "`ok_dirty` re-guarding stays eager") was replaced:
  - `ok_dirty` exits to baseline at the next pc (`dirty_exit`, `build.rs:2284-2350`, `DIRTY_EXITS`/`KEEP_ON_CLEAN`);
  - where no exit pc exists, the slot is demoted to `ObjHint` and lazily re-guarded at the next use.
- Evidence: commit `f6e4207` ("facts are fixed, a kill exits"), `29a6e0f`, the user's MIR design rules, and §13 M5e ("Dirty IC arms exit").
- **Doc drift:** §4.2, §8 and §12 Rev 5 still describe eager re-guard-and-rejoin.

#### §4.3 Layout claims, stamp bits, ICs
- `guard.layout {types}`, `load_field` and `store_field` are built.
- **DELIBERATE DIVERGENCE:** "`SLOTS` is never in a type; each op tests it locally, IC arm stays in OPT".
  - Now `guard.layout` also requires SLOTS (`GUARD_SLOTS`, `lower.rs:161`; commit `f5f4045` "layout guards prove SLOTS").
  - Typed field IC arms exit rather than rejoin (M5e).
  - The class-key miss falls back to the IC instead of exiting (M5d).
  - These are recorded in §13 and commits, but not in §4.3 or §12.
- **PARTIAL (medium):** "Loads feed the predicted type out (`Val{int32,double}` with a range, a string, an object of a known kind)". Claims are tags only (`claim_ty`, `build.rs:379`), with no ranges, `Str`, or object kind. RANGES is not relied on (M5e: "no MIR claim rests on it"). This is deliberate for ranges; the object kind is acknowledged in the §4.6 Status as "Not yet".

#### §4.4 GC
- Built as designed (commit `a2a6b69`):
  - home slots with greedy coloring (`lower.rs:1036-1040`);
  - location tracking, lazy reload, per-edge reconciliation;
  - dead-slot clearing (`lower.rs:1727`);
  - initialization of the rooting area (`init_root_area`).
- The `Raw` rules are unexercised because no `Raw` values exist (see §7 `elements_ptr`).
- "Locals never written through" matches, via the retaining-store scheme (`567ee90`).

#### §4.5 Prediction witnesses: **PARTIAL**, medium
- `Witness{may_kill}` side table (`func.rs:180`), printed and parsed (`!pred{…}`), and checked for every `Op`/`OkEdge` static kill (`verify.rs:740-760`).
- **But every witness the builder or inliner attaches is `KillPattern::ALL`**:
  - `build.rs:1570` (`args.object`), `2174` (`js_static`), `4768` (`js.throw`);
  - `inline.rs:325` (`exit.inline`).
- Nothing reads likelier's effect summaries, so the "forbidden kill" case can never fire in real code. Only the unit test `predictions` (`tests/mod.rs:395`) exercises it.
- Most kills are now on dirty edges, which need no witness. The only static-kill producers left are `js.throw` and allocations with `kill NONE`, so the rule currently guards almost nothing.

#### §4.6 TYPES
- M5b is built as its Status block says (commits `594fd9e`, `4e84435`, `runtime/NightObjectWord.h:78` `kStoreClearMask = RANGES|TYPES`).
- **DELIBERATE DIVERGENCE** (recorded in the Status): SLOTS is not cleared by generic stores.
- **PARTIAL** (acknowledged "Not yet"): the object component (kind/script/singleton) and guard-free direct calls through fields (§4.6 pt. 4, "`this.cb(x)` with no guard").
- **UNCLEAR:** the legacy-OPT transition hazard (pt. 3) and GEN's unconditional choke. The Status says "Legacy keeps its numeric masks" and `594fd9e` says "bbv's keep rule counts any claim". bbv was not audited. It matters only if bbv- and MIR-compiled code share objects in one run.
- **Not found:** the M5b gate's "field-claim coverage counts" and the demotion census as a MIR deliverable (low).

### §5 Boundary: exits, onramps, throws, reducibility, inlining

- **§5.1.**
  - Built: exits with a per-shape hub (`0147796`), liveness pruning, the resume rule and the `ARGC_RESUME_BIT` path.
  - **DELIBERATE DIVERGENCE / doc drift:** the "frame is written through (amended 2026-09-27)" paragraph is superseded. Commit `a2a6b69` says "Locals are no longer written through … exits write them", and `567ee90` adds retaining stores. `FrameStore` is now a retaining store (`lower.rs:1764-1774`), written through only for mapped formals. §5.1 and §5.5 ("Write-through keeps K's frame…") still describe write-through; `lower.rs:26-28` matches the code.
  - "Reserved extensions … validator rejects both": the parent-frame chain was superseded by §5.5's inline frames. Fine.
- **§5.2.** Built:
  - onramp roots that guard to the header types, including `Obj` layouts (`build.rs:3175-3260`);
  - the policy knob;
  - the entry dispatch.

  The preheader types come from the builder's fixpoint, not directly from "the prediction for that header". That is equivalent in intent; no finding.
- **§5.3.** Built, including stateless throw exits (`6632487`).
- **§5.4.** Built as designed. Step W was measured.
- **§5.5.** Built (M5c/M5h):
  - `exit.inline`, `inline.enter`, per-frame hubs;
  - the `guard.script` chain up to 4 targets.
- **§5.5 open point:** that baseline bodies of inline-eligible scripts accept a resume at every op is BASELINE's side, not audited here.

### §6 Effects and memory
- **Effect summaries** exist for every op (`ops.rs:1756`), with reads/writes, may_gc, may_run_js, may_throw, kill and flags.
- **Gaps in the summaries:**
  - `FrameStore`, `ActualArg`, `ArgsLength` and other ops fall into `_ => {}` and count as PURE. `FrameStore` has no write region, so `opt::licm` (which accepts ops with no writes and no reads) could hoist a retaining store whose operand is loop-invariant into the preheader. Write-through stores happen only at `args.object` creation, so the practical risk is only to retention timing. **UNCLEAR (low)**: worth a check.
  - `EnvStore`/`EnvLoad` use `Env(slot)`, not the spec's `Env(scope, slot)` (low).
- **Alias regions: PARTIAL** (medium). See summary item 10: `Layout.elements` is never set, so `Elements`/`ArrayLength` are always wildcards. Whether the analysis stamps every array class region is a question for likelier, not MIR.
- **Unknown-alias load vs store fences:** not distinguished in any pass. No DSE or store sinking exists, so this is moot.
- **Flags word: NEVER BUILT** (`lower.rs:617-621` always returns `FLAGS_ALL`, and `lower.rs:33-34` says "accurate flags come with M5"). §13 M5 lists it as remaining. The stamp epoch replaced its role for MIR-internal clean/dirty decisions.

### §7 Opcode set: construction and lowering census

Legend: B = built by `build.rs`/`inline.rs`, O = created by `opt.rs`, L = lowered. Only exceptions are listed.

| Opcode | B | L | Class |
|---|---|---|---|
| `const.obj` | – | – | NEVER BUILT |
| `i32.to_int` | – | ✓ | NEVER BUILT (lowered only) |
| `guard.singleton` | – (O folds) | – | NEVER BUILT |
| `check.binding` | – | – | NEVER BUILT |
| `int.{add,sub,mul}` | – | ✓ | NEVER BUILT (no interval proofs) |
| `i32.mul.wrap` | – | ✓ | PARTIAL (only Add/Sub under demand) |
| `init_field`, `publish_layout` | – | – | NEVER BUILT |
| `new_object K`, `new_array` | – | – | NEVER BUILT (→ `js.rt NewObject/NewArray`, generic) |
| `length.array`, `length.string` | – | – | NEVER BUILT (→ `js.getprop` arm, `lower.rs:2274`) |
| `elements_ptr` | – | – | NEVER BUILT |
| `str.char_code_at` | – | – | NEVER BUILT (→ call arms in lowering) |
| `load_gname`, `store_gname` | – | – | NEVER BUILT (→ `js.getname`/`js.setname`) |
| `call_direct` | – | – | NEVER BUILT (→ direct arms in `call` lowering) |
| `call_native` | – | – | NEVER BUILT (→ `NATIVE_ROUTE`; typed Math via `check.native`+`math`) |
| `unbox.str`, `guard.unbox.str` | – | ✓ | NEVER BUILT |

Everything else listed in §7 is built and lowered, including:
- `guard.kind`, `guard.script`, `f64.to_int_exact`, `to_int32`, `math`, `switch`;
- every `js.*` op, `load_elem`/`store_elem`, `load_ta`/`store_ta`, `length.ta`, `env.*`, `call`, `construct`.

Many ops beyond §7 were added and are all built and lowered, among them `js.rt`, `frame.store`, `exit.inline`, `inline.enter`, `create_this`, `ctor.stamp`, `restamp`, `stamp.fresh`, `args.*`, `apply_fwd`, `js.lambda`, `env.parent`, `js.typeof_eq` and `js.constant_strict_eq`.

### §8 JSOps to MIR
- Local-first guarding: built, then refined by M5e "proven receivers": slot types carry `Obj(keys,types)` so accesses skip guards. The method-entry `this` guard is `THIS_ENTRY_GUARD`.
- **DELIBERATE DIVERGENCE:** the `ok_dirty` default (see §4.2).
- "Explicit box/weaken upcasts before every exit": divergent by design; §5.1 now says the hubs box.
- **NEVER BUILT (low):** "The builder asserts this [OPT ≥ prediction] at every boundary". There is no such assertion.
- **PARTIAL:** "A prediction witness attached to every op with an effect". See §4.5.

### §9 MIR to waffle
Built as described (`wasm/mir/mod.rs`, `lower.rs`), except the flags part of step 4 (see §6).

### §10 Optimizations that must work
- **§10.1 Guard folding: built** (`opt.rs:362 fold_guards`), covering:
  - availability dataflow with fence kills;
  - by-type folding;
  - `canon` through `unbox`;
  - implication within a guard kind;
  - `forward_params`.

  **NEVER BUILT (low):** disproved → `fail` with a warning; dead-fail-block removal; exit sharing as a pass.
- **§10.2 Guard hoisting: PARTIAL** (med-high). No MIR-level guard LICM exists: `licm` skips terminators (`opt.rs:726`). The only hoisting is the builder's `HOIST_NATIVE` for `Native`/`Ta` receiver guards on loop entry edges (`build.rs:2756, 3313`). `guard.layout`, `guard.unbox`/`guard.tags` on invariant values, and `check.fuse` are never hoisted.
- **§10.3 Fences and rejoins:** the textual fixture `tests/fence_rejoin.mir` and the tests `fence_rejoin_wrong_fold`/`fold_guards_across_a_fence` exist. "The first guard on `a` hoists to P" is not achievable for layout guards (see above). The rejoin semantics diverged (kill exits).
- **§10.4 Box/unbox/weaken cleanup: NEVER BUILT** as passes. There is no `unbox(box x)` → `x` and no weaken-chain collapse. "Box sunk into exit blocks" is achieved by design instead: exit operands stay unboxed and the hubs box (§5.1). Low-med.
- **§10.5 Memory: PARTIAL**, covered in summary item 6.
  - Built: `cse_loads` (RLE plus store→load forwarding, clean edges only) and `licm` for pure/read-only non-terminators (`a28571e`).
  - Missing: DSE; element, env and global forwarding; memory knowledge surviving `ok_clean`.
- **§10.6 Numeric: PARTIAL**, covered in summary item 12.
- **Deliverables: PARTIAL.** No guard-count e2e tests, and no tests for `licm` or `cse_loads`.

### §11 v1 scope: doc drift (low)
- The declines now differ:
  - generators and async, global scripts, class constructors, scripts over 32 KiB, and any unlisted op (`build.rs:4928`) are declined;
  - `arguments`, rest, env ops and try are supported.
- "The MIR builder does not inline anything" is stale since M5c.
- Class-constructor and global-script declines are not listed in §11.

### §12 Decision log: doc drift
Rev 5 entries contradicted by later code, with the evidence in commits and §13 but not logged in §12:
- "ok_dirty re-guarding stays eager" (superseded by `f6e4207`);
- "SLOTS is local and tolerant … staying in OPT" (superseded by `f5f4045` GUARD_SLOTS and M5e dirty exits);
- "On failure, including a class-key miss, OPT exits" (superseded by M5d IC fallback).

Rev 6's "Exits write the whole frame" was amended to write-through and then reverted (`a2a6b69`), and §5.1 does not reflect the revert.

### §13 Milestones: marked done vs actually done
- **M0, M0b, M1, M2, M3, W:** done as stated.
- **M4 plan items.**
  - "guard folding **and hoisting**": folding is done; hoisting covers native/TA receivers only.
  - "Prediction witnesses and the §4.5 rule": structurally done, but the witnesses are all `ALL`.
  - "`ok_dirty` re-guarding": replaced by the exit design.
- **M5 plan items.**
  - Elements and TAs: done.
  - Globals via `gcell` bindings: not done as designed (inline arms instead).
  - Constructors: **not done**.
  - Env ops: done except scope-pushing ops.
  - Accurate flags: **not done**.
  - Liveness pruning: done.
- **M5b:** done per its Status, except the object component, and the gate counts are not evidenced.
- **M5c–M5h:** match the code.
- **M6:** not started, apart from `licm` and `cse_loads` (which count toward §10.5). Box/unbox cleanup, DSE and numeric range work are absent.

---

## Surprises
1. **The constructing lattice exists.** Only its producers and lowering are missing (see the top).
2. **Witnesses are all "may kill anything".** §4.5's check is structurally present but cannot catch anything.
3. **The biggest structural gap is opacity to the optimizer, not missing speed.** `a.length`, global reads and writes, object and array literals, constructor field adds, and `charCodeAt` all run fast inline arms in the lowering. But in MIR they are generic `js.*` ops or calls with `Unknown` writes and `may_run_js`. Any loop containing one defeats `licm`, `cse_loads` and fuse-check folding (see the `a28571e` commit note about navier-stokes).
4. **`load_field` is always a terminator** with `ok_clean/ok_dirty/err`, even when the lowering makes it a plain load under a SLOTS-proving guard. So invariant field loads can never be hoisted by `licm`.
5. **The text format cannot express inlined functions.** There is no `exit.inline` in the parser and no frame annotations.
6. **`FrameStore` has a PURE effect summary**, so it is eligible for `licm` hoisting if its operand is invariant. This is probably harmless (retention only), but unverified.
