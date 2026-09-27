# MIR vs legacy (bbv): parity audit

What the legacy BBV tier (`compiler/src/wasm/bbv/`) does that MIR
(`compiler/src/wasm/mir/`, `compiler/src/mir/`) does not, or does
differently. The goal is to capture everything legacy does before MIR
replaces it, including mechanisms that are masked today by MIR's other
advantages. Audited 2026-09-27 against a01edb9..2b94061; file:line
references are to that state and will drift.

Status: **same**, **partial** (fast path only / narrower), **missing**,
**different** (a deliberate design difference that still needs an
answer).

## 1. Structural differences (these cut across everything below)

1. **Guard failure = exit.** Legacy forks a side arm on a failed type or
   class test and keeps running compiled code in a weaker lineage
   (Side, Dirty, GEN) or in the op's helper. MIR exits to baseline
   (`guard`, `guard_result` in `build.rs`) and comes back only at a
   loop-header onramp. Affected: numeric claims (mixed int32|double
   claims are speculated int32-first and exit on any double, where
   legacy deliberately uses a boxed-numeric no-exit form,
   `bbv/arith.rs` `push_load_typed`), `I32Ovf`, entry formal guards,
   native/typed-array kind guards, blown fuses, a receiver with SLOTS
   clear or a non-number store into a SHALLOW object (to the uncached
   helper, then exit via `js_dirty_exits`).
2. **Facts die at every fence, even on clean paths.** `js()` sends
   `ok_clean` and `ok_dirty` to one block; `fence_params` demotes every
   proven `Obj` slot on every generic op (global reads, literal
   allocation, `InitProp`, closures, intrinsics, property IC ops,
   compares, calls, inlined calls, builtin-arm hits). Legacy keeps
   facts across IC hits, clean misses (`miss_second_chance`), side
   arms, unchanged epochs (`rt_call_keep*`), clean callee effect words
   (`emit_flag_fork`), and callee effect summaries
   (`summary_conflict_free`). MIR bodies always return `FLAGS_ALL`.
3. **No type refinement from dynamic tests.** Legacy's int arm of an
   untyped `+`, compare, bitop or inc refines the operand's source slot
   to int32 (`arith.rs`, `compare.rs:757`); a passed class guard is
   written back to the local/argument (`refine_src`). MIR results of
   generic ops stay boxed and operand slots never narrow.
4. **No loop-invariant code motion.** Legacy runs an effect-aware LICM
   (`bbv/licm.rs`) over shapes, class words, elements headers,
   typed-array data/length, gname rows, fuse cells, env loads. MIR
   hoists only Native/TypedArray kind guards (`HOIST_NATIVE`); its
   optimizer (`mir/opt.rs`) folds guards and forwards params, nothing
   else (no GVN/CSE, no constant folding, no range propagation;
   `CheckFuse` is not even folded).
5. **No ranges.** Legacy's interval/I53 machinery removes overflow and
   -0 checks, runs exact i64 arithmetic (including `%` via `rem_s`),
   seeds element/field ranges from stamps. MIR ignores `ValueRange`
   entirely, although `I32Ovf`/`IntArith` signatures already compute
   ranges.
6. **Whole-script declines.** Any unsupported op declines the whole
   script to baseline: `typeof globalName`, class constructors,
   generators/async, for-of/iterators, `??`, spread (call and array),
   `super`, `new.target`, `Hole`, `InitElemInc`, singleton `Object`,
   getter/setter element inits, lexical environments
   (`PushLexicalEnv`...), non-global `GetName`/`SetName`, eval.
7. **Unused IR.** `LoadGName`, `StoreGName`, `CheckBinding`,
   `NewObject(_)`, `NewArray`, `InitField`, `PublishLayout`,
   `CallDirect`, `CallNative`, `CheckNative`, `GuardSingleton`,
   `LengthArray`/`LengthString`/`LengthTa`, most `MathFn`, `IntArith`
   are defined but never built or lowered.

## 2. Priorities

Ordered by expected effect across the suite:

1. Keep facts on clean edges: split `ok_clean` from `ok_dirty` in the
   builder so only the dirty/helper edge fences (then epoch/flags keeps,
   then effect summaries for non-inlined calls).
2. Side arms instead of exits for the common guard misses: mixed
   numeric claims as boxed numbers, `I32Ovf` overflow to f64, layout
   misses to the IC (already done for reads), SLOTS-clear and SHALLOW
   stores to the IC with the store choke, kind mismatches to the generic
   op.
3. Coverage: the whole-script declines in 1.6.
4. Stamps MIR never writes: object-literal stamps (`lit_stamps_in`),
   array stamps (`array_stamp_in`), argument/local restamps
   (`arg_restamps_in`, `local_restamps_in`), inline delegate restamp.
   Under `--pipeline mir` nothing stamps these populations, so every
   class-fact guard predicting them misses.
5. Refinement from dynamic tests (1.3), and object/string claims in
   `guard_result` and entry claims.
6. LICM over the lowered code or in MIR (1.4); ranges (1.5) and overflow
   check removal.
7. Calls: static direct calls for non-inlined likely callees
   (`likely_patches`, fuse-guarded gname calls), the typed-entry SEL bit,
   native dispatch for native callees, apply-forward wrappers
   (inline them; `apply_targets_in`; >4 targets and dynamic arm),
   accessor arms, move char arms behind the native bit.
8. Element paths: dense append/hole store, `s[i]`, `arguments[i]` via
   GetElem, polymorphic typed arrays (`elem_poly_sites`), mega
   string-key get/set, unboxed typed-array reads, `%`/`>>>` results
   staying int for indexing.
9. Strings: inline string equality and literal-RHS compares, the quiet
   concat arm (`string_arith_sites`), STRING result types.

## 3. Property access (GetProp/SetProp)

| Legacy | MIR | Status |
|---|---|---|
| Class-fact get, one fused layout+SLOTS compare, miss to IC, fact written back (`property.rs` `emit_class_fact_get`) | `guard_layout_or` + `LoadField` (`build.rs`), separate layout and SLOTS tests; SLOTS-clear goes to the uncached helper and exits | partial |
| Checkless read under proven class+SLOTS facts | no SLOTS-proven fact; class word reloaded every access | partial |
| SHALLOW\|SLOTS(\|RANGES) typed read, RANGES seeds interval | `types` only when the whole layout is numeric (`numeric_layout`); no ranges | partial |
| `layout_site_for`: site row synthesized from a proven class | only `prop_sites_in` rows | missing |
| Advisory class hints (`field_cls_sites`, `arg_cls`) | none | missing |
| `this` class fact lazily via `refine_src` | entry `guard_this_layout`, exits; dies at next fence | different |
| Fact lifetime (killed only by GC-capable calls, set IC, non-number stores) | every generic op fences | partial |
| Clean-miss second chance | none | missing |
| `length` arms | `length_arms` | same |
| `charCodeAt`/`charAt` method reads | same, but emitted even for known-object receivers | same |
| IC inline ways + holder tail | `get_ic_ways` (4 ways, since a01edb9) | same |
| Accessor get/set arms (`accessor_sites`, `accessor_names`) | none | missing |
| Class-fact set, checkless under facts, barrier skipped for any non-GC value | numeric values only skip barriers; TYPES-claimed site with non-number value drops to generic | partial |
| Store choke elision via `layout_field_masks_in` | none | missing |
| Store choke clears SHALLOW and bumps epoch | non-number into SHALLOW object goes to helper | partial |
| Constructor init masks (`ctor_init_claim`) | relies on CONSTRUCTING exemption | missing |
| Range acts on stores (`layout_field_ranges_in`) | RANGES always cleared | missing |
| Set IC way 0 | `set_ic_way0` | partial |
| Mega-set probe | none | missing |
| Add-transition replay, static prediction forms | runtime-pair form only (`set_ic_trans`) | partial |
| Prototype-proof cell | none | missing |

## 4. Calls, construct, inlining

| Legacy | MIR | Status |
|---|---|---|
| Call cell classify | `classify_native` | same |
| Likely-direct static call (`likely_patches`) | always `call_indirect` | missing |
| Fuse-guarded direct call to a global function | none (inlining only) | missing |
| Typed entry (ARGC_SEL_BIT) proven by caller | never set; callee always re-validates | missing |
| Entry claims for this/object/string/bool/symbol/TA | numeric formals + `this` layout only | partial |
| `call_types` result claims, all shapes | numeric only | partial |
| Flag fork / epoch keep / summary keep after calls | none; facts die | missing |
| Native dispatch route (`native_dispatch`, `BC_STR_*`) | natives via `night_runtime_call` | missing |
| Math arms | `math_arms` (results boxed) | same |
| parseInt arm | none | missing |
| char arms after direct dispatch fails | before classify, on every 1-arg call | partial |
| push/pop arms | `push_arm`/`pop_arm` | same |
| `hasOwnProperty.call` arm (`apply_natives`) | none | missing |
| Apply-forward: splice wrapper, per-entry targets (`apply_targets_in`), up to 16 static arms + dynamic arm | wrappers never inlined; ≤4 inline targets else runtime helper | partial |
| Inline policy (mono 150/200, poly 500, depth 4/8 by root nest, closure cost, fuel) | caps and depth 4; in-loop test uses own loops; instruction budgets; no fuel (declines instead) | partial |
| Inline guard: call-cell hit + patched funcidx compare | `GuardScript`, ~7 dependent loads | partial |
| Caller facts into inlined callee, restored at return | demoted before splice | partial |
| Construct: likely-ctor static arm, per-funcidx nslots region, class guard on result, fresh marking | `call_indirect`, static nslots only, `Val(object)` result | partial |
| Ctor-exit stamp | `ctor_stamp_inline` | same |
| Delegate restamp inline | helper call; delegates never inlined | partial |
| Arg/local restamps | none | missing |
| SpreadCall, SuperCall, CallIter, eval | decline script | missing |

## 5. Elements, arithmetic, types

| Legacy | MIR | Status |
|---|---|---|
| Dense read arm always (runtime native check) | only when predicted and key typed I32; kind miss exits | partial |
| Array-stamp read fold with element range | none | missing |
| Array allocation stamps (`array_stamp_in`) | word 0 | missing |
| Element store duty (prove or clear RANGES) | always clears | partial |
| Dense append / hole store arm | none (push arm only) | missing |
| Typed-array read, unboxed result with kind interval, Uint32 | re-boxed and joined as `Val(ALL)`; Uint32 excluded; kind miss exits | partial |
| Typed-array store, F64 into int kinds | int and boxed-int only (since a01edb9) | partial |
| Polymorphic TA arm (`elem_poly_sites`) | none | missing |
| `s[i]` string arm | none | missing |
| `arguments[i]` via GetElem | bytecode forms only | partial |
| Mega string-key elem get/set | none | missing |
| Overflow check removal by intervals; overflow → f64 side arm | always checked; overflow exits | partial |
| Truncation demand incl. Mul | Add/Sub only (`int32_demand`) | partial |
| I64/I53 exact arithmetic, `%` via `rem_s` | none | missing |
| Untyped-operand ladders refine source slots | results stay boxed | partial |
| Fractional-site raw f64 add (`fractional_arith_sites`) | none | missing |
| String `+` concat arm (`string_arith_sites`) | generic add | missing |
| Typed `%` on I32 operands | boxed generic, F64 result | partial |
| `>>>` as I64 | F64 (loses int indexing) | partial |
| Generic untyped unops | NUM\|BIGINT results | partial |
| `bigint_free` | per-operand tags only (since a01edb9) | partial |
| String equality, literal-RHS compares, switch-on-string | helper | missing |
| Post-compare refinement | none | missing |
| Math results unboxed | boxed | partial |
| Mixed numeric claims: boxed, no exit | int32-first, exit on double | different |
| Loop re-entry with range guards | tag/kind/layout guards only | partial |

## 6. Allocation, globals, environments

| Legacy | MIR | Status |
|---|---|---|
| Literal bump allocation | `alloc_inline` | same (but a fence) |
| Object-literal stamps (`lit_stamps_in`) | none | missing |
| InitProp transition replay | `init_prop_inline` | same (a fence per property) |
| InitElemArray fill | `init_elem_inline` | same (no store duty) |
| Holey/spread/singleton literals, `__proto__`, home objects, fun names | decline script | missing |
| Construct cell + nursery bump | `construct_this` | same |
| Fused literal globals | `fused_gname` (exits when blown) | same |
| Value-fuse and guarded-slot gname arms | `gname_fast_arms` | same (a fence) |
| Global value facts (`gcell_bids`) | per-read guard | missing |
| `typeof globalName` | decline script | missing |
| Bind/SetGName inline arms | `gname_bind_arms`, `gname_set_arms` | same (a fence) |
| Aliased vars with static fixed/dynamic slot addressing | shape decoded each access; env walk each access | partial |
| Lexical environments, non-global names | decline script | missing |
| Intrinsic/BuiltinObject cells | since 2b94061 | same (a fence) |
| Exceptions: catch/finally compiled | throws exit; catch never built | different |

## 7. Facts: which tier reads what

Read by legacy only: `accessor_sites`, `accessor_names`,
`apply_natives`, `apply_targets_in`, `arg_cls`, `field_cls_sites`,
`arg_restamps_in`, `local_restamps_in`, `lit_stamps_in`,
`array_stamp_in`, `array_any_claim`, `likely_elems`,
`layout_field_masks_in`, `layout_field_ranges_in`, `gcell_bids`,
`elem_poly_sites`, `fractional_arith_sites`, `string_arith_sites`,
`bigint_free`, `script_effects`, `flag_demand`, `classes`,
`group_tables`, `ctor_nslots_in` (region form).

Read by both, but narrower in MIR: `arg_types` (numeric only),
`call_types` (numeric only), `gname_types` (numeric only),
`array_elem_in` (as a "predicted" bit, no mask or range),
`prop_sites_in` (no `range`), `this_layouts_in` (only `init_home`).

Read by MIR only: `this_layouts` (entry guard), `omitted_formals`,
`elem_sites` (directly, rather than via `likely_elems`).
