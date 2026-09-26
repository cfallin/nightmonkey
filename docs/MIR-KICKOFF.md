# MIR implementation kickoff

This is the starting brief for implementing the MIR described in
`docs/MIR.md` (the design, rev 5). Read that first. This document says
what to build first, where it goes, what "done" means for the first
milestones, and which conventions to follow. The design is settled
unless implementation turns up a real problem. If it does, stop and
raise it rather than quietly diverging, and record the outcome in the
design doc's decision log (§12).

## 1. Orientation

**Read in this order:**

1. `docs/MIR.md`: all of it. The load-bearing sections are:
   - §2 (types);
   - §3–§4 (facts, fences, weakening, stamp bits, predictions);
   - §5 (exits, onramps, throws);
   - §7 (ops);
   - §10 (optimizations that must work);
   - §13 (plan).
2. `docs/DESIGN.md`: the current system, especially §5 (versions and
   tracks) and §6 (stamps).
3. The code MIR must interoperate with:
   - `compiler/src/facts.rs`: `LikelyFacts`, the builder's input.
   - `compiler/src/opsem.rs`: `Prims`, `Range`, `ValueRange`, `TaKind`,
     and the numeric algebra. **Reuse these; don't fork them.**
   - `compiler/src/ids.rs`: `ScriptId`, `Pc`, `Site`, `LayoutKey`,
     `StampKey`, `SlotIndex`, `RegionRoot`, `NameId`.
   - `compiler/src/wasm/bbv/`, the GEN side that MIR lowers alongside:
     - `version.rs`: `theta`, `cont_at`, tokens, `emit_proof`;
     - `ctx.rs`: `Track`, `Repr`, `Ctx`;
     - `frame.rs`: `write_local`, `exception_target`, barriers;
     - `emit.rs`: `rt_call`, the spill/reload rooting handshake;
     - `property.rs`, `element.rs`, `arith.rs`, `call.rs`: the lowerings
       MIR ops will reuse;
     - `abi.rs`: frame offsets and stamp-word bits.
   - `runtime/NightObjectWord.h`: the stamp word and the store-mask
     policy.

**Commands:**
- `cargo test -p night-compiler`, for unit tests. MIR tests live here.
- `scripts/run-jit-tests.sh <firefox-checkout> [build-dir]` and
  `scripts/run-night-tests.sh`, for end-to-end lanes (from M1/M2 on).
  `NIGHT_INPROCESS_OFF=1` gives the interpreter-only baseline lane.

## 2. Conventions

- **Where code goes:** new code lives in `compiler/src/mir/`, as a
  `pub mod mir` in `lib.rs`. The only changes to `wasm/bbv` are the
  seams MIR needs (§5 below). Don't restructure the legacy path; it
  must keep working unchanged when MIR is off.
- **License:** new files carry no license header (Apache-2.0 via the
  root `LICENSE`). Anything copied from SpiderMonkey goes in its own
  MPL-headed file with a provenance note.
- **Style:** match the surrounding code. Use `//!` module docs that
  explain *why*, typed ids rather than bare integers (the `ids.rs`
  pattern), and `FxHashMap`/`FxHashSet`. Anything that affects output
  must iterate deterministically.
- **Option gate:** add `Options::mir: MirMode { Off, On, Only }`.
  - `Off` is the default.
  - `On`: MIR for the scripts the builder accepts, legacy for the rest.
  - `Only`: MIR or GEN-only, never legacy OPT. This is for coverage
    testing.

  Plumb it through `options.rs` and the in-process and snapshot flag
  parsing.
- **Diagnostics:** extend `Diagnostics` with a per-script line
  `night: mir <sid> {compiled|declined:<reason>|legacy}`, plus a
  summary count. Coverage must be measured, never assumed.
- **Commits:** one logical step per commit, and never commit to `main`.
  Each commit builds and passes `cargo test`.

## 3. M0: IR core (`compiler/src/mir/`)

### 3.1 Files

| File | Contents |
|---|---|
| `mod.rs` | Module docs, re-exports |
| `entity.rs` | `Value`, `Block`, `Inst`, `FrameShape`, `RegionId`, `FactId`… typed indices + `EntityVec`/`EntityMap` (or reuse waffle's `entity`, if it fits) |
| `types.rs` | `Type`, `VSet`, `TagSet`, `NumInfo`, `IRange`, `ObjInfo`, `ObjKind`, `LayoutClaim`, `StrInfo`, `RawKind`, `FactKind`; `is_subtype`, `join`, `repr()`, `killable_components()` |
| `ops.rs` | `Opcode` enum and `InstData` (operands, immediates, attachment id); per-op signature and result-type rule; `Effects` (reads/writes as region sets, may_gc, may_run_js, may_throw, kill pattern, flags contribution) |
| `func.rs` | `Func`: blocks (params, insts, terminator), values (def, type), roots (function entry + onramp roots), attachments side table, prediction-witness side table |
| `module.rs` | Module-level tables: layouts (key → fields, claims), alias regions, snapshot objects, atoms, fuses/bindings |
| `print.rs` / `parse.rs` | Text format (§3.2); `parse(print(f)) == f` |
| `verify.rs` | Validator (§3.3) |
| `tests/` | Text-format fixtures + Rust test drivers |

### 3.2 Text format

- It is for tests and dumps, so optimize for writing by hand.
- It must round-trip, and print deterministically.
- Suggested shape (adjust freely):

```
module {
  layout L3 = { x: val{int32} range[0,99], y: val{int32,double}, next: val{object} kind=Plain }
  region R0 = field(L3, x)
}

func @s12 (formals=1, locals=2) {
  root entry b0
  root onramp(pc=24) b5

b0(v0: obj{Function(s12)}, v1: val, v2: val):          ; callee, this, a0
  guard.unbox.i32 v2 -> ok b1(v3: i32), fail b9

b1(v3: i32):
  v4 = const.i32 0
  jump b2(v3, v4)

b2(v5: i32, v6: i32):                                  ; loop header
  ...
  i32.add.ovf v6, v5 -> ok b3(v7: i32[..]), fail b10

b9:
  exit pc=0 this=[v1] args=[v2] locals=[undef, undef] stack=[]
  ...
}
```

- Terminator successor lists name the value each edge *defines*
  (`ok b1(v3: i32)`). Guard outputs are the success block's params,
  and the printer shows the types.
- Attachments print as trailing `@{…}`.
- Prediction witnesses print as `!pred{…}`.

### 3.3 Validator checks

Every check needs a positive test and at least one negative test with
an expected error:

1. **Structure:** every block has exactly one terminator, successors
   exist, and edge arity matches the target's params.
2. **Dominance over multiple roots,** using a virtual super-root. Every
   use is dominated by its def; for a blockparam, by its block.
3. **Edge subtyping:** arg type ≤ param type, within the same
   representation (§2.2).
4. **Operand types** per op signature (for example, `unbox.i32` requires
   a `Val` whose tags ⊆ {int32}).
5. **Fences (§4.1–4.2):**
   - For each fence op or fence edge, no value whose type matches the
     kill pattern is live across it, except through a weaker-typed
     blockparam on a fence edge.
   - Liveness is standard backward liveness, and ghost `Fact` values
     count.
6. **Predicted or dynamic (§4.5):** every static kill of a component is
   covered by that op's prediction witness. Kills on `ok_dirty` edges
   are exempt.
7. **Raw across GC (§4.4):** no `Raw` value is live across a may-GC op.
8. **Boundary (§5):**
   - `exit`/`exit.throw` operands are all `Val(⊤)`, with arity equal to
     `FrameShape` (formals, locals, and the stack depth at `pc`);
   - an onramp root's params are all `Val(⊤)` with the same arity;
   - each loop has a unique preheader `P` that is the header's only
     non-backedge predecessor.

### 3.4 Definition of done (M0)

- [ ] Types: subtyping and join are unit-tested, including the
  constructing-prefix rule (§2.3) and shallow object loads (§4.3).
- [ ] Every op in MIR.md §7 is defined with a signature, result rule,
  and effect summary. Lowering doesn't exist yet.
- [ ] Printer and parser round-trip on all fixtures.
- [ ] Validator: all eight check families, each with positive and
  negative tests.
- [ ] A hand-written fixture of the §10.3 shape
  (`loop { a.x; f(); a.x }`) validates. A deliberately wrong variant
  (the second guard folded across the `ok_dirty` edge) is rejected with
  a fence error.

## 4. M1: minimal lowering

This is a preview; plan it in detail once M0 lands. The goal is
**hand-written MIR, lowered and running end to end, with forced
exits**, before any JSOps→MIR builder exists. That separates lowering
bugs from builder bugs.

- Subset: constants, `box`/`unbox`, i32/int/f64 arithmetic (`.ovf`
  forms), compares, `br`/`jump`/loops, `return`, `exit`, and
  `exit.throw`.
- A test hook to substitute a hand-written MIR body for a named script.
  A debug option pointing at a `.mir` file is enough.
- Flags: return `FLAGS_ALL` everywhere (§6 threading comes with calls in
  M4).

## 5. The GEN seam

This is the main integration risk, so investigate it first. M1 needs
three things from `wasm/bbv`:

1. **GEN pinned to `Dirty`, with tokens.** Today's rungs are `gen_only`,
   which has no tokens and no carriers, or full OPT+GEN. MIR needs a
   Dirty-only emission that still computes tokens and peel funnels, so
   exits into loops stay reducible (MIR.md §5.4). Find the smallest
   change to `theta`/`run_version_inner` that does this.
2. **An exit-landing API:**
   `gen_landing(pc, depth, token_ctx) -> (Block, ParamLayout)`. It gives
   the GEN version block an exit branches to, and the order of its
   params (operand stack, carried locals, flags). The exit lowering
   stores `this`, the args and the locals to the frame (`write_local`
   discipline), then passes the rest as block args.
3. **The throw path:** reuse `exception_target` (`frame.rs:213`) for
   `exit.throw`. It needs the current stack view, so the lowering must
   present the MIR frame state in the shape that function expects.

Write a short note, `docs/MIR-GEN-SEAM.md`, with the proposed API and
the diff to `bbv` before implementing it, and get it reviewed.

## 6. Things to decide during M0 (recommendations)

- **Entity arenas:** reuse `waffle::entity` if its `EntityVec`/
  `PerEntity` fit; otherwise write a minimal equivalent. Don't pull in a
  new dependency for this.
- **Terminators with block-defined outputs:** model a successor as
  `(Block, Vec<ValueOrOutput>)`, where an output slot is filled by the
  terminator (a guard's refined value, a call result). This keeps the
  "guard outputs are success-block params" rule uniform.
- **Type interning:** `Type` will be compared and joined constantly.
  Intern it in the `Func` (a `TypeId` into a table) if profiling shows
  the need; start with a plain `Clone` enum.
- **Kill patterns:** represent them as a small bitset over killable
  component classes (layout identity, `types`, per-fact-kind), plus an
  optional region or layout-range filter for later refinement.

## 7. Out of scope until later milestones

- The JSOps→MIR builder (M2)
- Onramps (M3)
- Objects and calls (M4)
- Elements, globals, constructors, env (M5)
- Richer field claims and the store-mask change (M5b)
- Optimization passes (M4 for guard folding and hoisting, M6 for the
  rest)

Don't start these early. The point of M0 and M1 is a small, fully
tested core that everything else builds on.
