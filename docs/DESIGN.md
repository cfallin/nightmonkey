# NightMonkey design

NightMonkey is an ahead-of-time compiler from SpiderMonkey bytecode to
WebAssembly. SpiderMonkey and compiled JavaScript execute in the same Wasm
module and linear memory, so compiled bodies can call engine helpers, inspect
engine data structures, and call one another.

This document describes the current implementation. It separates correctness
contracts from policy: limits and predictions may reduce coverage or
performance, but must never be required for correct execution.

## 1. Scope and deployment contract

NightMonkey consumes a closed snapshot of scripts and selected heap objects.
It does not consume execution profiles. The intended deployment is one
wasm32-wasi SpiderMonkey runtime, one active `JSContext`, and one installed AOT
environment per process.

Those restrictions are currently embedding assumptions, not fully enforced API
properties. Most AOT runtime state is process-global. An embedding must not
install two environments or activate NightMonkey in two runtimes. The
module-wide BigInt optimization also assumes values cannot enter from source or
an embedder outside the captured program. Until enforced or removed, these are
part of the trusted deployment boundary.

A compilation unit is a registered script tree plus selected self-hosted
scripts and regular-expression programs. A script is compiled as a whole or
remains interpreted. Unsupported operations, environments, limits, or
translation failures never produce partially compiled scripts.

## 2. End-to-end flow

Two deployment modes use the same analysis and translator.

### Snapshot flow

1. The wasm32-wasi shell compiles and registers script roots.
2. Registration delazifies reachable function trees and serializes information
   an external memory reader cannot safely derive.
3. Wizer captures the initialized module.
4. The host `nightmonkey` tool reads the registration block and snapshot,
   constructs `Source`, runs analysis, appends compiled functions, lays out AOT
   data, and patches function indices and object stamps.
5. On resume, `JS::NightActivate` installs the environment and enables AOT
   dispatch.

### In-process flow

1. The wasm shell captures live scripts and heap objects into `Source`.
2. The NightMonkey compiler, inside the Wasm instance, builds a temporary
   module with imported runtime helpers and serializes its defined functions as
   runner blobs.
3. `wasm-jit-runner` injects the functions into the running instance.
4. The shell installs the environment descriptor and patches scripts to their
   injected table entries.

The helper indices, table indices, region addresses, and serialized tables must
describe exactly the module that receives the blobs.

## 3. Compiler inputs and identities

`compiler/src/source.rs` owns the compiler input. `SourceObject` variants
describe scripts, scopes, objects, strings, symbols, and primitive values.
`source/ffi.rs` builds the graph in-process; the snapshot crate builds it from
the captured image.

Typed identifiers in `ids.rs` distinguish scripts, bytecode PCs, program
sites, names, layout keys, and their biased runtime stamp keys. Traversal of
maps that affects emitted identities must be stable; diagnostics and hash-table
iteration must not influence output.

`bytecode.rs` uses a generated `JSOp` enum and generated operand and stack
metadata. Its parser supports direct decoding and the `OpcodeVisitor` interface
used by analysis and prepasses.

## 4. Likely-facts analysis

`likelier` is an optimistic whole-program dataflow analysis. Its results are
predictions, not proofs. Codegen may use them only to select and order guarded
paths; a failed guard must reach a semantically complete path.

### Constraint graph and fixpoint

`scan.rs` walks each script once and builds constraints over an abstract
operand stack. Locals are flow-sensitive. Assignments create new abstract
values, control-flow joins create explicit join values, and loop headers
materialize joins eagerly for back edges.

`engine.rs` owns cells, constraints, subscriptions, provenance, and the
incremental worklist. Constraints are generated once and evaluated in each live
calling context. Cell growth requeues its subscribers.

`types.rs` combines bounded primitive and function sets, numeric magnitude and
interval information, and an object abstraction that widens from one allocation
to a class and then arbitrary object. Joins only weaken information. Every
resource limit must degrade in that direction: merge contexts, mark overflow,
drop a heap prediction, or widen to unknown.

### Calls and heap

`calls.rs` represents context as an interned bounded call string.  Arguments
and receivers flow into context-indexed callee cells; returns flow back to call
sites. Recursion, depth, fanout, and global budget limits fall back to the
generic context.

`heap.rs` models snapshot objects, allocation abstractions, fields, prototypes,
arrays, and constructor classes. Snapshot state seeds the same cells that later
program writes update. Property reads join every prototype level they might
observe. Elements use a separate abstract field to avoid merging unrelated
prototype elements.

The points-to model of the heap is a combination of Andersen points-to (with
points-to sets and membership/subset relations) and Steensgaard points-to (with
a union-find data structure that merges abstractions bidirectionally on any
interaction). Specifically, a typeset describes its object-reference component
as an element in a lattice that contains allocation sites at the bottom tier;
then constructor classes (every allocation site belongs to one constructor
class or a special pseudoclass for object literals); then union-find "regions"
of classes. Flow is still directional (no bidirectional union as in
Steensgaard), but where an Andersen points-to set would grow from one to
multiple elements, our points-to model instead merges the merging classes in
the union-find and represents the merged value by pointing to that region
instead.

Each heap abstraction carries predicted types per field name and predicted slot
number (property/shape order) per field name.

Constructor events record ordered writes and delegation. `likelier/emit.rs`
forms predicted fixed-slot layouts, groups compatible prefixes, assigns stable
layout keys, and emits site facts. `likelier/effects.rs` computes post-fixpoint
effect summaries per function (script).

`facts.rs::LikelyFacts` is the analysis-to-codegen contract. It contains value
claims, call resolutions, heap and element predictions, effect summaries,
global facts, and inlining inputs. Codegen should not reach into solver state.

`opsem.rs` is shared vocabulary for primitive sets, numeric magnitude,
intervals, and modeled operator results. It prevents analysis and codegen from
maintaining separate arithmetic semantics. Predicted results remain untrusted;
an interval originating at a guarded or canonical producer can become a proof
inside codegen.

## 5. Translation and basic-block versioning

`wasm/mod.rs` runs analysis, lays out memory regions, translates scripts and
regexps, places functions in the indirect table, and patches address
placeholders after bases are known.

`wasm/bbv` is the actual JavaScript bytecode to Wasm bytecode translator. Each
bytecode operation ends a generated block; a workqueue emits every reachable
structural version.

### Versions, predictions, and tracks

The overall strategy of the codegen backend is to emit code in two "tracks":
optimistic (OPT) and generic (GEN). The optimistic track is meant to align with
all of the predictions that the static type analysis makes; if the program
diverges from those types, execution is shunted to the generic track. Likewise,
in the other direction, if execution in the generic track can prove that it
meets all the assumptions of the optimistic track, we can shunt execution back.
We sometimes call these "offramps" and "onramps", colloquially. Each transition
may involve some boxing/unboxing, because OPT can carry values in raw unboxed
form.

Reducibility concerns (Wasm requires reducible CFGs) complexify the two-track
design somewhat: we need to duplicate code further into versions that are keyed
on which loop headers they are dominated by. Otherwise, an onramp or offramp
would become a side-entrance to the other copy of any loop in the current
loop-nest.

A basic block in the emitted IR is part of the lowering for a given JSOp for
one "version". That version is identified by its PC, execution track,
nested-loop token-vector class (the above-mentioned reducibility scheme), and
inline-segment depth (the means of conceptually duplicating code for inlining).

Each version carries a fact context: known types, object class-stamps (see
below), and unboxed representation choices for each value.  `predict.rs`
computes one optimistic context per program point; the generic track carries no
speculative facts.

The translator first runs a context-only fixpoint, then emits against the
closed prediction map. If emission discovers an unclosed successor, the script
is retried with less specialization. The bottom compile-ladder rung emits
generic-only code.

The optimistic track carries facts proved by guards and prior operations. Side
arms handle cases outside an optimistic lowering and continue with weakened
facts. The generic track uses boxed values and runtime helpers and is the
correctness floor.

All inter-operation edges pass through the continuation and `theta` machinery
in `version.rs` (named for the corresponding `theta` function in Static Basic
Block Versioning, which our version management previously followed more
closely). This code owns fact joining, track weakening, loop tokens, reducible
CFG construction, values carried across blocks, and guarded recovery from weak
loop or call-return paths. Lowerings must not bypass it for ordinary bytecode
successors.

### Representations and proofs

An operand records Wasm representation separately from JavaScript type. Common
representations are boxed `JS::Value`, `i32`, exact integer `i64`, `f64`, object
or string pointer, and boolean.

A codegen fact must originate in a dominating runtime guard, an exact producer,
a helper or canonical-boxing invariant, or preservation across a proven effect
class. An analysis prediction alone may not manufacture an unboxed value or
remove a required check. Generic helpers accept and return full boxed values
and preserve JavaScript exception behavior.

Before a may-GC call, every live GC value must be visible in the traced AOT
stack or another engine root. `live.rs` and frame flushing determine what is
materialized. Compiled direct calls return an error result and effect bits;
effect bits kill heap, stamp, and binding facts but do not replace rooting.

### Inlining

Inlining creates a synthetic bytecode segment in the caller's PC space. The
callee uses an alternate frame view and its returns rejoin the caller. Try
notes, environments, arguments, script-relative operands, generator state, and
absolute side-table PCs need special handling.

The implementation currently admits a callee unless an opcode is in the manual
`splice_blocked` list. That list is a correctness boundary: omitting a
root-frame-relative or script-relative lowering can miscompile. The desired
invariant is complete use of active frame/script abstractions so ordinary
lowerings are splice-safe by construction; we will eventually complete that
migration.

## 6. Object layouts and stamps

At runtime, all objects are "stamped" with their class ID according to this
lattice, and have bits indicating whether they still conform to the predicted
types and slot numbers. Emitted specialized code can guard on these ID-stamps
and validity bits to enable the use of raw, unchecked property accesses.
Properties are still always stored in boxed form, for compatibility with the
rest of the runtime.

A 32-bit stamp occupies the wasm32 `JSObject` alignment word at offset 4. Zero
means unstamped. The low 16 bits identify a predicted layout. Upper bits say
which subclaims remain valid. During construction, identity is unpublished and
an early key identifies the layout being built.

| Claim | Meaning | Use | Invalidation |
|---|---|---|---|
| identity | object has one compatible layout key | select a property layout | wholesale clear or restamp |
| TYPES/SHALLOW | guarded fields retain their numeric type property | remove redundant numberness checks | a non-number protected-field store |
| SLOTS | properties occupy predicted slots | bake a fixed-slot offset | an unexpected in-prefix property addition |
| RANGES | protected fields retain predicted intervals | propagate interval proofs | every unchecked engine store or an out-of-range compiled store |

Correctness requires an invalidation cut across all mutation paths: engine
stores call the NightMonkey store check; compiled stores perform equivalent
maintenance inline; property additions call `NightAddPropCheck`; shape and
prototype mutations clear identity when required; and GC forwarding either
updates roots or invalidates raw-pointer caches.

The construction sentinel prevents partial objects passing identity guards.
Constructor exit publishes identity only after checked stores establish the
surviving validity bits. Compatible prefix layouts receive contiguous keys so
one range check can cover a layout *region*. Older comments call a region a
*clump*.

## 7. Caches and fuses

A fuse is a rarely changing condition represented by an armed or blown word.
It is safe only if every operation that can falsify it reaches an invalidation
point. NightMonkey uses fuses or generations for bindings, call and constructor
targets, builtins, prototype-dependent operations, and dynamically compiled
source.

Global property hooks invalidate binding fuses for interpreted writes. Property
cache rows publish their validity word last so generated code cannot see a
partial row. Major GC clears raw shape/prototype caches; minor GC clears or
rebuilds subsets that can hold nursery pointers.

The dynamic-source fuse is intended to be monotone after capture. Re-arming is
sound only when registration accounts for every source compiled so far and no
unregistered compilation is interleaved.

## 8. Runtime ABI and memory regions

`NightEnv.h` defines the ordered environment descriptor shared by compiler and
runtime; `compiler/build.rs` generates its Rust mirror. `NightRegionShape.h`
similarly shares cache sizes and row strides. These are the preferred pattern
for cross-language ABI data.

The environment contains atom, layout, binding, fuse, builtin, regex, and cache
tables plus mutable cells. Snapshot region words are absolute addresses.
In-process table words are descriptor-relative offsets and are rebased during
installation; address and length words remain absolute.

`NightHelperList.h` is the C++ helper manifest. Rust's `Helpers` structure and
resolution logic manually duplicate it and should be generated from the same
source. `bbv/abi.rs` records SpiderMonkey offsets and selector values baked into
Wasm. `NightInlineHeap.cpp` statically asserts the engine-layout half. New ABI
data should use generated shared definitions rather than paired literals.

## 9. Entry, stack, and GC

`NightStack` is a separately allocated array of boxed values owned by
`JSContext`; its live prefix is traced as roots. `AutoNightReentry` restores the
old top after interpreter-to-AOT reentry.

An entry frame contains callee, receiver, actual/formal slots, locals, and
operand storage. Missing actuals are padded with `undefined`. The complete frame
must fit before entry. Bounds checks must compare integer slot counts before
forming an end pointer, because an already-out-of-range C++ pointer is undefined
even if it is used only in a comparison.

Generated code may retain non-GC scalars in SSA across calls. GC pointers that
survive a may-GC operation must be in the live stack prefix or another root.
Inline heap writes mirror SpiderMonkey barriers using offsets pinned by static
assertions.

Most installed state, caches, persistent roots, and callbacks are process-global
and have no teardown. This matches the single-image shell deployment but must
be enforced or redesigned before runtime destruction and recreation.

## 10. Generators, async, exceptions, and regexps

Generator and async bodies have generic-track support in `bbv/generator.rs` and
`NightGenerator.cpp`. Suspension stores locals and operands in an engine object
using an AOT-owned layout; resume re-enters the same compiled script. An
AOT-suspended generator cannot resume in the interpreter. Bodies needing an
arguments object remain unsupported, and resumable bodies do not receive the
ordinary optimistic specialization.

Try notes feed CFG and frame construction. Calls and helpers propagate pending
exceptions through the error result. Inlining rejects contexts whose exception
or frame semantics cannot be represented by a splice.

`wasm/regex.rs` translates supported irregexp bytecode to Wasm. Runtime matching
selects installed matchers by pattern and flags. A matcher returns success,
failure, or retry; retry and unsupported programs use irregexp's established
fallback. Exhausting fixed backtracking storage must return retry.

## 11. Limits and policy

`constants.rs` is intended to collect analysis, specialization, inlining,
translation, and diagnostic policy. Structural ABI limits stay with their
representations. Some limits are scattered throughout the implementations of
various heuristics; cleanup is ongoing.

## 12. Capabilities and fallback

The exhaustive match in `bbv/ops.rs` determines lowering support. Explicit
declines include BigInt literals, eval variants, module imports,
explicit-resource-management operations, and interpreter/debugger escapes.
Environment gates reject frame shapes the runtime cannot model.

Opcode knowledge is also duplicated in analysis transfer, effects, splice
safety, visualization, and auxiliary scans. An exhaustive lowering match does
not make those classifications exhaustive. A single opcode capability
description should state stack and immediate shape, analysis transfer, effects,
frame/script relativity, splice safety, and lowering support. New opcodes should
fail tests until every dimension is classified.

Fallback has three levels:

1. failed specialization continues in generic compiled code;
2. helpers and regex matchers use established engine slow paths;
3. untranslatable scripts have no AOT entry and remain interpreted.

Tests must distinguish these. Passing a language test through a shell that can
silently interpret a declined script does not establish generated-code coverage.

## 13. Validation

Validation includes Rust unit tests, jit-tests and jstests in AOT and
interpreter-only wasm lanes, differential application runs, Wasm validation,
post-translation reducibility checks, C++ assertions for baked layouts, and
diagnostics for degradation, skipped scripts, guards, effects, and caches.

## 14. Glossary

- **likely fact**: an untrusted analysis prediction.
- **codegen fact**: a property proved by a guard or sound producer and carried
  in a BBV context.
- **track**: optimistic or generic execution state in version identity.
- **side arm**: a guarded alternative inside one lowering.
- **rung**: a retry step of the compile ladder with less specialization.
- **theta**: the continuation and version-interning logic between operations.
- **carrier**: an unboxed SSA value passed between versions.
- **splice**: an inlined callee represented as synthetic bytecode.
- **stamp**: the object word identifying layout and valid subclaims.
- **region**: a compatible contiguous family of layout keys.
- **fuse**: an armed condition with a complete invalidation cut.
- **choke/chokepoint**: an invalidation point. Prefer that standard term in new
  code.
- **dirty**: a lineage whose facts were weakened by effects or a failed route.
- **on-ramp**: a guarded edge from a weak lineage to an optimistic context.
