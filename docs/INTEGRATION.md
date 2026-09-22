# SpiderMonkey integration: the external compiler hook surface

NightMonkey is a separate repository that links against a SpiderMonkey
build. Everything it needs from the engine sits behind one configure option,
`--enable-external-compiler-hooks` (`JS_EXTERNAL_COMPILER_HOOKS`), carried on
the `nightmonkey-external` branch of cfallin/firefox. An ordinary
build without the option is unaffected. This document lists the surface by
mechanism, so it can be reviewed as a patch and ported to another
SpiderMonkey (mozjs, a newer mozilla-central).

The runtime is not an embedder of the public JSAPI: it compiles against the
engine's private headers (`vm/*.h`, the `-inl.h` files) and bakes object,
shape, string and script layouts into generated code. The hook surface below
is what the engine has to *do* for the tier; the private headers are what it
has to *expose*.

## 1. The hook table (`js/public/ExternalCompilerHooks.h`)

`JS::ExternalCompilerHooks` is a struct of function pointers and policy
values registered on a runtime with `JS::SetExternalCompilerHooks(rt, hooks)`
once its context exists and before any script runs (`runtime/NightHooks.cpp`
is NightMonkey's table; the shell's `contextCreated` extension point is where
it registers). The context caches the table, so a hook site is one load off
the context and a branch; there is no global. Every hook takes the
`JSContext*`; the slot-store choke, which has none of its own, reaches the
table through the object's runtime and passes the runtime's main context.
The tier may keep opaque per-context state: `newContext` creates it when a
context is initialized (or when the table is registered on a runtime whose
context already exists), `destroyContext` tears it down with the context,
and `JSContext::getExternalCompilerState()` returns it. The members, and the
engine sites that call them:

| Member | Called from |
|---|---|
| `newContext(cx)`, `destroyContext(cx, state)` | `JSContext::init`, `JS::SetExternalCompilerHooks`, `js::DestroyContext` |
| `objectDemoted(cx, obj, oldWord, why)` | every structural change to an object whose external word is nonzero: `toDictionaryMode`, `changeProperty`, `changeCustomDataPropAttributes`, `removeProperty`, `freezeOrSealProperties`, `JSObject::setFlag`, `JSObject::swap`; and a slot store that changed the word |
| `storeClearMask`, `storeNonNumberClearMask` | the slot-store choke `NativeObject::setSlot`/`initSlot`: bits cleared on any engine-path store, and additionally when the value is not a number |
| `propertyAdded(cx, obj, id, slot, nfixed)` | `NativeObject::addProperty` (both paths), `AddSlotAndCallAddPropHook`, for an object whose word is nonzero |
| `globalKeyChanged(cx, id)` | `NativeDefineProperty`, `NativeDeleteProperty` on a global object |
| `globalDataStored(cx, id, bits)` | `NativeSetExistingDataProperty` on a global object |
| `globalLexicalShadowAdded(cx, idBits)` | `InitGlobalOrEvalDeclarations`, a new global lexical binding |
| `enterScript(cx, state)` | `js::RunScript`, for a script whose external tier word is nonzero |
| `enterCall(cx, args, script, constructing)` | the interpreter's `JSOp::Call` fast path, same gate |
| `isForeignGenerator(cx, gen)`, `resumeGenerator(cx, ...)` | `JSOp::Resume`: a generator whose frame belongs to the tier |
| `traceRoots(cx, trc)` | `JSContext::trace`, on every GC including minor ones |
| `sourceAssigned(cx)` | `ScriptSource::assignSource`, the one path every compile from source text takes (skipped for an off-thread compile with no context) |
| `minConstructorThisSlots` | `JSFunction::getAllocKindForThis`, a floor on the fixed-slot estimate |
| `regexpMatch(...)` | `RegExpShared::execute`, before the engine's own matcher |

## 2. Reserved words

- **Objects**: `JSObject::externalWord()` / `setExternalWord()` /
  `offsetOfExternalWord()`, a `uintptr_t`. On 32-bit targets it takes the
  place of the alignment pad that already exists; on 64-bit the option adds
  an 8-byte word. Zeroed in `initShape`. `externalStructuralChange` and
  `externalStoreCheck` are the inline halves of the two hook families above;
  their out-of-line halves live in `vm/ExternalCompilerHooks.cpp`.
  NightMonkey's use of the bits is described in `runtime/NightObjectWord.h`.
- **Scripts**: `BaseScript::externalTierWord()` (a `uintptr_t`, zero at
  birth); the engine consults the entry hooks only for scripts whose word is
  nonzero. NightMonkey stores the indirect-table index of the compiled body.
- **RegExpShared**: `externalWord()`, a cache slot for the matcher lookup.

## 3. Behavior changes under the option

- `RegExpStatics::updateLazily`: the statics record the replay recipe
  (source, flags, index, input) instead of copying the match pairs on every
  match; the first statics read re-executes. `ExecuteRegExpImpl` uses it.
- `OptimizeStringCharOpsFuse`: a RealmFuse over `String.prototype.charAt`,
  `charCodeAt` and `String.fromCharCode`, popped by Watchtower; String's
  prototype and constructor are fuse-watched. The tier's inline char ops
  consume it.
- `DecompileArgumentFromStack` tolerates a stack whose frames are invisible
  to `FrameIter`.

## 4. Exposed internals

- `js::CreateRegExpSearchResult`, `js::SetLastIndex<false>` (RegExp.cpp),
  `js::str_charAt`, `VectorMatchPairs::externalAllocOrExpandArray`,
  `StaticStrings::unitStaticTableBase`, `irregexp::kExternalMatcherSuccess`
  / `kExternalMatcherFailure` (pinned to V8's values by `static_assert`).
- `constexpr` offset accessors (unconditional, harmless in any build):
  `JSContext::offsetOfZone/Realm`, `NativeObject::offsetOfSlots/Elements`,
  `ObjectElements::offsetOf*`, `Shape::offsetOfImmutableFlags`,
  `Scope::offsetOf*`, `ImmutableScriptData::offsetOf*`,
  `PrivateScriptData::offsetOfNGCThings`, `BaseScript::offsetOfFunction`,
  `Nursery::nurseryCellHeaderSize`.
- Three common property names (`charAt`, `charCodeAt`, `fromCharCode`).

## 5. Build products

- `dist/include-private/`: a mirror of `js/src` (source and generated
  headers, `js-confdefs.h`, `gcc_hidden.h`) and `js-build-config.json`,
  the compiler command and flags libjs was built with
  (`js/src/build/export_private_headers.py`).
- `dist/lib/`: `libjsshell.a` (the shell without `main`, with mfbt and
  mozglue folded in; `js/src/shell/lib/moz.build`), `libjs_static.a`,
  `libjsrust.a`, `libpure_virtual.a`.
- The shell gains `js::shell::ShellExtension` (`shell/jsshell.h`): extra
  options, an options-parsed callback, a context-created callback (where the
  tier registers its table), extra globals, and per-script
  compiled/executed callbacks with a "primary script" flag. `main()` is
  compiled out under `JS_SHELL_LIBRARY`.

## 6. Tests

The SpiderMonkey tree carries no test changes. NightMonkey keeps
`tests/jit-test-excludes.txt` and `tests/jstests-excludes.txt` (tests that
cannot run under the tier), passed to the harnesses' existing
`--exclude-from` / `--exclude-file` options by the AOT lane only, so the
same tests still run in the tier-off lane, and `tests/wasi-*-excludes.txt`
(tests the wasm32-wasi shell cannot run at all), applied to both lanes.
NightMonkey's own regression tests live in `tests/jit-test/`.

## 7. Porting checklist

1. Apply the `--enable-external-compiler-hooks` patch (the diff of the
   tracked branch against its base, excluding tests) to the target
   SpiderMonkey. The hook sites are the list in section 1; each is a few
   lines under `#ifdef JS_EXTERNAL_COMPILER_HOOKS`.
2. Build with the option and confirm the ordinary test suites pass with no
   table registered: the hooks must be behavior-neutral.
3. Diff `vm/Opcodes.h` against the previous engine. The compiler regenerates
   its opcode enum, lengths and stack effects from it, so structural changes
   are caught automatically; a semantic change with an unchanged signature is
   signalled by `JSOP_SEMANTICS_VERSION` in `Opcodes.h`, a monotonic counter
   the engine bumps whenever bytecode meaning changes. NightMonkey records
   the version its lowerings target in `runtime/NightOpcodeVersion.h`; the
   compiler's build script and the runtime (a `static_assert` in
   `NightOps.cpp`) refuse a mismatch, so a bump means: review
   `compiler/src/opsem.rs` and the lowerings, then raise the number.
4. Build NightMonkey against the new `dist/`. Layout drift fails at the
   `static_assert`s in `runtime/NightInlineHeap.cpp` and the layout
   descriptor check in the snapshot reader.
5. Run both jit-test lanes.
