# NightMonkey: an AOT compiler from JavaScript to Wasm, layered on top of
# SpiderMonkey. This build consumes the dist/ directory of a SpiderMonkey
# build made with --enable-external-compiler-hooks (spidermonkey/mozconfig):
# its private headers, the compile flags libjs was built with
# (include-private/js-build-config.json) and the archives under lib/.
#
#   cmake -S . -B build -DSPIDERMONKEY_DIST=/path/to/firefox/obj-nightmonkey-sm/dist
#   cmake --build build
#
# Produces, under build/bin:
#   js               the NightMonkey wasm shell (the snapshot flow's shell)
#   js-inproc        the same shell with the in-process compiler linked in
#                    (the test lane; NIGHT_INPROCESS)
#   nightmonkey      the host AOT compiler (snapshot in, module out)
#   wasm-jit-runner  the host that runs the in-process test lane
#   inproc-shell.sh  the shell wrapper the test harnesses use

cmake_minimum_required(VERSION 3.20)

set(SPIDERMONKEY_DIST "" CACHE PATH
    "dist/ directory of a SpiderMonkey build with --enable-external-compiler-hooks")
option(NIGHT_INPROCESS "Build the in-process test lane (guest compiler, wasm-jit-runner)" ON)
option(NIGHT_DEBUG "Runtime diagnostics and crash-on-failure in the in-process lane" OFF)
set(NIGHT_CARGO "cargo" CACHE STRING "cargo executable")
set(NIGHT_STACK_SIZE "67108864" CACHE STRING "linear-memory stack size of the shells, in bytes")
set(NIGHT_CARGO_TARGET_DIR "" CACHE PATH "cargo target directory (default: <build>/cargo; share it between build trees)")

if(NOT SPIDERMONKEY_DIST)
  message(FATAL_ERROR "SPIDERMONKEY_DIST is required: the dist/ directory of a SpiderMonkey build made with --enable-external-compiler-hooks (see spidermonkey/mozconfig)")
endif()
get_filename_component(SPIDERMONKEY_DIST "${SPIDERMONKEY_DIST}" ABSOLUTE)
set(SM_CONFIG_JSON "${SPIDERMONKEY_DIST}/include-private/js-build-config.json")
if(NOT EXISTS "${SM_CONFIG_JSON}")
  message(FATAL_ERROR "${SM_CONFIG_JSON} not found: is this a --enable-external-compiler-hooks build?")
endif()
file(READ "${SM_CONFIG_JSON}" SM_JSON)

function(sm_json_list out key)
  string(JSON n LENGTH "${SM_JSON}" ${key})
  set(result)
  if(n GREATER 0)
    math(EXPR last "${n} - 1")
    foreach(i RANGE ${last})
      string(JSON v GET "${SM_JSON}" ${key} ${i})
      list(APPEND result "${v}")
    endforeach()
  endif()
  set(${out} "${result}" PARENT_SCOPE)
endfunction()

# The compiler command lines libjs was built with: the executable plus the
# sysroot, standard and target flags.
string(JSON SM_CXX_CMD GET "${SM_JSON}" cxx)
string(JSON SM_CC_CMD GET "${SM_JSON}" cc)
separate_arguments(SM_CXX_CMD NATIVE_COMMAND "${SM_CXX_CMD}")
separate_arguments(SM_CC_CMD NATIVE_COMMAND "${SM_CC_CMD}")
list(GET SM_CXX_CMD 0 SM_CXX)
list(GET SM_CC_CMD 0 SM_CC)
list(REMOVE_AT SM_CXX_CMD 0)
list(REMOVE_AT SM_CC_CMD 0)
sm_json_list(SM_OS_CXXFLAGS os_cxxflags)
sm_json_list(SM_OPTIMIZE_FLAGS optimize_flags)
sm_json_list(SM_DEBUG_FLAGS debug_flags)
sm_json_list(SM_EXTRA_CXXFLAGS extra_cxxflags)
sm_json_list(SM_DEBUG_DEFINES debug_defines)
sm_json_list(SM_LIBRARY_DEFINES library_defines)
sm_json_list(SM_FORCE_INCLUDES force_includes)
sm_json_list(SM_INCLUDE_DIRS include_dirs)
sm_json_list(SM_LIBRARIES libraries)
string(JSON SM_RUST_TARGET GET "${SM_JSON}" rust_target)
string(JSON SM_OS_ARCH GET "${SM_JSON}" os_arch)

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR wasm32)
set(CMAKE_C_COMPILER "${SM_CC}")
set(CMAKE_CXX_COMPILER "${SM_CXX}")
set(CMAKE_C_COMPILER_WORKS TRUE)
set(CMAKE_CXX_COMPILER_WORKS TRUE)
set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)
set(CMAKE_EXECUTABLE_SUFFIX "")

project(nightmonkey C CXX)

# Every engine-facing TU is compiled exactly as libjs was: same sysroot,
# standard, target, ABI-affecting flags, defines and force-included
# configuration headers, so the private headers describe the same layouts.
set(NIGHT_CXX_FLAGS ${SM_CXX_CMD} ${SM_OS_CXXFLAGS} ${SM_OPTIMIZE_FLAGS}
    ${SM_DEBUG_FLAGS} ${SM_EXTRA_CXXFLAGS})
set(NIGHT_DEFINES ENABLE_JS_NIGHTMONKEY=1)
foreach(d ${SM_DEBUG_DEFINES})
  list(APPEND NIGHT_DEFINES "${d}=1")
endforeach()
foreach(d ${SM_LIBRARY_DEFINES})
  list(APPEND NIGHT_DEFINES "${d}")
endforeach()
if(NIGHT_DEBUG)
  list(APPEND NIGHT_DEFINES NIGHTMONKEY_DEBUG=1)
endif()
set(NIGHT_INCLUDE_DIRS "${CMAKE_SOURCE_DIR}")
foreach(d ${SM_INCLUDE_DIRS})
  list(APPEND NIGHT_INCLUDE_DIRS "${SPIDERMONKEY_DIST}/${d}")
endforeach()
set(NIGHT_FORCE_INCLUDE_FLAGS)
foreach(h ${SM_FORCE_INCLUDES})
  # SHELL: keeps CMake from de-duplicating the repeated -include.
  list(APPEND NIGHT_FORCE_INCLUDE_FLAGS "SHELL:-include ${SPIDERMONKEY_DIST}/include-private/${h}")
endforeach()

function(night_engine_target name)
  target_compile_options(${name} PRIVATE ${NIGHT_CXX_FLAGS} ${NIGHT_FORCE_INCLUDE_FLAGS}
      -Wall -Wno-invalid-offsetof -Wno-unused-private-field)
  target_compile_definitions(${name} PRIVATE ${NIGHT_DEFINES})
  target_include_directories(${name} PRIVATE ${NIGHT_INCLUDE_DIRS})
endfunction()

# The in-process sources are compiled into the runtime archive but only pulled
# into a shell that references them (js-inproc); the snapshot shell stays free
# of the runner's hostcall imports.
function(night_inprocess_target name)
  target_compile_definitions(${name} PRIVATE ENABLE_JS_NIGHTMONKEY_INPROCESS=1)
endfunction()

# --- the night runtime -------------------------------------------------------
set(NIGHT_RUNTIME_SOURCES
    runtime/NightEntry.cpp
    runtime/NightGenerator.cpp
    runtime/NightHooks.cpp
    runtime/NightInlineCaches.cpp
    runtime/NightInlineHeap.cpp
    runtime/NightOps.cpp
    runtime/NightRegExp.cpp
    runtime/NightRegistration.cpp
    runtime/NightRuntime.cpp
    runtime/NightRuntimeSlots.cpp
    runtime/NightSnapshotExtras.cpp
    runtime/NightStack.cpp)
if(NIGHT_INPROCESS)
  list(APPEND NIGHT_RUNTIME_SOURCES runtime/NightInproc.cpp runtime/NightInprocHost.cpp)
endif()
add_library(night_runtime STATIC ${NIGHT_RUNTIME_SOURCES})
night_engine_target(night_runtime)
if(NIGHT_INPROCESS)
  night_inprocess_target(night_runtime)
endif()

# --- cargo-built pieces ----------------------------------------------------------
set(CARGO_TARGET_DIR "${CMAKE_BINARY_DIR}/cargo")
if(NIGHT_CARGO_TARGET_DIR)
  set(CARGO_TARGET_DIR "${NIGHT_CARGO_TARGET_DIR}")
endif()
set(CARGO_ENV "CARGO_TARGET_DIR=${CARGO_TARGET_DIR}" "SPIDERMONKEY_DIST=${SPIDERMONKEY_DIST}")
set(NIGHT_BIN_DIR "${CMAKE_BINARY_DIR}/bin")
file(MAKE_DIRECTORY "${NIGHT_BIN_DIR}")

# The host AOT compiler (snapshot in, module out) with wizer driving built in.
add_custom_target(nightmonkey_host ALL
  COMMAND ${CMAKE_COMMAND} -E env ${CARGO_ENV} RUSTFLAGS=-Cdebuginfo=0
          ${NIGHT_CARGO} build --release -p nightmonkey --features wizen
  COMMAND ${CMAKE_COMMAND} -E copy_if_different
          "${CARGO_TARGET_DIR}/release/nightmonkey" "${NIGHT_BIN_DIR}/nightmonkey"
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  BYPRODUCTS "${NIGHT_BIN_DIR}/nightmonkey"
  COMMENT "cargo: nightmonkey (host)"
  VERBATIM)

if(NIGHT_INPROCESS)
  # The guest compiler: night-compiler and night-snapshot as one staticlib
  # for the shell's target, linked into the shell next to libjsrust.a.
  set(NIGHT_GUEST_LIB "${CARGO_TARGET_DIR}/${SM_RUST_TARGET}/release/libnight_guest.a")
  add_custom_target(night_guest ALL
    COMMAND ${CMAKE_COMMAND} -E env ${CARGO_ENV} RUSTFLAGS=-Cdebuginfo=0
            ${NIGHT_CARGO} build --release -p night-guest --target ${SM_RUST_TARGET}
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
    BYPRODUCTS "${NIGHT_GUEST_LIB}"
    COMMENT "cargo: night-guest (${SM_RUST_TARGET})"
    VERBATIM)

  # The host that runs the in-process lane (hostcalls that inject compiled
  # bodies into the running shell instance).
  add_custom_target(wasm_jit_runner ALL
    COMMAND ${CMAKE_COMMAND} -E env ${CARGO_ENV} RUSTFLAGS=-Cdebuginfo=0
            ${NIGHT_CARGO} build --release -p wasm-jit-runner
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
            "${CARGO_TARGET_DIR}/release/wasm-jit-runner" "${NIGHT_BIN_DIR}/wasm-jit-runner"
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
    BYPRODUCTS "${NIGHT_BIN_DIR}/wasm-jit-runner"
    COMMENT "cargo: wasm-jit-runner (host)"
    VERBATIM)
endif()

# --- the shells --------------------------------------------------------------------
set(NIGHT_SM_LIBS)
foreach(l ${SM_LIBRARIES})
  list(APPEND NIGHT_SM_LIBS "${SPIDERMONKEY_DIST}/${l}")
endforeach()

# Links a NightMonkey shell: the runtime, SpiderMonkey's shell/engine
# archives and the libs. The memory and funcref table are exported (and the
# table growable) so appended and injected code can share them; the deep
# stack is for the in-process compiler's lowering, which recurses on the main
# stack. The linker driver needs the same sysroot/target as the compiler.
function(night_shell name)
  add_executable(${name} shell/nightshell.cpp)
  night_engine_target(${name})
  target_include_directories(${name} PRIVATE "${CMAKE_SOURCE_DIR}/third_party/wizer")
  set_target_properties(${name} PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${NIGHT_BIN_DIR}")
  target_link_libraries(${name} PRIVATE night_runtime ${NIGHT_SM_LIBS} ${ARGN} m)
  target_link_options(${name} PRIVATE ${SM_CXX_CMD}
      -Wl,-z,stack-size=${NIGHT_STACK_SIZE} -Wl,--stack-first
      -Wl,--export-memory -Wl,--export-table -Wl,--growable-table
      -lwasi-emulated-process-clocks -lwasi-emulated-getpid)
endfunction()

# The snapshot flow's shell: what `nightmonkey --shell` wizens.
night_shell(js)

if(NIGHT_INPROCESS)
  # The test lane's shell, with the guest compiler linked in. Two Rust static
  # libraries meet here: SpiderMonkey's libjsrust.a, whose LTO-merged object
  # carries its own copy of std's unmangled runtime symbols
  # (rust_eh_personality, the panic and allocator shims), and the guest
  # compiler with the prebuilt std. The first definition wins and every copy
  # routes through the same allocator shim.
  night_shell(js-inproc "${NIGHT_GUEST_LIB}")
  night_inprocess_target(js-inproc)
  add_dependencies(js-inproc night_guest)
  target_link_options(js-inproc PRIVATE -Wl,--allow-multiple-definition)

  # The harness wrapper: runs js-inproc under wasm-jit-runner.
  configure_file(scripts/inproc-shell.sh.in "${NIGHT_BIN_DIR}/inproc-shell.sh" @ONLY)
  file(CHMOD "${NIGHT_BIN_DIR}/inproc-shell.sh" PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE GROUP_READ GROUP_EXECUTE WORLD_READ WORLD_EXECUTE)
endif()
