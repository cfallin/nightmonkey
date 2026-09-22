/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// The SpiderMonkey bytecode semantics version NightMonkey's lowerings were
// written for (JSOP_SEMANTICS_VERSION in vm/Opcodes.h). The engine bumps it
// on any change to what bytecode means; the compiler's build script and the
// runtime both refuse a mismatch, so a bump is the cue to review
// compiler/src/opsem.rs and the lowerings, then raise this number.
//
// The compiler regenerates its opcode enum, lengths and stack effects from
// Opcodes.h on every build, so a renumbered, added or re-arity'd opcode is
// caught without this; the version covers semantic changes those cannot
// see.

#ifndef night_runtime_NightOpcodeVersion_h
#define night_runtime_NightOpcodeVersion_h

#define NIGHT_JSOP_SEMANTICS_VERSION 1

#endif  // night_runtime_NightOpcodeVersion_h
