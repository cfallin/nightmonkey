/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */
/*
 * wasm_build.h — header-only helpers for *building* the function blobs consumed
 * by `wasm_add_funcs` (see `wasm_add.h` for the core API).
 *
 * Provides:
 *   - a tiny growable byte buffer (`wa_buf`);
 *   - a `wa_func` builder that emits a single function blob (a wasm functype
 *     followed by a wasm code body);
 *   - convenience emitters for common opcodes; and
 *   - `wa_add_funcs`, which finishes a batch of `wa_func`s and hands them to
 * the runner in one call.
 *
 * This header is optional: a project that produces blobs some other way (e.g. a
 * compiler emitting the blob format directly) only needs `wasm_add.h`.
 */
#ifndef WASM_BUILD_H
#define WASM_BUILD_H

#include "wasm_add.h"

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------ */
/* valtypes                                                            */
/* ------------------------------------------------------------------ */

typedef enum {
  WA_I32 = 0x7f,
  WA_I64 = 0x7e,
  WA_F32 = 0x7d,
  WA_F64 = 0x7c,
  WA_FUNCREF = 0x70,
  WA_EXTERNREF = 0x6f,
} wa_valtype;

/* ------------------------------------------------------------------ */
/* Growable byte buffer                                                */
/* ------------------------------------------------------------------ */

typedef struct {
  uint8_t* data;
  size_t len;
  size_t cap;
} wa_buf;

static inline void wa_buf_reserve(wa_buf* b, size_t extra) {
  if (b->len + extra <= b->cap) return;
  size_t cap = b->cap ? b->cap : 16;
  while (cap < b->len + extra) cap *= 2;
  b->data = (uint8_t*)realloc(b->data, cap);
  b->cap = cap;
}

static inline void wa_buf_u8(wa_buf* b, uint8_t x) {
  wa_buf_reserve(b, 1);
  b->data[b->len++] = x;
}

static inline void wa_buf_bytes(wa_buf* b, const void* p, size_t n) {
  wa_buf_reserve(b, n);
  memcpy(b->data + b->len, p, n);
  b->len += n;
}

static inline void wa_buf_uleb(wa_buf* b, uint64_t v) {
  do {
    uint8_t byte = v & 0x7f;
    v >>= 7;
    if (v) byte |= 0x80;
    wa_buf_u8(b, byte);
  } while (v);
}

static inline void wa_buf_sleb(wa_buf* b, int64_t v) {
  int more = 1;
  while (more) {
    uint8_t byte = v & 0x7f;
    v >>= 7; /* arithmetic shift */
    if ((v == 0 && !(byte & 0x40)) || (v == -1 && (byte & 0x40)))
      more = 0;
    else
      byte |= 0x80;
    wa_buf_u8(b, byte);
  }
}

/* ------------------------------------------------------------------ */
/* Function builder                                                    */
/* ------------------------------------------------------------------ */

typedef struct {
  wa_buf params; /* raw valtype bytes */
  int n_params;
  wa_buf results; /* raw valtype bytes */
  int n_results;
  wa_buf locals; /* encoded local runs: uleb(count) valtype, ... */
  int n_local_runs;
  wa_buf code; /* instruction bytes incl. trailing `end` */
} wa_func;

static inline void wa_func_init(wa_func* f) { memset(f, 0, sizeof(*f)); }

static inline void wa_func_free(wa_func* f) {
  free(f->params.data);
  free(f->results.data);
  free(f->locals.data);
  free(f->code.data);
  memset(f, 0, sizeof(*f));
}

static inline void wa_param(wa_func* f, wa_valtype t) {
  wa_buf_u8(&f->params, (uint8_t)t);
  f->n_params++;
}

static inline void wa_result(wa_func* f, wa_valtype t) {
  wa_buf_u8(&f->results, (uint8_t)t);
  f->n_results++;
}

/* Add `count` locals of type `t`. Locals are indexed after the parameters. */
static inline void wa_local(wa_func* f, wa_valtype t, int count) {
  wa_buf_uleb(&f->locals, (uint64_t)count);
  wa_buf_u8(&f->locals, (uint8_t)t);
  f->n_local_runs++;
}

/* Raw opcode / immediate emitters. */
static inline void wa_op(wa_func* f, uint8_t op) { wa_buf_u8(&f->code, op); }
static inline void wa_uleb(wa_func* f, uint64_t v) { wa_buf_uleb(&f->code, v); }
static inline void wa_sleb(wa_func* f, int64_t v) { wa_buf_sleb(&f->code, v); }

/* Convenience emitters for the opcodes used in the example. */
static inline void wa_local_get(wa_func* f, uint32_t i) {
  wa_op(f, 0x20);
  wa_uleb(f, i);
}
static inline void wa_local_set(wa_func* f, uint32_t i) {
  wa_op(f, 0x21);
  wa_uleb(f, i);
}
static inline void wa_local_tee(wa_func* f, uint32_t i) {
  wa_op(f, 0x22);
  wa_uleb(f, i);
}
static inline void wa_global_get(wa_func* f, uint32_t i) {
  wa_op(f, 0x23);
  wa_uleb(f, i);
}
static inline void wa_global_set(wa_func* f, uint32_t i) {
  wa_op(f, 0x24);
  wa_uleb(f, i);
}
static inline void wa_i32_const(wa_func* f, int32_t v) {
  wa_op(f, 0x41);
  wa_sleb(f, v);
}
static inline void wa_i32_add(wa_func* f) { wa_op(f, 0x6a); }
static inline void wa_i32_sub(wa_func* f) { wa_op(f, 0x6b); }
static inline void wa_i32_mul(wa_func* f) { wa_op(f, 0x6c); }
static inline void wa_i32_load(wa_func* f, uint32_t align, uint32_t off) {
  wa_op(f, 0x28);
  wa_uleb(f, align);
  wa_uleb(f, off);
}
static inline void wa_i32_store(wa_func* f, uint32_t align, uint32_t off) {
  wa_op(f, 0x36);
  wa_uleb(f, align);
  wa_uleb(f, off);
}
static inline void wa_call(wa_func* f, uint32_t fn) {
  wa_op(f, 0x10);
  wa_uleb(f, fn);
}
static inline void wa_call_indirect(wa_func* f, uint32_t type, uint32_t table) {
  wa_op(f, 0x11);
  wa_uleb(f, type);
  wa_uleb(f, table);
}
static inline void wa_drop(wa_func* f) { wa_op(f, 0x1a); }
static inline void wa_end(wa_func* f) { wa_op(f, 0x0b); }

/*
 * Serialize a finished function into a blob. The returned buffer is malloc'd;
 * the caller owns it.
 */
static inline void wa_func_finish(wa_func* f, uint8_t** out_bytes,
                                  size_t* out_len) {
  wa_buf blob = {0};
  wa_buf_u8(&blob, 0x60);
  wa_buf_uleb(&blob, (uint64_t)f->n_params);
  wa_buf_bytes(&blob, f->params.data, f->params.len);
  wa_buf_uleb(&blob, (uint64_t)f->n_results);
  wa_buf_bytes(&blob, f->results.data, f->results.len);
  wa_buf_uleb(&blob, (uint64_t)f->n_local_runs);
  wa_buf_bytes(&blob, f->locals.data, f->locals.len);
  wa_buf_bytes(&blob, f->code.data, f->code.len);
  *out_bytes = blob.data;
  *out_len = blob.len;
}

/*
 * Convenience wrapper: finish `n` functions and hand them to the runner in one
 * call. `out` must have room for `n` funcptrs.
 */
static inline wa_err wa_add_funcs(wa_func* funcs, int n, wa_funcptr* out) {
  uint8_t** bytecode = (uint8_t**)malloc((size_t)n * sizeof(uint8_t*));
  size_t* lens = (size_t*)malloc((size_t)n * sizeof(size_t));
  for (int i = 0; i < n; i++) wa_func_finish(&funcs[i], &bytecode[i], &lens[i]);
  wa_err e = wasm_add_funcs(bytecode, lens, n, out);
  for (int i = 0; i < n; i++) free(bytecode[i]);
  free(bytecode);
  free(lens);
  return e;
}

static inline wa_err wa_add_funcs2(wa_func* funcs, int n,
                                   const wa_funcptr* extern_funcs, int nextern,
                                   wa_funcptr* out) {
  uint8_t** bytecode = (uint8_t**)malloc((size_t)n * sizeof(uint8_t*));
  size_t* lens = (size_t*)malloc((size_t)n * sizeof(size_t));
  for (int i = 0; i < n; i++) wa_func_finish(&funcs[i], &bytecode[i], &lens[i]);
  wa_err e = wasm_add_funcs2(bytecode, lens, n, extern_funcs, nextern, out);
  for (int i = 0; i < n; i++) free(bytecode[i]);
  free(bytecode);
  free(lens);
  return e;
}

#endif /* WASM_BUILD_H */
