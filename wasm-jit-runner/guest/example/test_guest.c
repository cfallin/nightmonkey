/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */
/*
 * test_guest.c — exercises the `wasm_add_funcs` runtime-function-adding API.
 *
 * It dynamically builds three wasm functions and verifies:
 *   - basic execution + memory-independent computation (func0);
 *   - one added function directly calling another by index (func1 calls func0);
 *   - an added function reading parameters, performing an *indirect* call back
 *     into an existing guest function via table 0, and writing to the guest's
 *     linear memory (func2).
 *
 * Build (see build.sh): needs the guest headers on the include path, e.g.
 *   wasm32-wasip1-clang -I.. test_guest.c -O2 -o test_guest.wasm
 */
#include "wasm_build.h"
#include <stdint.h>
#include <stdio.h>

/*
 * An ordinary guest function that the dynamically-added code will call back
 * into, *indirectly* through table 0. Taking its address forces it into the
 * indirect function table; `used`/`noinline` keep it intact under -O2.
 */
__attribute__((noinline, used)) int host_helper(int x) { return x * x; }

/* Where func2 will store its result; address passed in as a parameter. */
volatile int g_sink = 0;

int main(void) {
  int failures = 0;

  /* ---- func0: (i32 x) -> i32 ; returns x + 100 ---------------------- */
  wa_func f0;
  wa_func_init(&f0);
  wa_param(&f0, WA_I32);
  wa_result(&f0, WA_I32);
  wa_local_get(&f0, 0);   /* x        */
  wa_i32_const(&f0, 100); /* 100      */
  wa_i32_add(&f0);        /* x + 100  */
  wa_end(&f0);

  /* ---- func1: (i32 x) -> i32 ; returns func0(x) + 1 ----------------- */
  /* Demonstrates a *direct* call (by index 0) between added functions.  */
  wa_func f1;
  wa_func_init(&f1);
  wa_param(&f1, WA_I32);
  wa_result(&f1, WA_I32);
  wa_local_get(&f1, 0); /* x            */
  wa_call(&f1, 0);      /* call func0   */
  wa_i32_const(&f1, 1);
  wa_i32_add(&f1); /* + 1          */
  wa_end(&f1);

  /*
   * ---- func2: (i32 helper, i32 x, i32 addr) -> i32 ------------------
   * r = (*helper)(x)        ; indirect call through table 0
   * *(i32*)addr = r         ; write to guest linear memory
   * return r * 2
   * Uses one i32 local (index 3) to hold r. The indirect call uses type
   * index 0, whose signature — (i32)->i32 — is func0's type.
   */
  wa_func f2;
  wa_func_init(&f2);
  wa_param(&f2, WA_I32); /* 0: helper funcptr */
  wa_param(&f2, WA_I32); /* 1: x              */
  wa_param(&f2, WA_I32); /* 2: addr           */
  wa_result(&f2, WA_I32);
  wa_local(&f2, WA_I32, 1); /* local 3: r */

  wa_local_get(&f2, 1);        /* x                          */
  wa_local_get(&f2, 0);        /* helper (table index)       */
  wa_call_indirect(&f2, 0, 0); /* call_indirect type0 table0 */
  wa_local_set(&f2, 3);        /* r = ...                    */
  wa_local_get(&f2, 2);        /* addr                       */
  wa_local_get(&f2, 3);        /* r                          */
  wa_i32_store(&f2, 2, 0);     /* *(i32*)addr = r            */
  wa_local_get(&f2, 3);        /* r                          */
  wa_i32_const(&f2, 2);
  wa_i32_mul(&f2); /* r * 2                      */
  wa_end(&f2);

  wa_func funcs[3] = {f0, f1, f2};
  wa_funcptr ptr[3];
  wa_err err = wa_add_funcs(funcs, 3, ptr);
  if (err != 0) {
    printf("wasm_add_funcs failed with err=%d\n", err);
    return 1;
  }
  printf("added 3 functions, funcptrs = %d, %d, %d\n", ptr[0], ptr[1], ptr[2]);

  /* Call the freshly-added functions through their funcptrs. */
  int (*fn0)(int) = (int (*)(int))(intptr_t)ptr[0];
  int (*fn1)(int) = (int (*)(int))(intptr_t)ptr[1];
  int (*fn2)(int, int, int) = (int (*)(int, int, int))(intptr_t)ptr[2];

  int r0 = fn0(5);
  printf("func0(5)            = %d (expect 105)\n", r0);
  failures += (r0 != 105);

  int r1 = fn1(5);
  printf("func1(5)            = %d (expect 106)\n", r1);
  failures += (r1 != 106);

  int helper_idx = (int)(intptr_t)(void*)&host_helper;
  int addr = (int)(intptr_t)(void*)&g_sink;
  int r2 = fn2(helper_idx, 7, addr);
  printf("func2(helper,7,&sink)= %d (expect 98)\n", r2);
  printf("g_sink              = %d (expect 49)\n", g_sink);
  failures += (r2 != 98);
  failures += (g_sink != 49);

  /*
   * ---- func3 (wasm_add_funcs2): (i32 x) -> i32 ----------------------
   * Direct-calls IMPORTED function 0 (host_helper, resolved by the host
   * from its table-0 index) and adds 1000: returns host_helper(x) + 1000.
   * Also checks the wasm_table_size index-prediction contract: the blob's
   * funcptr must equal the pre-call table size.
   */
  int base = wasm_table_size();
  printf("table size          = %d (expect > 0)\n", base);
  failures += (base <= 0);

  wa_func f3;
  wa_func_init(&f3);
  wa_param(&f3, WA_I32);
  wa_result(&f3, WA_I32);
  wa_local_get(&f3, 0); /* x                     */
  wa_call(&f3, 0);      /* call imported helper  */
  wa_i32_const(&f3, 1000);
  wa_i32_add(&f3);
  wa_end(&f3);

  wa_func funcs2[1] = {f3};
  wa_funcptr externs[1] = {(wa_funcptr)(intptr_t)(void*)&host_helper};
  wa_funcptr ptr3[1];
  err = wa_add_funcs2(funcs2, 1, externs, 1, ptr3);
  if (err != 0) {
    printf("wasm_add_funcs2 failed with err=%d\n", err);
    return 1;
  }
  printf("func3 funcptr       = %d (expect %d, predicted)\n", ptr3[0], base);
  failures += (ptr3[0] != base);

  int (*fn3)(int) = (int (*)(int))(intptr_t)ptr3[0];
  int r3 = fn3(6);
  printf("func3(6)            = %d (expect 1036)\n", r3);
  failures += (r3 != 1036);

  if (failures == 0) {
    printf("ALL TESTS PASSED\n");
    return 0;
  }
  printf("%d CHECK(S) FAILED\n", failures);
  return 1;
}
