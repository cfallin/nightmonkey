// MIR's typed-array element access (`load_ta`/`store_ta` on a receiver
// proven of its kind, the guard hoisted to the loop's entry): every kind's
// loads and stores, out-of-bounds indices (the generic op), a receiver of
// another kind (an exit), NaN payloads read as the canonical NaN.
function sum_u(a, n) { var t = 0; for (var i = 0; i < n; i++) t += a[i]; return t; }
function fill_u(a, n, v) { for (var i = 0; i < n; i++) a[i] = v + i; return a; }
function fillD_u(a, n, v) { for (var i = 0; i < n; i++) a[i] = v * i; return a; }
function sum_s(a, n) { var t = 0; for (var i = 0; i < n; i++) t += a[i]; return t; }
function fill_s(a, n, v) { for (var i = 0; i < n; i++) a[i] = v + i; return a; }
function fillD_s(a, n, v) { for (var i = 0; i < n; i++) a[i] = v * i; return a; }
function sum_w(a, n) { var t = 0; for (var i = 0; i < n; i++) t += a[i]; return t; }
function fill_w(a, n, v) { for (var i = 0; i < n; i++) a[i] = v + i; return a; }
function fillD_w(a, n, v) { for (var i = 0; i < n; i++) a[i] = v * i; return a; }
function sum_d(a, n) { var t = 0; for (var i = 0; i < n; i++) t += a[i]; return t; }
function fill_d(a, n, v) { for (var i = 0; i < n; i++) a[i] = v + i; return a; }
function fillD_d(a, n, v) { for (var i = 0; i < n; i++) a[i] = v * i; return a; }
function sum_f(a, n) { var t = 0; for (var i = 0; i < n; i++) t += a[i]; return t; }
function fill_f(a, n, v) { for (var i = 0; i < n; i++) a[i] = v + i; return a; }
function fillD_f(a, n, v) { for (var i = 0; i < n; i++) a[i] = v * i; return a; }
for (var r = 0; r < 30; r++) {
  var u8 = fill_u(new Uint8Array(16), 16, 250);       // wraps past 255
  assertEq(u8[5], 255);
  assertEq(u8[6], 0);
  assertEq(sum_u(u8, 16), 250 + 251 + 252 + 253 + 254 + 255 + 45);
  var i8 = fill_s(new Int8Array(8), 8, 125);
  assertEq(i8[3], -128);
  assertEq(sum_s(i8, 8), 125 + 126 + 127 - 128 - 127 - 126 - 125 - 124);
  var i32 = fill_w(new Int32Array(10), 10, 1 << 30);
  assertEq(sum_w(i32, 10), 10 * (1 << 30) + 45);
  var f64 = fillD_d(new Float64Array(10), 10, 0.5);
  assertEq(sum_d(f64, 10), 22.5);
  var f32 = fillD_f(new Float32Array(4), 4, 0.1);
  assertEq(f32[1], Math.fround(0.1));
  assertEq(sum_f(f32, 4), Math.fround(0) + Math.fround(0.1) + Math.fround(0.2) + Math.fround(0.30000000000000004));
}
assertEq(sum_d(f64, 12), NaN);                       // out of bounds: undefined
fill_w(i32, 12, 0);                                  // out of bounds: ignored
assertEq(i32.length, 10);
assertEq(sum_u(new Int16Array([1, 2, 3]), 3), 6);    // another kind: an exit
assertEq(sum_u([1, 2, 3], 3), 6);                    // an array
var nan = new Float64Array(new Uint32Array([1, 0x7ff80001]).buffer);
assertEq(sum_d(nan, 1), NaN);
var c = new Uint8ClampedArray(4);
fill_u(c, 4, 254);                                   // clamped: an exit
assertEq(c[3], 255);
