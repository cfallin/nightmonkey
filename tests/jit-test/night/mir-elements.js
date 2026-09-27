// MIR's dense element access (`load_elem`/`store_elem` on a native
// receiver, its guard hoisted to the loop's entry): holes, out-of-bounds
// indices, frozen elements and non-array receivers take the generic path
// or exit; overflowing and -0 products exit to doubles.
function sum(a, n) {
  var t = 0;
  for (var i = 0; i < n; i++) t += a[i] | 0;
  return t;
}
function fill(a, n, v) {
  for (var i = 0; i < n; i++) a[i] = v + i;
  return a;
}
function mul(a, b, n) {
  var r = [];
  for (var i = 0; i < n; i++) r.push(a[i] * b[i]);
  return r;
}
var a = [];
for (var i = 0; i < 100; i++) a.push(i);
for (var n = 0; n < 30; n++) {
  assertEq(sum(a, 100), 4950);
  assertEq(sum(a, 120), 4950);             // out of bounds: undefined | 0
  fill(a, 100, 0);
}
var h = [1, 2, , 4];                        // a hole
assertEq(sum(h, 4), 7);
var f = Object.freeze([1, 2, 3]);
fill(f, 3, 10);                             // frozen: no store
assertEq(f[0], 1);
assertEq(sum(new Int32Array([5, 6, 7]), 3), 18);   // a typed array
assertEq(sum("12345", 5), 15);              // a string receiver
assertEq(sum({0: 3, 1: 4}, 2), 7);          // a plain object
var g = fill(new Array(10), 10, 1);
assertEq(g[9], 10);
var big = [65536, 3, -2, 0];
var m = mul(big, [65536, 5, 0, -7], 4);
assertEq(m[0], 4294967296);
assertEq(m[1], 15);
assertEq(Object.is(m[2], -0), true);
assertEq(Object.is(m[3], -0), true);
