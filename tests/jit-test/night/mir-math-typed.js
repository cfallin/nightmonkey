// `Math.<fn>(...)` as typed MIR ops: behind a check that the callee is
// the pristine native and that the arguments are numbers (a miss runs the
// call in baseline), the result is a raw f64. Edge values (-0, NaN,
// infinities, int32 bounds), non-number arguments, and a replaced
// `Math.floor` must all behave as the builtins do.

function f1(x) {
  return Math.floor(x) + Math.ceil(x) + Math.trunc(x) + Math.abs(x) + Math.sqrt(Math.abs(x)) + Math.fround(x);
}
function f2(x, y) { return Math.min(x, y) * 3 + Math.max(x, y) + Math.pow(x, y); }
function trig(x) { return Math.sin(x) * Math.sin(x) + Math.cos(x) * Math.cos(x); }
function negZero(x) { return 1 / Math.min(x, -0) + 1 / Math.max(-0, x); }
function idx(a, x) { return a[Math.floor(x / 2)]; }
function floorOf(x) { return Math.floor(x); }

var a = [10, 11, 12, 13, 14, 15, 16, 17];
for (var n = 0; n < 300; n++) {
  var x = n / 7 - 20;
  var expect1 = Math.floor(x) + Math.ceil(x) + Math.trunc(x) + Math.abs(x) + Math.sqrt(Math.abs(x)) + Math.fround(x);
  assertEq(f1(x), expect1);
  assertEq(f1(n), n + n + n + n + Math.sqrt(n) + n);
  assertEq(f2(n % 5, 2), Math.min(n % 5, 2) * 3 + Math.max(n % 5, 2) + (n % 5) * (n % 5));
  assertEq(Math.abs(trig(x) - 1) < 1e-12, true);
  assertEq(negZero(0), NaN);
  assertEq(negZero(1), -Infinity + 1);
  assertEq(idx(a, n % 16), a[Math.floor((n % 16) / 2)]);
  assertEq(floorOf(-0.5), -1);
  assertEq(Object.is(floorOf(-0), -0), true);
  assertEq(Number.isNaN(floorOf(NaN)), true);
  assertEq(floorOf(2147483648.5), 2147483648);
  assertEq(Math.min(NaN, 1) !== Math.min(NaN, 1), true);
}
// Non-number arguments: the builtins' coercions.
for (var n = 0; n < 50; n++) {
  assertEq(floorOf("3.7"), 3);
  assertEq(Number.isNaN(floorOf(undefined)), true);
  assertEq(floorOf(null), 0);
  assertEq(floorOf({ valueOf: function () { return 8.5; } }), 8);
  assertEq(f2("2", "3"), 2 * 3 + 3 + 8);
}
// A replaced native: the call is the replacement's.
var orig = Math.floor;
Math.floor = function (v) { return "patched" + v; };
assertEq(floorOf(1.5), "patched1.5");
Math.floor = orig;
assertEq(floorOf(1.5), 1);
