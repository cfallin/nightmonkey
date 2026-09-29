// `hasOwnProperty.call(o, k)` at a site the analysis resolved to the
// builtin runs the HasOwn op directly behind identity checks of `.call`
// and the target; a replaced `hasOwnProperty` (or `.call`) takes the
// generic call. And a double stored into an array whose elements admit
// doubles goes in as a double, integral or not: its readers, integer
// consumers included, see the same number.

var hop = Object.prototype.hasOwnProperty;
function count(o, keys) {
  var n = 0;
  for (var i = 0; i < keys.length; i++)
    if (hop.call(o, keys[i])) n++;
  return n;
}
var o = { a: 1, b: 2, c: 3 }, keys = ["a", "x", "b", "y", "c", "toString"];
for (var r = 0; r < 300; r++) assertEq(count(o, keys), 3);
hop = function (k) { return k === "x"; };
for (var r = 0; r < 50; r++) assertEq(count(o, keys), 1);
hop = Object.prototype.hasOwnProperty;
var realCall = Function.prototype.call;
Function.prototype.call = function (self, k) { return k === "y"; };
for (var r = 0; r < 50; r++) assertEq(count(o, keys), 1);
Function.prototype.call = realCall;
for (var r = 0; r < 50; r++) assertEq(count(o, keys), 3);

function scale(x, x0, a, n) {
  for (var i = 1; i < n; i++) x[i] = (x0[i] + a * x[i - 1]) * 0.5;
}
function sumInts(x, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s = (s + (x[i] | 0)) | 0;
  return s;
}
function run() {
  var n = 64, x = new Array(n), x0 = new Array(n);
  for (var i = 0; i < n; i++) { x[i] = 0; x0[i] = (i % 3) * 2; }
  for (var r = 0; r < 200; r++) {
    scale(x, x0, 0, n);
    // (i % 3) * 2 * 0.5: integral doubles, stored as doubles.
    for (var i = 1; i < n; i++) {
      assertEq(x[i], i % 3);
      assertEq(x[i] === (i % 3), true);
    }
    assertEq(sumInts(x, n), 63);
    scale(x, x0, 0.25, n);
    assertEq(x[1] > 0, true);
  }
}
run();
function storeNaN(a, v) { a[1] = v * 1.5; }
function runNaN() {
  var nan = [0.5, 0.5];
  for (var r = 0; r < 200; r++) storeNaN(nan, r);
  storeNaN(nan, NaN);
  assertEq(nan[1] !== nan[1], true);
  storeNaN(nan, -0);
  assertEq(1 / nan[1], -Infinity);
}
runNaN();
