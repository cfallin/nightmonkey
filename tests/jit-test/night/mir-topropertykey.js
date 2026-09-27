// MIR's ToPropertyKey (compound element assignment, `o[k] += v`): an
// int32, string or symbol key is itself; anything else goes through the
// runtime, which may run user code (a key object's toString).
function bump(o, k, d) { o[k] += d; return o[k]; }
var calls = 0;
var keyObj = { toString: function () { calls++; return "p"; } };
var o = { p: 1, 2: 10, "1.5": 100 };
var sym = Symbol("s");
o[sym] = 7;
for (var n = 0; n < 40; n++) {
  assertEq(bump(o, 2, 1), 11 + n);
  assertEq(bump(o, "p", 1), 2 + 2 * n);
  assertEq(bump(o, keyObj, 1), 3 + 2 * n);
  assertEq(bump(o, 1.5, 1), 101 + n);
  assertEq(bump(o, sym, 1), 8 + n);
}
assertEq(calls, 80);
var thrower = { toString: function () { throw "boom"; } };
var caught = null;
try { bump(o, thrower, 1); } catch (e) { caught = e; }
assertEq(caught, "boom");
