// `map.get(k)` on a Map, inline for an atom or int32 key (the table's own
// hash, bucket and chain walk); every other key and receiver takes the call.
// Keys of every kind, absent keys, deleted entries, clears, growth (rehash),
// empty maps, a subclass, a replaced `get`, and GCs.

function get(m, k) { return m.get(k); }

var m = new Map();
var names = ["a", "bb", "aliasing", "a fat inline atom ok", "a long atom that is neither thin nor fat inline at all", "\u1234x", "\u1234\u1235\u1236\u1237\u1238\u1239y"];
for (var i = 0; i < names.length; i++) m.set(names[i], i);
for (var i = -5; i < 300; i++) m.set(i, "i" + i);
m.set(1.5, "dbl");
m.set(NaN, "nan");
var ok = {}; m.set(ok, "obj");
m.set(true, "t"); m.set(null, "n"); m.set(undefined, "u");

for (var r = 0; r < 2000; r++) {
  if (r % 400 == 0) gc();
  if (r % 97 == 0) minorgc();
  var j = r % names.length;
  assertEq(get(m, names[j]), j);
  assertEq(get(m, names[j].slice(0, -1) + names[j].slice(-1)), j);  // a run-time string
  var n = (r % 310) - 5;
  assertEq(get(m, n), n < 300 ? "i" + n : undefined);
  assertEq(get(m, n + 0.5), n == 1 ? "dbl" : undefined);
  assertEq(get(m, 3.0 + (r & 0)), "i3");
  assertEq(get(m, -0), "i0");
  assertEq(get(m, NaN), "nan");
  assertEq(get(m, ok), "obj");
  assertEq(get(m, {}), undefined);
  assertEq(get(m, true), "t");
  assertEq(get(m, null), "n");
  assertEq(get(m, undefined), "u");
  assertEq(get(m, "absent" + (r % 3)), undefined);
}
// Deletes, re-adds and clears.
for (var r = 0; r < 300; r++) {
  var k = r % 50;
  if (r % 2) m.delete(k); else m.set(k, "again" + r);
  assertEq(get(m, k), r % 2 ? undefined : "again" + r);
}
m.clear();
for (var r = 0; r < 50; r++) assertEq(get(m, r), undefined);
// Growth from empty: every rehash point.
var g = new Map();
for (var i = 0; i < 2000; i++) {
  g.set("k" + i, i);
  assertEq(get(g, "k" + (i >> 1)), i >> 1);
  assertEq(get(g, i), undefined);
}
// A subclass is a Map; a replaced get is called.
class M2 extends Map {}
var s2 = new M2([["x", 1]]);
assertEq(get(s2, "x"), 1);
var own = new Map([["x", 1]]);
own.get = function () { return "own"; };
assertEq(get(own, "x"), "own");
var orig = Map.prototype.get;
Map.prototype.get = function () { return "patched"; };
assertEq(get(new Map([["x", 1]]), "x"), "patched");
Map.prototype.get = orig;
// Not a Map.
var fake = { get(k) { return "fake " + k; } };
assertEq(get(fake, "x"), "fake x");
var threw = false;
try { orig.call(new Set(), "x"); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);
// The pristine get on an object that is not a Map, called as a method.
var notMap = Object.create(Map.prototype);
for (var r = 0; r < 100; r++) {
  var threw2 = false;
  try { get(notMap, r & 1 ? "x" : r); } catch (e) { threw2 = e instanceof TypeError; }
  assertEq(threw2, true);
}
