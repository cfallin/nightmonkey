// A for-in's steps (`more`, `end`) in compiled code: keys in order, deleted
// ones skipped, the iterator closed on every way out of the loop (normal
// exit, break, return, throw) so the engine's cached iterator is reused
// clean, nested loops over the same object, null/undefined (the shared
// empty iterator), arrays, prototypes, and GCs, incremental marking among
// them (the close then takes the helper).

function keys(o) { var r = []; for (var k in o) r.push(k); return r.join(); }
function firstTwo(o) { var r = []; for (var k in o) { r.push(k); if (r.length == 2) break; } return r.join(); }
function findKey(o, want) { for (var k in o) if (k == want) return k; return null; }
function throwAt(o, at) { try { for (var k in o) if (k == at) throw k; } catch (e) { return "caught " + e; } return "none"; }
function nested(o) { var n = 0; for (var a in o) for (var b in o) n++; return n; }
function deleting(o) { var r = []; for (var k in o) { r.push(k); delete o[k == "a" ? "c" : "zz"]; } return r.join(); }
function adding(o) { var r = []; for (var k in o) { r.push(k); o["n" + r.length] = 1; } return r.join(); }

function P() { this.own1 = 1; this.own2 = 2; }
P.prototype.inherited = 3;
var hasMarking = typeof startgc === "function" && typeof gcstate === "function";

for (var r = 0; r < 600; r++) {
  if (r % 100 == 0) gc();
  if (r % 37 == 0) minorgc();
  if (hasMarking && r % 150 == 75) startgc(1);
  var o = { a: 1, b: 2, c: 3, d: 4 };
  assertEq(keys(o), "a,b,c,d");
  assertEq(firstTwo(o), "a,b");
  assertEq(keys(o), "a,b,c,d");
  assertEq(findKey(o, "c"), "c");
  assertEq(findKey(o, "q"), null);
  assertEq(throwAt(o, "b"), "caught b");
  assertEq(throwAt(o, "x"), "none");
  assertEq(nested(o), 16);
  assertEq(keys(null), "");
  assertEq(keys(undefined), "");
  assertEq(keys([5, 6, 7]), "0,1,2");
  assertEq(keys(new String("hi")), "0,1");
  assertEq(keys(new P()), "own1,own2,inherited");
  assertEq(deleting({ a: 1, b: 2, c: 3, d: 4 }), "a,b,d");
  assertEq(adding({ a: 1, b: 2 }), "a,b");
  var big = {};
  for (var i = 0; i < 40; i++) big["k" + i] = i;
  var s = 0;
  for (var k in big) s += big[k];
  assertEq(s, 780);
}
if (hasMarking) finishgc();
