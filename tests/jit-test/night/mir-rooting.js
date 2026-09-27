// MIR's rooting under frequent GCs: managed values stored once to their
// home slot before the first may-GC call they are live across, kept there
// across repeated calls and loops, and reloaded where next used; merges of
// a helper's slow path with a fast arm; values that enter a loop only in
// their slot.
// `mk` and `id` collect the nursery every so often (when `stress` is
// set), so a caller's register copy of an object it made is stale after
// the call unless it was reloaded from its root.
var stress = false, tick = 0;
function gcSometimes() { if (stress && (++tick % 3) == 0) minorgc(); }
function mk(i) { var o = { i: i, s: "s" + i }; gcSometimes(); return o; }
function id(x) { gcSometimes(); return x; }
function twoCalls(a, b) {
  var o = mk(a);
  var p = mk(b);
  var q = id(o);
  var r = mk(a + b);
  return q.i + p.i + r.i + o.s.length + p.s.length;
}
function loopCalls(n) {
  var keep = mk(-1), acc = 0, arr = [];
  for (var i = 0; i < n; i++) {
    var t = mk(i);
    arr.push(t);
    acc += keep.i + t.i + id(t).s.length;
  }
  return acc + arr.length + arr[n - 1].i + keep.s.length;
}
function branchy(o, flag) {
  var x = flag ? mk(1) : o;
  var y = id(x);
  if (flag) y = mk(y.i + 1);
  return x.i + y.i + o.i;
}
// Identity: the global's copy is updated by the GC; a stale register copy
// would compare unequal (a moved object's old copy still reads the same).
var seen = [];
function identity(k) {
  var o = mk(k), p = mk(k + 1);
  seen[0] = o; seen[1] = p;
  var q = id(p), r = mk(k + 2);
  for (var j = 0; j < 3; j++) r = id(mk(j));
  return (o === seen[0]) + (p === seen[1]) + (q === p) + r.i;
}
function viaGetter(o) {
  // A property get whose slow path runs a getter that allocates.
  var a = o.g, b = o.g, c = mk(3);
  return a.i + b.i + c.i + o.k.i;
}
var withGetter = { k: mk(9) };
Object.defineProperty(withGetter, "g", { get: function () { return mk(7); } });
function run() {
  for (var n = 0; n < 60; n++) {
    assertEq(twoCalls(n, 2), n + 2 + n + 2 + ("s" + n).length + 2);
    // keep.i x20, 0..19, "s0".."s19" lengths, length, last, "s-1".length
    assertEq(loopCalls(20), -20 + 190 + 50 + 20 + 19 + 3);
    assertEq(branchy(mk(5), n & 1), (n & 1) ? 1 + 2 + 5 : 15);
    assertEq(viaGetter(withGetter), 7 + 7 + 3 + 9);
    assertEq(identity(n), 3 + 2);
  }
}
run();
stress = true;
run();
stress = false;
gczeal(7, 3);
run();
gczeal(0);

// Retention matches baseline's frame: a local's value stays alive until
// the local is overwritten, even where it is dead, and no longer after;
// including across a GC inside an inlined callee.
function collect() { gc(); }
function released() {
  gc();
  var o = makeFinalizeObserver();
  var c0 = finalizeCount();
  o = undefined;
  collect();
  return finalizeCount() - c0;
}
function retained() {
  gc();
  var o = makeFinalizeObserver();
  var c0 = finalizeCount();
  collect();
  return finalizeCount() - c0;
}
for (var n = 0; n < 40; n++) {
  assertEq(released(), 1);
  assertEq(retained(), 0);
}
