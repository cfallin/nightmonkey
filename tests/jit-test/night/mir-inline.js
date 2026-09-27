// MIR inlining (`--pipeline mir`, docs/MIR.md §5.5): a call whose
// predicted targets are small scripts runs their MIR in place, guarded on
// the callee's script. An exit inside the inlined code finishes the callee
// in its baseline body and continues the caller; exceptions propagate.
function add(a, b) { return a + b; }
function sumTo(n) { var t = 0; for (var i = 0; i < n; i++) t = add(t, i); return t; }
assertEq(sumTo(1000), 499500);
// The inlined add sees strings (an exit inside it), then numbers again.
function mixed(n) {
  var t = 0;
  for (var i = 0; i < n; i++) t = add(t, i == 500 ? "x" : i);
  return t;
}
var m = mixed(1000);
assertEq(typeof m, "string");
assertEq(m.slice(0, 6), "124750");
assertEq(sumTo(10), 45);

// Missing and extra arguments, and `this`.
function pair(a, b) { return [a, b]; }
function callPair(n) { var r; for (var i = 0; i < n; i++) r = pair(i); return r; }
assertEq(String(callPair(10)), "9,");
function extra(n) { var r = 0; for (var i = 0; i < n; i++) r += add(i, 1, 99, 100); return r; }
assertEq(extra(10), 55);
var obj = { k: 3, get(x) { return this.k * x; } };
function useThis(o, n) { var t = 0; for (var i = 0; i < n; i++) t += o.get(i); return t; }
assertEq(useThis(obj, 10), 135);

// A throw inside the inlined callee, caught by the caller.
function check(x) { if (x > 90) throw new RangeError("big " + x); return x; }
function guarded(n) {
  var t = 0;
  for (var i = 0; i < n; i++) {
    try { t += check(i); } catch (e) { t -= 1000; }
  }
  return t;
}
assertEq(guarded(100), 4095 - 9000);
function unguarded(n) { var t = 0; for (var i = 0; i < n; i++) t += check(i); return t; }
var threw = null;
try { unguarded(95); } catch (e) { threw = e.message; }
assertEq(threw, "big 91");

// Polymorphic sites (several targets), and a site whose callee changes.
function f1(x) { return x + 1; }
function f2(x) { return x * 2; }
function f3(x) { return x - 3; }
function poly(fs, n) { var t = 0; for (var i = 0; i < n; i++) t += fs[i % fs.length](i); return t; }
assertEq(poly([f1, f2, f3], 30), 145 + 290 + 125);
var fns = [f1, f2];
function viaVar(n) { var t = 0; for (var i = 0; i < n; i++) t += fns[i & 1](i); return t; }
assertEq(viaVar(10), 25 + 50);
fns[1] = function (x) { return -x; };
assertEq(viaVar(10), 25 - 25);

// Closures over the caller's scope, and a GC while inlined code runs.
function makeCounter() {
  var c = 0;
  return function bump(d) { c += d; if (c % 100 == 0) gc(); return c; };
}
var bump = makeCounter();
function bumps(n) { var r; for (var i = 0; i < n; i++) r = bump(1); return r; }
assertEq(bumps(1000), 1000);
function holder(n) {
  var keep = { v: 1 };
  var t = 0;
  for (var i = 0; i < n; i++) { t += bump(0) * 0 + keep.v; }
  return t;
}
assertEq(holder(50), 50);

// Recursion (not inlined into itself), and an inlined callee that calls.
function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
assertEq(fib(20), 6765);
function twice(x) { return add(x, x); }
function nested(n) { var t = 0; for (var i = 0; i < n; i++) t += twice(i); return t; }
assertEq(nested(100), 9900);
