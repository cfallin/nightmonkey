"use strict";
// MIR's generic ops (`--pipeline mir`): global reads, property and element
// access, calls, `let` bindings and constant compares, through the runtime
// helpers. Managed values live across each call must survive a GC in the
// callee (the lowering roots them on the NightStack and reloads them).

function sq(x) { return x * x; }
function sumsq(n) { let s = 0; for (let i = 0; i < n; i++) s += sq(i); return s; }
assertEq(sumsq(10), 285);

function field(o) { return o.x + o.y; }
assertEq(field({ x: 1, y: 2 }), 3);
assertEq(field({ x: "a", y: 2 }), "a2");

function setf(o, v) { o.x = v; return o.x; }
assertEq(setf({ x: 1 }, 5), 5);
var frozen = Object.freeze({ x: 1 });
var threw = false;
try { setf(frozen, 2); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);

function elems(a) { let s = 0; for (let i = 0; i < a.length; i++) s += a[i]; return s; }
assertEq(elems([1, 2, 3, 4]), 10);
assertEq(elems([1.5, 2.5]), 4);

function store(a, n) { for (let i = 0; i < n; i++) a[i] = i * 2; return a[n - 1]; }
assertEq(store([], 5), 8);

// A GC in the callee while `keep` and `other` are live in MIR.
function gcy(o, p) { let keep = o; let other = p; gc(); return keep.x + other.y; }
assertEq(gcy({ x: 40 }, { y: 2 }), 42);
function churn(n) {
  let o = { v: 1 };
  let t = 0;
  for (let i = 0; i < n; i++) {
    if (i % 100 == 0) gc();
    t += o.v;
  }
  return t;
}
assertEq(churn(1000), 1000);

function meth(o) { return o.get(); }
assertEq(meth({ get() { return 7; } }), 7);

// Deep recursion through MIR bodies stays on the NightStack.
function rec(n) { if (n <= 0) return 0; return 1 + rec(n - 1); }
assertEq(rec(5000), 5000);

// A throwing callee: the throw exit hands the exception to baseline.
function thrower() { throw new Error("t"); }
function callsThrower() { thrower(); return 1; }
var caught = null;
try { callsThrower(); } catch (e) { caught = e.message; }
assertEq(caught, "t");

// A getter that runs arbitrary JS.
var calls = 0;
var obj = { get z() { calls++; gc(); return calls; } };
function getz(o) { return o.z + o.z; }
assertEq(getz(obj), 3);

function isnum(x) { return typeof x === "number"; }
assertEq(isnum(3), true);
assertEq(isnum("a"), false);

function nn(x) { return x == null; }
function ce(x) { return x === undefined; }
function cne(x) { return x !== null; }
assertEq(nn(null), true);
assertEq(nn(undefined), true);
assertEq(nn(0), false);
assertEq(nn({}), false);
assertEq(ce(undefined), true);
assertEq(ce(null), false);
assertEq(cne(null), false);
assertEq(cne(1), true);

// A global read, and a global that changes between reads.
var g = 1;
function readg() { return g; }
assertEq(readg(), 1);
g = "two";
assertEq(readg(), "two");

// let-bound loop variables (the TDZ constant, then initialization).
function lets(n) {
  let t = 0;
  for (let i = 0; i < n; i++) { let j = i * 2; t += j; }
  return t;
}
assertEq(lets(10), 90);
