// `new` in MIR (`--pipeline mir`): a construct site passes its sized
// allocation and early stamp word to the runtime, which creates `this`
// and runs the constructor; the object the constructor returns (if any)
// wins; errors propagate.
function P(x, y) { this.x = x; this.y = y; }
function makeMany(n) {
  var t = 0;
  for (var i = 0; i < n; i++) { var p = new P(i, 1); t += p.x + p.y; }
  return t;
}
assertEq(makeMany(1000), 499500 + 1000);

// Objects built in MIR are stamped: typed reads see them.
function sumX(ps) { var t = 0; for (var i = 0; i < ps.length; i++) t += ps[i].x; return t; }
function build(n) { var a = []; for (var i = 0; i < n; i++) a.push(new P(i, 0)); return a; }
for (var k = 0; k < 10; k++) assertEq(sumX(build(100)), 4950);

// A constructor returning an object, a primitive, and throwing.
function R() { this.a = 1; return { b: 2 }; }
function Q() { this.a = 1; return 5; }
function T(n) { if (n > 50) throw new RangeError("big"); this.n = n; }
function mk(i) {
  var r = new R(), q = new Q();
  return r.b + q.a + (r.a === undefined ? 10 : 0);
}
for (var i = 0; i < 50; i++) assertEq(mk(i), 13);
function tryT(n) { try { return new T(n).n; } catch (e) { return e instanceof RangeError ? -1 : -2; } }
function loopT() { var t = 0; for (var i = 0; i < 60; i++) t += tryT(i); return t; }
assertEq(loopT(), 1275 - 9);

// Built-in constructors, a non-constructor, and a class.
function builtins(n) {
  var a = new Array(n), d = new Date(0), m = new Map();
  m.set(1, n);
  return a.length + d.getTime() + m.get(1);
}
for (var i = 0; i < 30; i++) assertEq(builtins(i), 2 * i);
var arrow = () => 1;
function badNew(f) { try { new f(); return 0; } catch (e) { return e instanceof TypeError ? 1 : 2; } }
for (var i = 0; i < 30; i++) assertEq(badNew(arrow), 1);
class C { constructor(v) { this.v = v; } get dbl() { return this.v * 2; } }
function useC(n) { var t = 0; for (var i = 0; i < n; i++) t += new C(i).dbl; return t; }
assertEq(useC(100), 9900);

// Arguments that exit (a type change mid-evaluation) and a GC in the
// constructor.
function G(a, b) { gc(); this.s = a + b; }
function mkG(v) { return new G(v, 1).s; }
for (var i = 0; i < 30; i++) assertEq(mkG(i), i + 1);
assertEq(mkG("z"), "z1");

// A constructor some sites call with fewer arguments: the omitted formal
// reads `undefined` (MIR does not guard it at entry).
function V(name, init) { this.value = init || 0; this.name = name; }
for (var i = 0; i < 100; i++) {
  assertEq(new V("a", i).value, i);
  assertEq(new V("b").value, 0);
}
