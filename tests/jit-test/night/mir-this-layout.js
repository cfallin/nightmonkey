// MIR's proven receivers: a method guards `this` to its predicted layout
// once, and its field accesses through it take no guard of their own
// until a fence (a call) weakens the proof, when the next access guards
// again. A foreign `this` exits at the method's entry; an object that
// loses its TYPES bit is read under its identity alone.
function V(x, y) { this.x = x; this.y = y; this.n = 0; }
V.prototype.step = function (d) {
  this.x += d;
  this.y -= d;
  this.n++;
  return this.x + this.y;
};
V.prototype.poke = function (o) {
  var a = this.x;
  o.touch();              // a fence between two reads of `this`
  return a + this.x;
};
function T() { this.k = 1; }
T.prototype.touch = function () { this.k++; };
var v = new V(1, 2);
var t = new T();
for (var i = 0; i < 200; i++) {
  assertEq(v.step(1), 3);
  assertEq(v.poke(t), 2 * v.x);
}
assertEq(v.n, 200);
// A foreign receiver.
var f = { x: 10, y: 20, n: 0 };
assertEq(V.prototype.step.call(f, 5), 30);
assertEq(f.n, 1);
// A non-number store drops TYPES on this object: reads stay correct.
var w = new V(3, 4);
for (var i = 0; i < 100; i++) w.step(0);
w.x = "s";
assertEq(w.step(0), "s04");
assertEq(v.step(0), 3);
// Constructors adding non-number fields to fresh objects.
function P(a, b) { this.car = a; this.cdr = b; }
var l = null;
for (var i = 0; i < 300; i++) l = new P(i, l);
var s = 0;
for (var q = l; q !== null; q = q.cdr) s += q.car;
assertEq(s, 299 * 300 / 2);
