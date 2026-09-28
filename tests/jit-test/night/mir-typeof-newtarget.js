// `typeof` of a global name, bound or not (no ReferenceError for an
// unbound one), and `new.target` in constructed, called, inlined and
// delegated frames.

var boundNum = 3, boundFn = function () {};
function kinds() {
  return (typeof boundNum) + "," + (typeof boundFn) + "," + (typeof neverDeclaredAnywhere) + "," +
         (typeof lateBound);
}
for (var i = 0; i < 300; i++) {
  if (i == 150) this.lateBound = "s";
  assertEq(kinds(), "number,function,undefined," + (i >= 150 ? "string" : "undefined"));
}

function NT() { this.nt = new.target === NT; this.called = new.target === undefined; }
function makeBoth(i) {
  var a = new NT();
  var b = {};
  NT.call(b);
  return (a.nt ? 1 : 0) + (a.called ? 10 : 0) + (b.nt ? 100 : 0) + (b.called ? 1000 : 0);
}
for (var i = 0; i < 300; i++) {
  assertEq(makeBoth(i), 1001);
  assertEq(NT() === undefined, true);
}

// A delegate reads its own frame's new.target: undefined under `.call`.
function Inner() { this.inner = new.target; }
function Outer() { Inner.call(this); this.outer = new.target; }
for (var i = 0; i < 300; i++) {
  var o = new Outer();
  assertEq(o.inner, undefined);
  assertEq(o.outer, Outer);
}
