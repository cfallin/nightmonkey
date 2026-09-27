// MIR inlines `new F(…)` of a site's one constructor: `this` is made as a
// direct construct makes it, the body is spliced with its new.target, a
// stamping constructor's inlined returns stamp, and the result is the
// body's value if an object, else `this`. Other callees construct
// generically.
function P(x, y) { this.x = x; this.y = y; }
P.prototype.sum = function () { return this.x + this.y; };
function R(v) { this.v = v; if (v < 0) return { neg: true }; return 7; }
function NT() { this.t = new.target === NT; }
function Thrower(v) { if (v === 3) throw new Error("three"); this.v = v; }
function Few(a, b, c) { this.a = a; this.b = b; this.c = c; }
function mkP(i) { return new P(i, i + 1); }
function mkR(v) { return new R(v); }
function mkNT() { return new NT(); }
function mkT(v) { return new Thrower(v); }
function mkFew(a) { return new Few(a); }
var any = function (F, v) { return new F(v); };
for (var n = 0; n < 200; n++) {
  var p = mkP(n);
  assertEq(p.sum(), 2 * n + 1);
  assertEq(p instanceof P, true);
  assertEq(mkR(1).v, 1);
  assertEq(mkR(-1).neg, true);
  assertEq(mkNT().t, true);
  var f = mkFew(n);
  assertEq(f.a, n);
  assertEq(f.c, undefined);
  var caught = null;
  try { mkT(n % 5); } catch (e) { caught = e.message; }
  assertEq(caught, n % 5 === 3 ? "three" : null);
  assertEq(any(P, n).x, n);
}
assertEq(any(R, 5).v, 5);                       // another callee
assertEq(any(function (v) { this.w = v * 2; }, 4).w, 8);
var q = {};
P.call(q, 1, 2);                                // not constructing: no stamp
assertEq(q.x + q.y, 3);
var old = P.prototype;
P.prototype = { sum: function () { return -1; } };
assertEq(mkP(3).sum(), -1);
assertEq(Object.getPrototypeOf(mkP(3)) === old, false);
