// A shared constructor wrapper (prototype.js's `Class.create`), spliced at
// each `new` site with its `this.initialize.apply(this, arguments)`
// resolved for that site: the wrapper's inline frame holds the call's
// actuals, whatever their count. Covers under- and over-application, an
// `initialize` that reads `arguments`, adds shadowing a prototype's
// default (`x: 0`), a constructor whose value types change mid-run (the
// adds leave construction to baseline), a site whose class changes, and
// an `initialize` replaced after the wrapper was inlined.

var Class = { create: function() { return function() { this.initialize.apply(this, arguments); }; } };

var V = Class.create();
V.prototype = {
  x: 0, y: 0, z: 0,
  initialize: function(x, y, z) { this.x = (x ? x : 0); this.y = (y ? y : 0); this.z = (z ? z : 0); },
  sum: function() { return this.x + this.y + this.z; }
};
var N = Class.create();
N.prototype = { initialize: function() { this.n = arguments.length; this.last = arguments[arguments.length - 1]; } };
var P = Class.create();
P.prototype = { initialize: function(a, b) { this.a = a; this.b = b; } };

function makeV(i) { return new V(i, i + 1, i + 2); }
function makeV2(i) { return new V(i); }
function makeV4(i) { return new V(i, 1, 2, 3); }
function makeN(i) { return new N(i, i, i); }
function makeP(i, s) { return new P(i, s); }
function pick(i) { var C = (i % 7 == 6) ? P : V; return new C(i, 2); }

for (var r = 0; r < 400; r++) {
  var v = makeV(r);
  assertEq(v.sum(), 3 * r + 3);
  assertEq(v.hasOwnProperty("x"), true);
  assertEq(makeV2(r).sum(), r);
  assertEq(makeV4(r).sum(), r + 3);
  var n = makeN(r);
  assertEq(n.n, 3);
  assertEq(n.last, r);
  var p = makeP(r, r % 50 == 49 ? "s" + r : r);
  assertEq(p.a, r);
  assertEq(p.b, r % 50 == 49 ? "s" + r : r);
  var q = pick(r);
  if (r % 7 == 6) assertEq(q.b, 2); else assertEq(q.sum(), r + 2);
  // Doubles into the same fields.
  if (r % 30 == 29) assertEq(makeV(r + 0.5).sum(), 3 * r + 4.5);
}
// A new `initialize` for the class after the wrapper has been inlined.
V.prototype.initialize = function(x) { this.x = -x; };
for (var r = 0; r < 50; r++)
  assertEq(makeV(r).sum(), -r + 0);
