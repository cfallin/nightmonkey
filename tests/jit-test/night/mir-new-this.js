// `new_this` (an inlined `new F()` of a layout constructor: `this` from
// `F.prototype`, read by name) and a wrapper constructor's forward of its
// `this` under construction (`this.initialize.apply(this, arguments)`),
// whose other targets exit for baseline. Every case must match the spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + String(got) + ", want " + String(want));
}

function P(x, y) { this.x = x; this.y = y; }
P.prototype.sum = function () { return this.x + this.y; };
function makeP(i) { return new P(i, 1); }

for (var k = 0; k < 50; k++) check(makeP(k).sum(), k + 1, "P");
var p0 = makeP(0);
check(Object.getPrototypeOf(p0), P.prototype, "prototype");

// A reassigned prototype: objects made after it have the new one.
var oldProto = P.prototype;
P.prototype = { sum: function () { return -1; } };
check(makeP(3).sum(), -1, "reassigned prototype");
check(Object.getPrototypeOf(makeP(3)) === oldProto, false, "not the old one");
// A non-object prototype: Object.prototype.
P.prototype = 5;
var q = makeP(4);
check(Object.getPrototypeOf(q), Object.prototype, "non-object prototype");
check(q.x, 4, "fields still set");
P.prototype = oldProto;
check(makeP(5).sum(), 6, "restored");

// Another new.target: the generic path.
function G() {}
G.prototype.tag = "g";
var r = Reflect.construct(P, [1, 2], G);
check(Object.getPrototypeOf(r), G.prototype, "Reflect.construct new.target");
check(r.x + r.y, 3, "Reflect.construct fields");

// The Class.create wrapper: one constructor script for every class.
var Class = {
  create: function () {
    return function () { this.initialize.apply(this, arguments); };
  },
};
var Vec = Class.create();
Vec.prototype = {
  initialize: function (x, y) { this.x = x; this.y = y; },
  len2: function () { return this.x * this.x + this.y * this.y; },
};
var Col = Class.create();
Col.prototype = {
  initialize: function (r) { this.r = r; },
  red: function () { return this.r; },
};
function makeVec(i) { return new Vec(i, 2); }
function makeCol(i) { return new Col(i); }
for (var k = 0; k < 50; k++) {
  check(makeVec(k).len2(), k * k + 4, "Vec");
  check(makeCol(k).red(), k, "Col");
}

// `initialize` replaced: the forward's other target (an exit; baseline
// calls it).
var calls = 0;
Vec.prototype.initialize = function (x, y) { calls++; this.x = y; this.y = x; };
var v = makeVec(7);
check(v.x, 2, "replaced initialize x");
check(v.y, 7, "replaced initialize y");
check(calls, 1, "replaced initialize ran");

// `Function.prototype.apply` replaced: not the builtin (an exit).
var realApply = Function.prototype.apply;
var applies = 0;
Function.prototype.apply = function (t, a) { applies++; return realApply.call(this, t, a); };
var c = makeCol(9);
check(c.red(), 9, "patched apply");
check(applies, 1, "patched apply ran");
Function.prototype.apply = realApply;
check(makeCol(10).red(), 10, "restored apply");
