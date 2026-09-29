// Accessor sites (`Object.defineProperty(P, name, {get, set})`): the
// receiver's shape probed in the accessor-call cache, the getter or setter
// it records called directly. Covers prototype and own accessors, a
// getter-only name written (a sloppy no-op), a receiver whose name is a
// plain data property, redefinition after the site has run, and a setter
// that throws.

function P(x) { this._x = x; this.sets = 0; }
Object.defineProperty(P.prototype, "x", {
  get: function () { return this._x; },
  set: function (v) { this._x = v; this.sets++; },
  configurable: true,
});
Object.defineProperty(P.prototype, "twice", { get: function () { return this._x * 2; } });

function Q(x) { this.x = x; this.twice = -1; this.sets = 0; }

function getX(o) { return o.x; }
function setX(o, v) { o.x = v; return o.x; }
function getTwice(o) { return o.twice; }
function setTwice(o, v) { o.twice = v; return o.twice; }

var own = {};
Object.defineProperty(own, "x", { get: function () { return 99; }, set: function (v) { this.seen = v; } });

var p = new P(3), q = new Q(5);
for (var r = 0; r < 400; r++) {
  assertEq(getX(p), r === 0 ? 3 : r - 1);
  assertEq(setX(p, r), r);
  assertEq(p.sets, r + 1);
  assertEq(getTwice(p), 2 * r);
  assertEq(setTwice(p, 7), 2 * r);
  assertEq(getX(q), r === 0 ? 5 : r - 1);
  assertEq(setX(q, r), r);
  assertEq(q.sets, 0);
  assertEq(getTwice(q), -1);
  if (r % 50 === 7) {
    assertEq(getX(own), 99);
    assertEq(setX(own, r), 99);
    assertEq(own.seen, r);
  }
}

// Redefined after the sites have run: the cached row must not serve it.
Object.defineProperty(P.prototype, "x", { get: function () { return -this._x; }, configurable: true });
for (var r = 0; r < 50; r++) {
  assertEq(getX(p), -399);
}

// A setter that throws.
var T = function () {};
Object.defineProperty(T.prototype, "x", { set: function (v) { throw new Error("no " + v); } });
var t = new T(), caught = 0;
for (var r = 0; r < 100; r++) {
  try { setX(t, r); } catch (e) { caught++; assertEq(e.message, "no " + r); }
}
assertEq(caught, 100);
