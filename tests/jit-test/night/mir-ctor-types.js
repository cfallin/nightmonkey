// The constructing type (MIR.md §2.3): an inlined `new` builds its
// constructor for a `this` under construction, whose adds are
// `init_field`s, whose methods (inlined) read the fields added so far with
// no entry guard, and which is published once every field is there. Every
// way construction can leave the predicted order must still compute the
// right values: calls before completion, methods that add fields,
// delegates, adds out of order, a getter adding a field mid-construction,
// non-conforming values, and constructors called without `new`.

// Methods called before every field is added.
function V(x, y) {
  this.x = x;
  this.len = this.norm();
  this.y = y;
  this.k = this.scale(2);
}
V.prototype.norm = function () { return this.x * this.x; };
V.prototype.scale = function (s) { return (this.x + this.y) * s; };
V.prototype.sum = function () { return this.x + this.len + this.y + this.k; };

// A method that adds fields itself (an init delegate).
function W(a) {
  this.a = a;
  this.init(a + 1);
  this.c = this.a + this.b;
}
W.prototype.init = function (b) { this.b = b; };

// A delegate through `.call(this)`, then a method.
function Base(s) { this.s = s; }
function D(s, t) {
  Base.call(this, s);
  this.t = t;
  this.u = this.both();
}
D.prototype.both = function () { return this.s * 10 + this.t; };

// Adds out of the predicted order, some of the time.
function O(swap, p, q) {
  if (swap) { this.q = q; this.p = p; } else { this.p = p; this.q = q; }
  this.r = this.p - this.q;
}

// A getter on the prototype adding a field while the object is built.
function G(v) {
  this.v = v;
  var w = this.sneak;
  this.w = w + v;
}
Object.defineProperty(G.prototype, "sneak", {
  get: function () { if (this.v % 13 == 0) this.extra = 1; return 5; }
});

// A non-conforming value, some of the time.
function N(i) {
  this.i = i;
  this.j = (i % 17 == 0) ? "s" : i * 2;
  this.k = this.j + 1;
}

var total = 0, want = 0;
for (var r = 0; r < 3000; r++) {
  var i = r % 50;
  var v = new V(i & 15, 3);
  total += v.sum();
  var x = i & 15;
  want += x + x * x + 3 + (x + 3) * 2;

  var w = new W(i);
  total += w.c;
  want += i + i + 1;

  var d = new D(i, 7);
  total += d.u;
  want += i * 10 + 7;

  var o = new O(r % 5 == 0, i, 3);
  total += o.r;
  want += i - 3;

  var g = new G(i);
  total += g.w + (g.extra || 0);
  want += 5 + i + (i % 13 == 0 ? 1 : 0);

  var n = new N(i);
  if (i % 17 == 0) {
    assertEq(n.k, "s1");
  } else {
    total += n.k;
    want += i * 2 + 1;
  }
}
assertEq(total, want);

// Called without `new`: `this` is whatever the call passes.
var plain = Object.create(V.prototype);
V.call(plain, 2, 1);
assertEq(plain.len, 4);
assertEq(plain.k, 6);

// A subclass whose layout extends through a delegate.
function E(x, y, z) { V.call(this, x, y); this.z = z; }
E.prototype = Object.create(V.prototype);
for (var r = 0; r < 500; r++) {
  var e = new E(r & 7, 2, r);
  assertEq(e.sum(), (r & 7) + (r & 7) * (r & 7) + 2 + ((r & 7) + 2) * 2);
  assertEq(e.z, r);
}
