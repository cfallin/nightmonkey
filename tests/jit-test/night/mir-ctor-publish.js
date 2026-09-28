// Construction through deep prototype chains and init delegates, with
// methods called on `this` before the constructor returns (the object is
// published there, `ctor_publish`), and polymorphic store sites whose
// other classes take the set helper (vouched stores keep TYPES). Typed
// reads must see every value actually stored, including non-conforming
// ones on each of those paths.

Object.defineProperty(Object.prototype, "inheritsFrom", {
  value: function (shuper) {
    function Inheriter() { }
    Inheriter.prototype = shuper.prototype;
    this.prototype = new Inheriter();
    this.superConstructor = shuper;
  }
});

var registry = [];

function Base(s) { this.strength = s; }
Base.prototype.add = function () { this.addToGraph(); registry.push(this); };
Base.prototype.total = function () { return this.strength; };

function Bin(a, b, s) {
  Bin.superConstructor.call(this, s);
  this.v1 = a;
  this.v2 = b;
  this.direction = 0;
  this.add();
}
Bin.inheritsFrom(Base);
Bin.prototype.addToGraph = function () { this.direction = this.v1 > this.v2 ? 1 : -1; };
Bin.prototype.flip = function () { this.direction = -this.direction; };
Bin.prototype.total = function () { return this.v1 + this.v2 + this.direction + this.strength; };

// Same delegate, a different layout (fields added before the delegation).
function Scale(a, b, k, s) {
  this.direction = 0;
  this.scale = k;
  Scale.superConstructor.call(this, a, b, s);
}
Scale.inheritsFrom(Bin);
Scale.prototype.total = function () {
  return (this.v1 + this.v2) * this.scale + this.direction + this.strength;
};

function Eq(a, b, s) { Eq.superConstructor.call(this, a, b, s); }
Eq.inheritsFrom(Bin);

function expectBin(o, a, b, s, dir) { return a + b + dir + s; }

for (var r = 0; r < 60; r++) {
  registry = [];
  for (var i = 0; i < 40; i++) {
    var e = new Eq(i, 20, 3);
    var sc = new Scale(i, 20, 2, 5);
    assertEq(e.direction, i > 20 ? 1 : -1);
    assertEq(sc.direction, i > 20 ? 1 : -1);
  }
  var sum = 0, want = 0;
  for (var j = 0; j < registry.length; j++) {
    var o = registry[j];
    o.flip();
    sum += o.total();
    var dir = -(o.v1 > o.v2 ? 1 : -1);
    want += o instanceof Scale ? (o.v1 + o.v2) * o.scale + dir + o.strength
                               : o.v1 + o.v2 + dir + o.strength;
  }
  assertEq(sum, want);
}

// Non-conforming stores on each path must drop the claim.
// 1. After the early publish, in the constructor itself.
function Late(a) {
  this.x = a;
  this.y = 1;
  this.touch();
  if (a % 7 == 0) this.x = "s" + a;
}
Late.prototype.touch = function () { this.y = this.y + 1; };
Late.prototype.sum = function () { return this.x + this.y; };
for (var i = 0; i < 300; i++) {
  var l = new Late(i);
  assertEq(l.sum(), i % 7 == 0 ? "s" + i + 2 : i + 2);
}

// 2. A polymorphic store site: its second class misses the site's inline
//    way and takes the helper, with conforming and non-conforming values.
function P1(v) { this.a = v; this.b = 1; }
P1.prototype.get = function () { return this.a + this.b; };
function P2(v) { this.b = 2; this.a = v; }
P2.prototype.get = function () { return this.a + this.b; };
function setA(o, v) { o.a = v; }
for (var i = 0; i < 300; i++) {
  var p = new P1(i), q = new P2(i);
  setA(p, i + 1);
  setA(q, i + 2);
  assertEq(p.get(), i + 2);
  assertEq(q.get(), i + 4);
  if (i % 5 == 0) {
    setA(q, "q");
    assertEq(q.get(), "q2");
    setA(p, 0.5);
    assertEq(p.get(), 1.5);
  }
}

// 3. Under construction, through a deep chain: a non-conforming add or
//    store before the object is published.
function D0() { }
function D1() { }
D1.inheritsFrom(D0);
function D2() { }
D2.inheritsFrom(D1);
function D3(v) {
  this.m = v;
  this.n = v % 11 == 0 ? "n" : v;
  this.o = v + 1;
}
D3.inheritsFrom(D2);
D3.prototype.sum = function () { return this.m + this.n + this.o; };
for (var i = 0; i < 300; i++) {
  var d = new D3(i);
  assertEq(d.sum(), i % 11 == 0 ? i + "n" + (i + 1) : 3 * i + 1);
}
