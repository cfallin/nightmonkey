// TYPES maintenance through every store path that may keep the bit: the
// set helpers (checking the field's claim), baseline stores (vouched), a
// construction delegate's stores, element stores on a plain object, adds
// beyond the layout, and accessors defined on a stamped object. Typed
// reads must see every value actually stored; under --mir-stress the
// methods run partly in baseline, whose stores take the helper paths.

// A delegate shared by many classes: its `this` stores are checked
// against the classes whose construction reaches it.
function Base() { this.pos = 0; this.eof = false; this.buffer = null; }
function mk(name) {
  var C = function (v) { this.v = v; this.tag = name; Base.call(this); };
  C.prototype.read = function () {
    if (this.buffer === null) this.buffer = [this.v, this.v + 1];
    this.pos = this.pos + 1;
    if (this.pos > 3) this.eof = true;
    return this.buffer[this.pos % 2] + this.pos + (this.eof ? 100 : 0);
  };
  return C;
}
var classes = [];
for (var i = 0; i < 12; i++) classes.push(mk("c" + i));

var total = 0, want = 0;
for (var r = 0; r < 40; r++) {
  for (var i = 0; i < classes.length; i++) {
    var o = new classes[i](i);
    for (var k = 1; k <= 5; k++) {
      total += o.read();
      want += (k % 2 == 0 ? i : i + 1) + k + (k > 3 ? 100 : 0);
    }
  }
}
assertEq(total, want);

// Digits as elements of a plain object, fields beside them.
function Big(n) { this.t = 0; this.s = 0; for (var i = 0; i < n; i++) this[i] = i * 3; this.t = n; }
Big.prototype.sum = function () { var s = this.s; for (var i = 0; i < this.t; i++) s += this[i]; return s; };
for (var r = 0; r < 200; r++) {
  var b = new Big(r % 7 + 1);
  b[0] = r;
  var n = r % 7 + 1, w = r;
  for (var i = 1; i < n; i++) w += i * 3;
  assertEq(b.sum(), w);
}

// Adds beyond the layout, and accessors on a stamped object.
function Ctx() { this.save = function () { return 1; }; this.restore = function () { return 2; }; }
Ctx.prototype.both = function () { return this.save() + this.restore(); };
for (var r = 0; r < 100; r++) {
  var c = new Ctx();
  assertEq(c.both(), 3);
  c._orig = c.save;
  Object.defineProperty(c, "current", { get: function () { return 7; } });
  c.save = function () { return 10; };
  assertEq(c.both(), 12);
  assertEq(c.current, 7);
  if (r % 9 == 0) {
    c.restore = "not a function";
    assertEq(typeof c.restore, "string");
    var threw = false;
    try { c.both(); } catch (e) { threw = true; }
    assertEq(threw, true);
  }
}

// A non-conforming store through a polymorphic site still drops the claim.
function A(v) { this.x = v; this.y = 1; }
function B(v) { this.y = 2; this.x = v; }
A.prototype.get = B.prototype.get = function () { return this.x + this.y; };
function setX(o, v) { o.x = v; }
for (var r = 0; r < 300; r++) {
  var a = new A(r), bb = new B(r);
  setX(a, r + 1);
  setX(bb, r + 2);
  assertEq(a.get(), r + 2);
  assertEq(bb.get(), r + 4);
  if (r % 7 == 0) {
    setX(bb, "s");
    assertEq(bb.get(), "s2");
  }
}
