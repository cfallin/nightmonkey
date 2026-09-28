// Stamping outside a constructor's exit: object-literal and array
// allocation stamps, the two-phase restamp of an init delegate (also when
// it is inlined), a fill script's formal, and a post-construction fill
// sequence's local. Typed reads of the stamped objects must see every
// later change, including shape changes and non-number stores.

// Object literals: stamped at allocation, read through typed field sites.
function mkPoint(i) { return { x: i, y: i * 2, z: i + 0.5 }; }
function sumPoint(p) { return p.x + p.y + p.z; }

// Arrays: stamped with their element claim, then filled.
function mkDigits(n) {
  var a = [];
  for (var i = 0; i < n; i++) a[i] = i % 10;
  return a;
}
function sumArr(a) { var s = 0; for (var i = 0; i < a.length; i++) s += a[i]; return s; }

// An init delegate: the constructor stamps a prefix, the delegate adds
// the rest and restamps at its returns.
function Vec(x, y) { this.x = x; this.y = y; this.init(x + y); }
Vec.prototype.init = function (s) { this.sum = s; this.tag = "v"; };
Vec.prototype.total = function () { return this.x + this.y + this.sum; };

// A fill script: a fresh object filled through a formal.
function fill(o, a, b) { o.a = a; o.b = b; o.c = a * b; }
function mkFilled(i) { var o = {}; fill(o, i, 3); return o; }
function useFilled(o) { return o.a + o.b + o.c; }

// A post-construction fill sequence on a local.
function Box(v) { this.v = v; }
function mkBox(i) { var b = new Box(i); b.w = i + 1; b.h = i + 2; return b; }
function area(b) { return b.v + b.w * b.h; }

for (var n = 0; n < 200; n++) {
  var p = mkPoint(n);
  assertEq(sumPoint(p), n + 2 * n + n + 0.5);
  var d = mkDigits(25);
  assertEq(sumArr(d), 45 + 45 + 10);
  var v = new Vec(n, 1);
  assertEq(v.total(), n + 1 + n + 1);
  assertEq(v.tag, "v");
  var f = mkFilled(n);
  assertEq(useFilled(f), n + 3 + 3 * n);
  var b = mkBox(n);
  assertEq(area(b), n + (n + 1) * (n + 2));
}

// Stamped objects that change afterwards: a non-number field, an extra
// property, a deleted one, a non-int element.
for (var n = 0; n < 50; n++) {
  var p = mkPoint(n);
  p.x = "s";
  assertEq(sumPoint(p), "s" + 2 * n + (n + 0.5));
  var q = mkPoint(n);
  q.extra = 1;
  delete q.y;
  assertEq(Number.isNaN(sumPoint(q)), true);
  var d = mkDigits(10);
  d[3] = 1.5;
  assertEq(sumArr(d), 45 - 3 + 1.5);
  d[4] = "x";
  assertEq(typeof sumArr(d), "string");
  var v = new Vec(n, 2);
  v.x = 0.25;
  assertEq(v.total(), 0.25 + 2 + n + 2);
  var b = mkBox(n);
  b.w = "w";
  assertEq(area(b), n + ("w" * (n + 2)));
}
