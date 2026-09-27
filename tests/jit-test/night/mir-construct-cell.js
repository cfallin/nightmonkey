// MIR direct construct's inline `this` (the site's construct cell, then a
// nursery bump): the cached prototype must follow `.prototype`
// reassignment, and the objects must survive minor GCs.
function P(x) { this.x = x; this.y = x + 1; }
P.prototype.sum = function () { return this.x + this.y; };
function make(x) { return new P(x); }
var keep = [];
for (var n = 0; n < 2000; n++) {
  var p = make(n);
  assertEq(p.sum(), 2 * n + 1);
  if (n % 100 == 0) keep.push(p);
  if (n == 1000) minorgc();
}
for (var i = 0; i < keep.length; i++) assertEq(keep[i].x, i * 100);
var old = P.prototype;
P.prototype = { sum: function () { return -1; } };
for (var n = 0; n < 50; n++) {
  var p = make(n);
  assertEq(p.sum(), -1);
  assertEq(Object.getPrototypeOf(p) === old, false);
}
// A new shape on the constructor (an added property) keeps it working.
P.extra = 1;
assertEq(make(3).sum(), -1);
assertEq(make(3).y, 4);
