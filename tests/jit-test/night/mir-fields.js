// MIR's typed property access (`--pipeline mir`): where the analysis
// predicts a receiver's layout, MIR guards the stamp locally and loads or
// stores the field's fixed slot (the SLOTS bit), or goes through the
// generic helper. Each case also has receivers that break the prediction.

function Point(x, y) { this.x = x; this.y = y; }
function len2(p) { return p.x * p.x + p.y * p.y; }
function sumLen(ps) {
  var t = 0;
  for (var i = 0; i < ps.length; i++) t += len2(ps[i]);
  return t;
}
var ps = [];
for (var i = 0; i < 100; i++) ps.push(new Point(i, i + 1));
assertEq(sumLen(ps), 666700);

// Doubles in the same fields.
var qs = [];
for (var i = 0; i < 10; i++) qs.push(new Point(i + 0.5, 1));
assertEq(sumLen(qs), 342.5);

// A receiver of another shape, and a non-object.
assertEq(len2({ y: 2, x: 1 }), 5);
assertEq(len2({ x: 3, y: 4, z: 0 }), 25);
var threw = false;
try { len2(null); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);

// Stores through the predicted layout, then a non-number.
function moveBy(p, d) { p.x = p.x + d; p.y = p.y + d; return p.x + p.y; }
var p = new Point(1, 2);
for (var i = 0; i < 50; i++) moveBy(p, 1);
assertEq(p.x, 51);
assertEq(p.y, 52);
p.x = "s";
assertEq(moveBy(p, 1), "s1" + 53);

// A field that holds an object: loaded generically, never claimed.
function Node(v, next) { this.v = v; this.next = next; }
function listSum(n) { var t = 0; while (n) { t += n.v; n = n.next; } return t; }
var list = null;
for (var i = 0; i < 100; i++) list = new Node(i, list);
assertEq(listSum(list), 4950);

// GC while typed loads are in flight.
function churn(ps) {
  var t = 0;
  for (var i = 0; i < ps.length; i++) {
    if (i % 10 == 0) gc();
    t += ps[i].x;
  }
  return t;
}
assertEq(churn(ps), 4950);

// Deleting a field changes the object's layout: the guard must fail.
var d = new Point(5, 6);
delete d.x;
assertEq(Number.isNaN(len2(d)), true);
