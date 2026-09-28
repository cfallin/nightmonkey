// TYPES on a layout with numeric and object fields: a compiled store of a
// value of the field's predicted type keeps it, so reads of the numeric
// fields are typed; a store of any other value (compiled, through the IC,
// or through the engine) clears it, and the reads must see the value.

function Node(id, next) { this.id = id; this.weight = id * 2; this.next = next; this.name = "n" + id; }
Node.prototype.total = function () { return this.id + this.weight; };
function relink(a, b) { a.next = b; return a; }
function rename(a, s) { a.name = s; return a; }
function setWeight(a, w) { a.weight = w; return a; }
function sum(list) { var s = 0; for (var p = list; p !== null; p = p.next) s += p.total(); return s; }

function build(n) {
  var head = null;
  for (var i = 0; i < n; i++) head = new Node(i, head);
  return head;
}

for (var round = 0; round < 100; round++) {
  var l = build(20);
  assertEq(sum(l), 3 * (19 * 20 / 2));
  relink(l, l.next.next);
  rename(l, "x" + round);
  assertEq(sum(l), 3 * (19 * 20 / 2) - 3 * 18);
  setWeight(l, 1.5);
  assertEq(l.total(), 19 + 1.5);
  if (round % 10 == 0) {
    setWeight(l, "w");
    assertEq(l.total(), "19w");
    setWeight(l, { valueOf: function () { return 4; } });
    assertEq(l.total(), 23);
    l.id = null;
    assertEq(l.total(), 4);
    Object.assign(l.next, { weight: "e" });
    assertEq(l.next.total(), "17e");
  }
}

// Delegating constructors (the object's early key is the outer class's)
// and one store site reaching two classes whose same-named field has
// different predicted types: each store is checked against its object's
// own class.
function Base(s) { this.strength = s; }
function Mid(a, s) { Base.call(this, s); this.a = a; this.dir = 0; }
function Leaf(a, s) { Mid.call(this, a, s); }
Leaf.prototype = Mid.prototype;
Mid.prototype.sum = function () { return this.a.v + this.strength.v + this.dir; };
function A() { this.tag = "a"; this.n = 1; }
function B() { this.tag = 7; this.n = 2; }
function setTag(o, t) { o.tag = t; return o; }
function tagOf(o) { return o.tag; }
for (var round = 0; round < 200; round++) {
  var l = new Leaf({ v: round }, { v: 2 });
  assertEq(l.sum(), round + 2);
  var x = setTag(new A(), "s" + round);
  var y = setTag(new B(), round);
  assertEq(tagOf(x), "s" + round);
  assertEq(tagOf(y), round);
  if (round % 50 == 49) {
    setTag(x, round);
    assertEq(tagOf(x) + 1, round + 1);
    setTag(y, "t");
    assertEq(tagOf(y), "t");
    l.dir = "d";
    assertEq(l.sum(), round + 2 + "d");
  }
}
