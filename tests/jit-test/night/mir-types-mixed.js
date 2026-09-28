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
