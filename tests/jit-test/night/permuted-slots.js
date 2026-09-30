// The engine's custom-slot shapes (SharedShape::getShapeWithPropertyAtSlot,
// via the shell's addPropertyAtSlot): a property placed in a slot of the
// caller's choosing keeps the visible property order, the values, and the
// engine's own paths (generic adds on top, delete, dictionary conversion,
// attribute changes, Object.assign, JSON, GC) correct.

function assertEq(a, b, msg) {
  if (a !== b) {
    throw new Error((msg || "") + ": got " + String(a) + ", expected " + String(b));
  }
}
function keys(o) { return Object.keys(o).join(","); }

// Two insertion orders, one slot assignment: x->0, y->1, z->2.
function build(order) {
  var o = {};
  var slot = { x: 0, y: 1, z: 2 };
  for (var k of order) {
    assertEq(addPropertyAtSlot(o, k, slot[k]), true, "place " + k);
    o[k] = k.toUpperCase();
  }
  return o;
}
var a = build(["x", "y", "z"]);
var b = build(["x", "z", "y"]);
assertEq(keys(a), "x,y,z");
assertEq(keys(b), "x,z,y");
assertEq(hasPermutedSlots(a), false, "in-order placement is sequential");
assertEq(hasPermutedSlots(b), true);
assertEq(objectSlotSpan(b), 3);
assertEq(b.x + b.y + b.z, "XYZ");

// Holes: z first at 2 leaves 0 and 1 as holes (undefined, no property).
var h = {};
assertEq(addPropertyAtSlot(h, "z", 2), true);
assertEq(objectSlotSpan(h), 3);
assertEq(keys(h), "z");
assertEq("x" in h, false);
assertEq(h.x, undefined);
// A slot in use is refused; a hole is filled.
assertEq(addPropertyAtSlot(h, "w", 2), false, "slot in use");
assertEq(addPropertyAtSlot(h, "z", 1), false, "key present");
assertEq(addPropertyAtSlot(h, "x", 0), true);
assertEq(objectSlotSpan(h), 3);
h.x = 10; h.z = 30;
// Generic adds go on top of the span.
h.g1 = 40;
h.g2 = 50;
assertEq(objectSlotSpan(h), 5);
assertEq(keys(h), "z,x,g1,g2");
assertEq(h.x + h.z + h.g1 + h.g2, 130);
// The remaining hole can still be filled after generic adds.
assertEq(addPropertyAtSlot(h, "y", 1), true);
h.y = 20;
assertEq(keys(h), "z,x,g1,g2,y");
assertEq(h.x + h.y + h.z + h.g1 + h.g2, 150);

// GC with holes present (minor and major), then values intact.
var many = [];
for (var i = 0; i < 200; i++) {
  var o = {};
  addPropertyAtSlot(o, "c", 5);
  addPropertyAtSlot(o, "a", 1);
  o.c = { v: i };
  o.a = "s" + i;
  o.tail = [i];
  many.push(o);
}
minorgc();
gc();
for (var i = 0; i < 200; i++) {
  var o = many[i];
  assertEq(o.c.v, i);
  assertEq(o.a, "s" + i);
  assertEq(o.tail[0], i);
  assertEq(keys(o), "c,a,tail");
}

// Delete: the last property (not the top slot) and a middle one.
function holey() {
  var o = {};
  addPropertyAtSlot(o, "p", 3);
  addPropertyAtSlot(o, "q", 0);
  o.p = 1; o.q = 2;
  o.r = 3;  // generic: slot 4
  return o;
}
var d1 = holey();
delete d1.r;
assertEq(keys(d1), "p,q");
d1.s = 4;
assertEq(d1.p + d1.q + d1.s, 7);
var d2 = holey();
delete d2.q;
assertEq(keys(d2), "p,r");
d2.t = 5;
assertEq(d2.p + d2.r + d2.t, 9);
var d3 = holey();
delete d3.p;
delete d3.r;
delete d3.q;
assertEq(keys(d3), "");
d3.u = 6;
assertEq(d3.u, 6);

// Dictionary conversion (many adds) keeps every value.
var big = {};
addPropertyAtSlot(big, "k7", 7);
addPropertyAtSlot(big, "k2", 2);
big.k7 = 7; big.k2 = 2;
for (var i = 0; i < 400; i++) {
  big["n" + i] = i;
}
assertEq(big.k7 + big.k2, 9);
var sum = 0;
for (var i = 0; i < 400; i++) {
  sum += big["n" + i];
}
assertEq(sum, 399 * 400 / 2);

// Attribute changes rebuild the map with each property's own slot.
var c = holey();
Object.defineProperty(c, "p", { enumerable: false });
assertEq(keys(c), "q,r");
assertEq(c.p + c.q + c.r, 6);
Object.defineProperty(c, "q", { writable: false });
c.q = 99;
assertEq(c.q, 2);
var f = holey();
Object.freeze(f);
assertEq(Object.isFrozen(f), true);
assertEq(f.p + f.q + f.r, 6);

// Object.assign, from and to permuted objects.
var src = holey();
var t1 = Object.assign({}, src);
assertEq(keys(t1), "p,q,r");
assertEq(t1.p * 100 + t1.q * 10 + t1.r, 123);
for (var i = 0; i < 5; i++) {
  var t2 = Object.assign({}, src);
  assertEq(t2.p * 100 + t2.q * 10 + t2.r, 123);
}
var tgt = {};
addPropertyAtSlot(tgt, "b", 1);
tgt.b = "B";
Object.assign(tgt, { a: "A", c: "C" });
assertEq(keys(tgt), "b,a,c");
assertEq(tgt.a + tgt.b + tgt.c, "ABC");
var spread = { ...src };
assertEq(spread.p * 100 + spread.q * 10 + spread.r, 123);

// JSON round trip.
var j = JSON.parse(JSON.stringify(src));
assertEq(keys(j), "p,q,r");
assertEq(JSON.stringify(j), JSON.stringify(src));
assertEq(JSON.stringify(src), '{"p":1,"q":2,"r":3}');

// Slots past the fixed slots, and large slot numbers: a first map entry
// placed at 300 takes a normal map; a compact map refuses slots past its
// small field.
var dyn = {};
assertEq(addPropertyAtSlot(dyn, "far", 40), true);
dyn.far = "F";
dyn.next = "N";
assertEq(objectSlotSpan(dyn), 42);
gc();
assertEq(dyn.far + dyn.next, "FN");
var n1 = {};
assertEq(addPropertyAtSlot(n1, "a", 300), true);
assertEq(addPropertyAtSlot(n1, "b", 301), true);
n1.a = 1; n1.b = 2;
assertEq(n1.a + n1.b, 3);
var c1 = {};
assertEq(addPropertyAtSlot(c1, "a", 0), true);
assertEq(addPropertyAtSlot(c1, "b", 300), false, "compact map limit");
c1.b = 2;
assertEq(keys(c1), "a,b");

// for-in and entries follow insertion order.
var fi = [];
for (var k in b) fi.push(k);
assertEq(fi.join(","), "x,z,y");
assertEq(Object.entries(b).map(e => e.join("=")).join(","), "x=X,z=Z,y=Y");
