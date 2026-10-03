// A property read's caches serve a proven absence (`undefined`) and a
// primitive receiver's prototype chain without leaving compiled code. Each
// absence here is cached first, then falsified on every object its proof
// rests on (the receiver, each prototype, Object.prototype), by an add, a
// getter, a prototype change or a delete-and-readd; every read must see the
// change at once.

function readRef(o) { return o.ref; }
function readKey(o) { return o.key; }
function readDP(f) { return f.defaultProps; }
function readZ(v) { return v.zzz; }
function readTrim(v) { return v.trim; }
function readFixed(v) { return v.toFixed; }
function readHas(v) { return v.hasOwnProperty; }

function warm(fn, v, want, n) {
  for (var i = 0; i < (n || 200); i++) assertEq(fn(v), want);
}

// Two hops, the far one falsified first: a string's chain (String.prototype,
// Object.prototype) and a constructed object's (C0.prototype,
// Object.prototype), each absence cached and then broken only on the hop
// past the first.
function C0() { this.v = 1; }
var c0s = [new C0(), new C0()];
var s0s = ["abc", "d"];
for (var i = 0; i < 300; i++) {
  assertEq(readZ(s0s[i & 1]), undefined);
  assertEq(readKey(c0s[i & 1]), undefined);
}
Object.prototype.zzz = "far";
Object.prototype.key = "far";
for (var i = 0; i < 300; i++) {
  assertEq(readZ(s0s[i & 1]), "far");
  assertEq(readKey(c0s[i & 1]), "far");
}
delete Object.prototype.zzz;
delete Object.prototype.key;
for (var i = 0; i < 300; i++) {
  assertEq(readZ(s0s[i & 1]), undefined);
  assertEq(readKey(c0s[i & 1]), undefined);
}

// One hop: a plain object whose prototype is Object.prototype.
var plain = [{ a: 1 }, { a: 1, b: 2 }, { b: 3 }, { c: 4, a: 5 }];
for (var i = 0; i < 400; i++) assertEq(readRef(plain[i % 4]), undefined);
plain[2].ref = "own";
for (var i = 0; i < 400; i++) assertEq(readRef(plain[i % 4]), i % 4 == 2 ? "own" : undefined);
Object.prototype.ref = "proto";
for (var i = 0; i < 400; i++) assertEq(readRef(plain[i % 4]), i % 4 == 2 ? "own" : "proto");
delete Object.prototype.ref;
for (var i = 0; i < 400; i++) assertEq(readRef(plain[i % 4]), i % 4 == 2 ? "own" : undefined);
Object.defineProperty(Object.prototype, "ref", { get() { return "getter"; }, configurable: true });
for (var i = 0; i < 400; i++) assertEq(readRef(plain[i % 4]), i % 4 == 2 ? "own" : "getter");
delete Object.prototype.ref;

// No prototype at all: the receiver's shape is the whole proof.
var bare = Object.create(null);
bare.x = 1;
warm(readKey, bare, undefined);
bare.key = 7;
warm(readKey, bare, 7);

// Two hops: a constructed object, its prototype, Object.prototype.
function C() { this.v = 1; }
var cs = [new C(), new C(), new C()];
for (var i = 0; i < 300; i++) assertEq(readKey(cs[i % 3]), undefined);
C.prototype.key = "mid";
for (var i = 0; i < 300; i++) assertEq(readKey(cs[i % 3]), "mid");
delete C.prototype.key;
for (var i = 0; i < 300; i++) assertEq(readKey(cs[i % 3]), undefined);
Object.prototype.key = "top";
for (var i = 0; i < 300; i++) assertEq(readKey(cs[i % 3]), "top");
delete Object.prototype.key;
for (var i = 0; i < 300; i++) assertEq(readKey(cs[i % 3]), undefined);
// The middle prototype's own prototype changes.
var other = { key: "swapped" };
Object.setPrototypeOf(C.prototype, other);
for (var i = 0; i < 300; i++) assertEq(readKey(cs[i % 3]), "swapped");
Object.setPrototypeOf(C.prototype, Object.prototype);
for (var i = 0; i < 300; i++) assertEq(readKey(cs[i % 3]), undefined);

// Functions: their resolve hook may materialize name/length/prototype, but
// not this name; Function.prototype is a middle hop.
function Comp() {}
function Comp2() {}
for (var i = 0; i < 300; i++) assertEq(readDP(i & 1 ? Comp : Comp2), undefined);
Comp.defaultProps = { d: 1 };
for (var i = 0; i < 300; i++) assertEq(readDP(i & 1 ? Comp : Comp2), i & 1 ? Comp.defaultProps : undefined);
Function.prototype.defaultProps = "fp";
for (var i = 0; i < 300; i++) assertEq(readDP(i & 1 ? Comp : Comp2), i & 1 ? Comp.defaultProps : "fp");
delete Function.prototype.defaultProps;
for (var i = 0; i < 300; i++) assertEq(readDP(i & 1 ? Comp : Comp2), i & 1 ? Comp.defaultProps : undefined);
// A function's lazily resolved name is never cached as absent.
function readName(f) { return f.name; }
for (var i = 0; i < 300; i++) assertEq(readName(i & 1 ? Comp : Comp2), i & 1 ? "Comp" : "Comp2");

// Primitives: the lookup starts at the prototype.
var strs = ["abc", "", "longer string value", "\u1234x"];
for (var i = 0; i < 400; i++) assertEq(readZ(strs[i % 4]), undefined);
String.prototype.zzz = "sp";
for (var i = 0; i < 400; i++) assertEq(readZ(strs[i % 4]), "sp");
delete String.prototype.zzz;
for (var i = 0; i < 400; i++) assertEq(readZ(strs[i % 4]), undefined);
Object.prototype.zzz = "op";
for (var i = 0; i < 400; i++) assertEq(readZ(strs[i % 4]), "op");
for (var i = 0; i < 400; i++) assertEq(readZ(i & 1 ? 1.5 : i), "op");
for (var i = 0; i < 400; i++) assertEq(readZ(!!(i & 1)), "op");
delete Object.prototype.zzz;
for (var i = 0; i < 400; i++) assertEq(readZ(i & 1 ? 1.5 : i), undefined);
for (var i = 0; i < 400; i++) assertEq(readZ(i & 1 ? strs[i % 4] : true), undefined);
// Number.prototype's and Boolean.prototype's absences stay theirs.
Number.prototype.zzz = "np";
for (var i = 0; i < 400; i++) assertEq(readZ(i % 3 == 0 ? i : i % 3 == 1 ? "s" : false), i % 3 == 0 ? "np" : undefined);
delete Number.prototype.zzz;

// Methods found on the primitive's prototype, then replaced.
var origTrim = String.prototype.trim;
for (var i = 0; i < 400; i++) assertEq(readTrim(strs[i % 4]), origTrim);
String.prototype.trim = function () { return "mine"; };
for (var i = 0; i < 400; i++) assertEq(readTrim(strs[i % 4])(), "mine");
String.prototype.trim = origTrim;
for (var i = 0; i < 400; i++) assertEq(readTrim(strs[i % 4]), origTrim);
var origFixed = Number.prototype.toFixed;
for (var i = 0; i < 400; i++) assertEq(readFixed(i & 1 ? i : i + 0.25), origFixed);
// Found past the prototype (Object.prototype), then shadowed on it.
var origHas = Object.prototype.hasOwnProperty;
for (var i = 0; i < 400; i++) assertEq(readHas(i & 1 ? "s" : 3), origHas);
String.prototype.hasOwnProperty = "shadow";
for (var i = 0; i < 400; i++) assertEq(readHas(i & 1 ? "s" : 3), i & 1 ? "shadow" : origHas);
delete String.prototype.hasOwnProperty;
for (var i = 0; i < 400; i++) assertEq(readHas(i & 1 ? "s" : 3), origHas);
// A getter on the prototype sees the primitive as `this`.
Object.defineProperty(String.prototype, "zzz", { get() { "use strict"; return typeof this + this.length; }, configurable: true });
for (var i = 0; i < 400; i++) assertEq(readZ(strs[i % 4]), "string" + strs[i % 4].length);
delete String.prototype.zzz;
for (var i = 0; i < 400; i++) assertEq(readZ(strs[i % 4]), undefined);

// Across GCs, which zero and refill every row.
for (var i = 0; i < 2000; i++) {
  if (i % 500 == 0) gc();
  if (i % 77 == 0) minorgc();
  assertEq(readRef(plain[i % 4]), i % 4 == 2 ? "own" : undefined);
  assertEq(readZ(strs[i % 4]), undefined);
  assertEq(readDP(Comp2), undefined);
}
