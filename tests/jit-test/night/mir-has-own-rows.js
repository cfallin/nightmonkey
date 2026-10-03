// `hasOwnProperty.call(o, k)` answered from a row keyed by the receiver's
// shape and the key's atom, without leaving compiled code. The rows must
// track own adds and deletes (both reshape), never answer for a key the
// receiver's prototype holds, never answer for a receiver whose own keys
// its shape does not pin (an array's indices, a typed array, a function's
// lazily resolved name, a proxy), and survive GCs.

var hop = Object.prototype.hasOwnProperty;
function has(o, k) { return hop.call(o, k); }

var keys = Object.keys({ a: 0, b: 0, c: 0, key: 0, ref: 0, children: 0, toString: 0, 1: 0, 0: 0, length: 0, name: 0, x: 0 });
function check(o, label) {
  for (var k of keys) assertEq(has(o, k), Object.getOwnPropertyNames(o).indexOf(k) >= 0, label + " " + k);
}

var objs = [{ a: 1 }, { a: 1, b: 2 }, { b: 2, key: 3 }, { children: [] }, Object.create({ a: "proto" })];
for (var r = 0; r < 300; r++) {
  for (var o of objs) {
    for (var k in o) assertEq(has(o, k), k != "a" || o !== objs[4]);
    assertEq(has(o, "toString"), false);
  }
}
for (var o of objs) check(o, "plain");

// Adds and deletes change the answer at once.
var o = { a: 1 };
for (var r = 0; r < 300; r++) {
  assertEq(has(o, "b"), r % 2 == 1);
  if (r % 2 == 0) o.b = r; else delete o.b;
}
// A getter is an own property too.
var g = { a: 1 };
for (var r = 0; r < 200; r++) assertEq(has(g, "q"), false);
Object.defineProperty(g, "q", { get() { return 1; }, configurable: true });
for (var r = 0; r < 200; r++) assertEq(has(g, "q"), true);

// Receivers whose own keys the shape does not pin.
var arr = [1, 2, 3];
var ta = new Int8Array(4);
function fn() {}
var prox = new Proxy({}, { getOwnPropertyDescriptor(t, k) { return k == "magic" ? { value: 1, configurable: true } : undefined; } });
for (var r = 0; r < 300; r++) {
  assertEq(has(arr, "1"), arr.length > 1);
  assertEq(has(arr, "length"), true);
  if (r % 2) { arr[1] = 2; arr[2] = 3; } else arr.length = 1;
  assertEq(has(arr, "1"), r % 2 == 1);
  assertEq(has(ta, "3"), true);
  assertEq(has(ta, "4"), false);
  assertEq(has(fn, "name"), true);
  assertEq(has(fn, "prototype"), true);
  assertEq(has(prox, "magic"), true);
  assertEq(has(prox, "other"), false);
}
// Fresh functions and arguments objects, whose lazily resolved own
// properties no lookup has materialized yet: the shape does not say they
// are there. (The keys are atoms, as a for-in's are: a string literal is
// not one, and never matches a row.)
function argsOf() { return arguments; }
var [kName, kLength, kCallee, kPrototype] = Object.keys({ name: 0, length: 0, callee: 0, prototype: 0 });
for (var r = 0; r < 300; r++) {
  var f = function () {};
  var b = f.bind(null);
  assertEq(has(f, kName), true);
  assertEq(has(f, kLength), true);
  assertEq(has(f, kPrototype), true);
  assertEq(has(b, kLength), true);
  var args = argsOf(1, 2);
  assertEq(has(args, kLength), true);
  assertEq(has(args, kCallee), true);
  assertEq(has(args, kName), false);
}

// Non-atom keys (built at run time) and non-string keys.
for (var r = 0; r < 300; r++) {
  var k = "ke" + "y".repeat(1 + (r & 1));
  assertEq(has(objs[2], k), r % 2 == 0);
  assertEq(has(arr, r % 3), r % 3 < arr.length);
  assertEq(has({ 5: 1 }, 5), true);
}
var sym = Symbol("s");
var so = { [sym]: 1 };
for (var r = 0; r < 100; r++) assertEq(has(so, sym), true);

// Across GCs (the rows are zeroed and refilled).
for (var r = 0; r < 2000; r++) {
  if (r % 400 == 0) gc();
  if (r % 61 == 0) minorgc();
  var fresh = { a: r, ["k" + (r % 5)]: 1 };
  assertEq(has(fresh, "a"), true);
  assertEq(has(fresh, "k" + (r % 5)), true);
  assertEq(has(fresh, "k" + ((r + 1) % 5)), false);
}
