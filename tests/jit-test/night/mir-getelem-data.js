// `getelem.data` (a generic element read that runs no code): elements
// (dense, holes and out of bounds through the prototypes, typed arrays,
// arguments objects, string chars) and named properties by primitive keys
// read in MIR; a read that would run code (an indexed getter, a proxy, an
// object key's toString) or throw (null, undefined) exits before the read
// for baseline to do it. Every case must match the spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + String(got) + ", want " + String(want));
}

// Receivers and keys of no static type.
function get(o, k) { return o[k]; }
function sum(o, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s += o[i];
  return s;
}

var arr = [1, 2, 3, 4];
for (var k = 0; k < 30; k++) {
  check(sum(arr, 4), 10, "dense");
  check(get(arr, 7), undefined, "out of bounds");
  check(get([1, , 3], 1), undefined, "hole");
  check(get({ a: 5 }, "a"), 5, "named");
  check(get({ a: 5 }, "b"), undefined, "absent name");
  check(get(Object.create({ p: 6 }), "p"), 6, "prototype name");
  check(get("abc", 1), "b", "string char");
  check(get("abc", 3), undefined, "string out of bounds");
  check(get("abc", "length"), 3, "string length");
  check(get(new Int16Array([5, 6]), 1), 6, "typed array");
  check(get(new Int16Array([5, 6]), 2), undefined, "typed array out of bounds");
  check(get(5, "toFixed"), Number.prototype.toFixed, "number's method");
  check(get(arr, 1.5), undefined, "non-index number");
  check(get({ "1.5": 7 }, 1.5), 7, "non-index number key");
  check(get({ "x1": 8 }, "x" + (k % 2 + 1 - (k % 2))), 8, "computed string key");
}

// A symbol key.
var sym = Symbol("s");
var so = {};
so[sym] = 9;
check(get(so, sym), 9, "symbol key");

// Holes read through prototypes with indexed properties.
Array.prototype[1] = "proto";
check(get([1, , 3], 1), "proto", "hole through Array.prototype");
delete Array.prototype[1];
check(get([1, , 3], 1), undefined, "hole after delete");

// An indexed getter (the read exits; baseline runs it).
var calls = 0;
var g = [1, 2];
Object.defineProperty(g, 1, { get: function () { calls++; return 20; } });
check(sum(g, 2), 21, "indexed getter");
check(calls, 1, "getter ran once");

// A proxy's get trap.
var traps = 0;
var p = new Proxy([3, 4], { get: function (t, k) { traps++; return t[k]; } });
check(sum(p, 2), 7, "proxy");
check(traps, 2, "proxy traps");

// An object key: its toString runs (user code), or Object.prototype's.
calls = 0;
var key = { toString: function () { calls++; return "a"; } };
check(get({ a: 11 }, key), 11, "object key toString");
check(calls, 1, "key toString ran");
check(get({ "[object Object]": 12 }, {}), 12, "plain object key");

// Arguments objects: mapped and unmapped, a deleted element.
function margs(a, b) { return sum(arguments, 2); }
function uargs(a, b) { "use strict"; return sum(arguments, 2); }
function dargs(a, b) { delete arguments[1]; return get(arguments, 1); }
for (var k = 0; k < 30; k++) {
  check(margs(1, 2), 3, "mapped arguments");
  check(uargs(3, 4), 7, "unmapped arguments");
  check(dargs(5, 6), undefined, "deleted argument");
}

// null and undefined throw.
for (var bad of [null, undefined]) {
  var threw = false;
  try { get(bad, 0); } catch (e) { threw = e instanceof TypeError; }
  check(threw, true, "TypeError on " + bad);
}

// In a loop over an invariant object: the reads hoist past the element
// reads (which write nothing).
function scaled(o, a, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s += a[i] * o.f;
  return s;
}
for (var k = 0; k < 50; k++) check(scaled({ f: 2 }, [1, 2, 3], 3), 12, "scaled");

// Past a string's end: nothing on String.prototype or Object.prototype,
// unless an index is defined there.
function scan(s) {
  var n = 0, i = 0;
  while (get(s, i) !== undefined) { n++; i++; }
  return n;
}
for (var k = 0; k < 30; k++) check(scan("hello" + k), k < 10 ? 6 : 7, "scan");
String.prototype[8] = "sp";
check(get("abc", 8), "sp", "String.prototype index");
delete String.prototype[8];
Object.prototype[9] = "op";
check(get("abc", 9), "op", "Object.prototype index");
delete Object.prototype[9];
check(get("abc", 9), undefined, "after delete");
