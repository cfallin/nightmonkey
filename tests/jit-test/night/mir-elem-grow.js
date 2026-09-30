// The runtime's append behind `store_elem.append` (mir-elem-append.js has
// the inline arm): an append the inline arm refuses (the elements must
// grow, the row is not cached yet) runs there, without JS; anything that
// is not an ordinary dense append (an indexed setter on a prototype,
// frozen elements, a non-writable length) is not done there. Every case
// must match the spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + got + ", want " + want);
}

// Fill an array by index from empty: every store appends, and the
// elements grow several times.
function fill(n) {
  var a = [];
  for (var i = 0; i < n; i++) a[i] = i * 3;
  return a;
}

// The same on a plain object's elements (no length to bump).
function fillObj(n) {
  var o = {};
  for (var i = 0; i < n; i++) o[i] = i + 1;
  return o;
}

// Overwrites and appends through one site.
function scale(a, n) {
  for (var i = 0; i < n; i++) a[i] = (a[i] | 0) + 1;
  return a;
}

for (var r = 0; r < 200; r++) {
  var a = fill(1000);
  check(a.length, 1000, "fill length");
  check(a[999], 2997, "fill[999]");
  check(a[500], 1500, "fill[500]");
  var o = fillObj(100);
  check(o[99], 100, "fillObj[99]");
  check(o.length, undefined, "fillObj.length");
  var b = scale([1, 2, 3], 6);
  check(b.length, 6, "scale length");
  check(b.join(","), "2,3,4,1,1,1", "scale");
}

// Frozen: the appends do not happen (sloppy mode: silently).
var f = Object.freeze([1, 2]);
scale(f, 4);
check(f.length, 2, "frozen length");
check(f[0], 1, "frozen[0]");

// A non-writable length: no append past it.
var nl = [1, 2];
Object.defineProperty(nl, "length", { writable: false });
scale(nl, 4);
check(nl.length, 2, "non-writable length");
check(nl[2], undefined, "non-writable length [2]");

// An indexed setter on Array.prototype: the append runs it (and the
// element is not added as an own property).
var seen = [];
Object.defineProperty(Array.prototype, 5, {
  set: function (v) { seen.push(v); },
  get: function () { return "proto"; },
  configurable: true,
});
var c = fill(8);
check(seen.length, 1, "setter calls");
check(seen[0], 15, "setter value");
check(c.hasOwnProperty(5), false, "no own [5]");
check(c[5], "proto", "c[5] through the prototype");
delete Array.prototype[5];
