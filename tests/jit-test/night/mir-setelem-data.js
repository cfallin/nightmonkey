// `setelem.data` (a generic element store by an int32 key that runs no
// code): overwrites, appends and sparse adds of native objects' and
// arrays' elements, and numbers to typed arrays, store in MIR; a store
// that would run code (an indexed setter on the object or a prototype, a
// proxy, a typed array's valueOf) or be refused (frozen elements, a
// non-extensible object, a non-writable length) exits before the store for
// baseline to do it. Every case must match the spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + String(got) + ", want " + String(want));
}

// Receivers of no static type, int32 keys.
function fill(o, n, v) {
  for (var i = 0; i < n; i++) o[i] = v + i;
  return o;
}
function put(o, i, v) { o[i] = v; return o; }

for (var k = 0; k < 30; k++) {
  var a = fill([], 4, k);
  check(a.length, 4, "appended length");
  check(a[3], k + 3, "appended");
  fill(a, 2, 100);
  check(a[1], 101, "overwritten");
  put(a, 10, "far");
  check(a.length, 11, "sparse add length");
  check(5 in a, false, "hole");
  var o = fill({}, 3, 1);
  check(o[2], 3, "object elements");
  var t = fill(new Float64Array(3), 3, 0.5);
  check(t[2], 2.5, "typed array");
  put(t, 7, 1);
  check(t.length, 3, "typed array out of range ignored");
  var u = put(new Uint8Array(2), 0, 300);
  check(u[0], 44, "typed array wraps");
}

// An indexed setter on a prototype runs (the add exits; baseline sets).
var seen = [];
Object.defineProperty(Array.prototype, 2, {
  set: function (v) { seen.push(v); },
  get: function () { return "proto"; },
  configurable: true,
});
var b = fill([], 3, 7);
check(seen.join(), "9", "setter ran");
check(b.hasOwnProperty(2), false, "no own [2]");
delete Array.prototype[2];

// An own indexed setter, a proxy.
var calls = 0;
var c = [0, 0];
Object.defineProperty(c, 1, { set: function (v) { calls++; }, get: function () { return -1; } });
fill(c, 2, 5);
check(calls, 1, "own setter");
check(c[0], 5, "plain element beside it");
var traps = 0;
var p = new Proxy([], { set: function (t, k, v) { traps++; t[k] = v; return true; } });
fill(p, 2, 1);
check(traps, 2, "proxy set traps");

// Refused stores: frozen, non-extensible, non-writable length (sloppy:
// ignored).
var f = Object.freeze([1, 2]);
fill(f, 2, 9);
check(f[0], 1, "frozen kept");
var ne = Object.preventExtensions([1]);
fill(ne, 2, 9);
check(ne[0], 9, "non-extensible overwrite");
check(ne.length, 1, "non-extensible: no add");
var nl = [1];
Object.defineProperty(nl, "length", { writable: false });
put(nl, 1, 2);
check(nl.length, 1, "non-writable length");
check(1 in nl, false, "no add past a non-writable length");

// A typed array of a value whose conversion runs user code.
calls = 0;
var obj = { valueOf: function () { calls++; return 4; } };
var ta = new Int32Array(2);
put(ta, 1, obj);
check(ta[1], 4, "valueOf stored");
check(calls, 1, "valueOf ran once");

// Strict mode: the refused stores throw.
function putStrict(o, i, v) { "use strict"; o[i] = v; }
for (var k = 0; k < 30; k++) putStrict([], 0, k);
for (var bad of [f, ne]) {
  var threw = false;
  try { putStrict(bad, 5, 1); } catch (e) { threw = e instanceof TypeError; }
  check(threw, true, "strict refused store throws");
}

// In a loop through an invariant receiver: field reads hoist past the
// element stores (which write only elements and lengths).
function scale(o, a, n) {
  for (var i = 0; i < n; i++) a[i] = a[i] * o.f;
  return a;
}
for (var k = 0; k < 50; k++) check(scale({ f: 3 }, [1, 2, 3], 3).join(), "3,6,9", "scale");
