// MIR's inline dense element overwrite (`--pipeline mir`): an in-bounds,
// non-hole element of a native object's dense elements, unless frozen.
// Everything else (appends, holes, frozen or typed arrays, setters on the
// prototype chain, non-int keys) goes through the runtime.
function fill(a, n, v) { for (var i = 0; i < n; i++) a[i] = v + i; return a; }
var a = new Array(100).fill(0);
for (var n = 0; n < 20; n++) fill(a, 100, n);
assertEq(a[99], 19 + 99);
// Appends past the end, and doubles.
var b = [];
fill(b, 50, 0.5);
assertEq(b.length, 50);
assertEq(b[49], 49.5);

// Objects into a tenured array: the element post-barrier.
function fillObj(a, n) { for (var i = 0; i < n; i++) a[i] = { i: i }; }
var objs = new Array(200).fill(null);
gc();
fillObj(objs, 200);
minorgc();
gc();
var t = 0;
for (var o of objs) t += o.i;
assertEq(t, 19900);

// Holes, a frozen array, a typed array, a sparse object.
var h = [1, , 3];
fill(h, 3, 10);
assertEq(h.join(), "10,11,12");
var f = Object.freeze([1, 2, 3]);
fill(f, 3, 7);
assertEq(f.join(), "1,2,3");
function strictSet(a, i, v) { "use strict"; a[i] = v; }
for (var i = 0; i < 20; i++) strictSet(a, 0, i);
var threw = false;
try { strictSet(f, 0, 9); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);
var ta = new Int32Array(10);
fill(ta, 10, 3);
assertEq(ta[9], 12);
var sp = {};
fill(sp, 5, 1);
assertEq(sp[4], 5);

// A setter on the prototype chain for an index the array lacks.
var seen = [];
var proto = [];
Object.defineProperty(proto, 5, { set(v) { seen.push(v); } });
var c = [0, 1];
Object.setPrototypeOf(c, proto);
fill(c, 7, 100);
assertEq(seen.join(), "105");
assertEq(c[1], 101);
