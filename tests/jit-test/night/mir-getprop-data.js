// `getprop.data` (a by-name read that runs no code) and `hoist_reads`
// (a loop's invariant read diamond moved to its preheader): a property
// read whose receiver is not of the predicted layout, or has none, reads
// data properties (own, on a prototype, absent) in MIR; a lookup that
// would run code (a getter the analysis does not know of, a proxy) or
// throw (null) exits for baseline to do it. Every case must match the
// spec, in loops whose reads are hoisted too.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + got + ", want " + want);
}

function P(x, y) { this.x = x; this.y = y; }
P.prototype.norm = function () { return this.x * this.x + this.y * this.y; };
function Q(y, x) { this.y = y; this.x = x; }

// The read site's prediction is P; Q and plain objects take the fallback.
function sumx(arr) {
  var s = 0;
  for (var i = 0; i < arr.length; i++) s += arr[i].x;
  return s;
}

var arr = [];
for (var i = 0; i < 60; i++) arr.push(i % 3 ? new P(i, 1) : new Q(1, i));
for (var k = 0; k < 50; k++) check(sumx(arr), 1770, "sumx");
check(sumx([new P(1, 2), { x: 5 }, Object.create({ x: 7 })]), 13, "own and prototype x");
check(sumx([new P(1, 2), {}]), NaN, "absent x");
check(sumx([new P(1, 2), "str"]), NaN, "string x");
check(sumx([new P(1, 2), 3]), NaN, "number x");

// A getter the analysis cannot name (installed by defineProperties): the
// read exits and baseline runs it.
var calls = 0;
var g = {};
Object.defineProperties(g, { x: { get: function () { calls++; return 100; } } });
check(sumx([new P(1, 2), g, new Q(3, 4)]), 105, "getter x");
check(calls, 1, "getter calls");

// A proxy: its get trap runs.
var traps = 0;
var prox = new Proxy({ x: 7 }, { get: function (t, k) { traps++; return t[k]; } });
check(sumx([new P(1, 2), prox]), 8, "proxy x");
check(traps, 1, "proxy traps");

// null and undefined throw a TypeError.
for (var bad of [null, undefined]) {
  var threw = false;
  try { sumx([new P(1, 2), bad]); } catch (e) { threw = e instanceof TypeError; }
  check(threw, true, "TypeError on " + bad);
}

// A loop-invariant receiver: its read diamond is hoisted. The fallback
// reads a plain data property, then a getter (an exit at the loop's
// entry, where baseline runs the loop).
function sumT(o, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s += o.x + i;
  return s;
}
for (var k = 0; k < 50; k++) check(sumT(new P(2, 0), 10), 65, "sumT P");
check(sumT({ x: 3 }, 10), 75, "sumT plain");
check(sumT(new Q(0, 4), 10), 85, "sumT Q");
calls = 0;
check(sumT(g, 4), 406, "sumT getter");
check(calls, 4, "sumT getter calls");
check(sumT(Object.create(g), 2), 201, "sumT inherited getter");

// The loop writes the field it reads: nothing is hoisted, and every
// iteration sees the new value.
function bump(o, n) {
  var s = 0;
  for (var i = 0; i < n; i++) { s += o.x; o.x = o.x + 1; }
  return s;
}
for (var k = 0; k < 50; k++) check(bump(new P(0, 0), 5), 10, "bump P");
check(bump({ x: 1 }, 4), 10, "bump plain");

// A read under a condition is not hoisted: a receiver that fails it on
// entry must not exit every time.
function cond(o, n) {
  var s = 0;
  for (var i = 0; i < n; i++) if (o) s += o.x;
  return s;
}
for (var k = 0; k < 50; k++) check(cond(new P(1, 0), 3), 3, "cond P");
check(cond(null, 3), 0, "cond null");

// The global object: a read by name sees typed global stores.
var gv = 1;
function readGlobal(n) {
  var s = 0;
  for (var i = 0; i < n; i++) { s += globalThis.gv; gv = gv + 1; }
  return s;
}
check(readGlobal(4), 1 + 2 + 3 + 4, "global reads");
check(gv, 5, "gv");

// Primitive receivers read their prototype's methods and data.
String.prototype.tag = "s";
Number.prototype.tag = "n";
function tags(a) {
  var s = "";
  for (var i = 0; i < a.length; i++) s += a[i].tag;
  return s;
}
for (var k = 0; k < 20; k++) check(tags(["a", 1, "b", 2.5, true]), "snsnundefined", "tags");
delete String.prototype.tag;
check(tags(["a", 1]), "undefinedn", "tags after delete");

// Lengths: arrays, strings, arguments, typed arrays.
function lens(a) {
  var s = 0;
  for (var i = 0; i < a.length; i++) s += a[i].length;
  return s;
}
function args() { return arguments; }
for (var k = 0; k < 20; k++) check(lens([[1, 2], "abc", args(1, 2, 3, 4), new Int8Array(5)]), 14, "lens");
