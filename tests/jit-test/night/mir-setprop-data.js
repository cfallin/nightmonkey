// `setprop.data` (a by-name store that runs no code and demotes no
// claim): an overwrite of a plain object's own writable data property, or
// a plain add, stores in MIR; a setter the analysis does not know of, a
// read-only or non-extensible target, a proxy, a prototype or the global
// exits before the store for baseline to do it. Every case must match the
// spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + got + ", want " + want);
}

function P(x) { this.x = x; this.y = 0; }
function Q(y, x) { this.y = y; this.x = x; }

// The store site's prediction is P; Q and plain objects take the fallback.
function setAll(arr, v) {
  for (var i = 0; i < arr.length; i++) arr[i].x = v;
}
function sumx(arr) {
  var s = 0;
  for (var i = 0; i < arr.length; i++) s += arr[i].x;
  return s;
}
var arr = [];
for (var i = 0; i < 30; i++) arr.push(i % 3 ? new P(i) : new Q(0, i));
for (var k = 0; k < 50; k++) {
  setAll(arr, k);
  check(sumx(arr), 30 * k, "setAll " + k);
}

// Adds: a plain object without the property gets it.
var fresh = [new P(1), {}, { y: 1 }];
setAll(fresh, 5);
check(fresh[1].x, 5, "added x");
check(Object.keys(fresh[2]).join(), "y,x", "add order");

// A setter the analysis cannot name: the store exits, baseline runs it.
var seen = [];
var g = {};
Object.defineProperties(g, { x: { set: function (v) { seen.push(v); }, get: function () { return -1; } } });
setAll([new P(1), g], 7);
check(seen.join(), "7", "setter ran once");
check(g.x, -1, "setter's getter");

// An inherited setter, a read-only property (sloppy: ignored), a
// non-extensible object (sloppy: no add), a frozen one.
var proto = {};
Object.defineProperties(proto, { x: { set: function (v) { seen.push("p" + v); } } });
var child = Object.create(proto);
var ro = {};
Object.defineProperties(ro, { x: { value: 3, writable: false } });
var sealed = Object.preventExtensions({});
var frozen = Object.freeze({ x: 9 });
setAll([new P(1), child, ro, sealed, frozen], 8);
check(seen.join(), "7,p8", "inherited setter");
check(child.hasOwnProperty("x"), false, "no own x on child");
check(ro.x, 3, "read-only kept");
check("x" in sealed, false, "no add to a non-extensible object");
check(frozen.x, 9, "frozen kept");

// Strict mode: the same failures throw.
function setStrict(o, v) { "use strict"; o.x = v; }
for (var k = 0; k < 30; k++) setStrict(new P(0), k);
for (var bad of [ro, sealed, frozen]) {
  var threw = false;
  try { setStrict(bad, 1); } catch (e) { threw = e instanceof TypeError; }
  check(threw, true, "strict store throws");
}

// A proxy's set trap runs.
var traps = 0;
var target = {};
var prox = new Proxy(target, { set: function (t, k, v) { traps++; t[k] = v * 2; return true; } });
setAll([new P(1), prox], 4);
check(traps, 1, "set trap");
check(target.x, 8, "trap's store");

// A prototype: stores to it go through the engine (Watchtower watches it),
// and readers through the prototype see them.
function Base() {}
Base.prototype.x = 1;
var kid = new Base();
setAll([new P(1), Base.prototype], 11);
check(kid.x, 11, "store to a prototype");

// The global object: a store by name is seen by a global read.
var gx = 1;
function setGx(o, v) { o.gx = v; }
for (var k = 0; k < 30; k++) setGx({ gx: 0 }, k);
setGx(globalThis, 12);
check(gx, 12, "store to the global");

// In a loop, through an invariant receiver: the store blocks only reads
// of its own name; reads of other fields hoist.
function fill(o, n) {
  var s = 0;
  for (var i = 0; i < n; i++) {
    o.x = i;
    s += o.y + o.x;
  }
  return s;
}
for (var k = 0; k < 50; k++) check(fill(new P(0), 5), 10, "fill P");
check(fill({ x: 0, y: 2 }, 5), 20, "fill plain");
check(fill(new Q(3, 0), 4), 18, "fill Q");

// Non-conforming values to typed fields: the class's TYPES claim is not
// for this store to keep; baseline does it, and readers still see the
// value.
function setY(o, v) { o.y = v; }
var typed = [];
for (var i = 0; i < 20; i++) typed.push(new P(i));
for (var k = 0; k < 30; k++) for (var i = 0; i < typed.length; i++) setY(typed[i], i);
setY(typed[3], "str");
check(typed[3].y, "str", "non-conforming store");
check(sumx(typed), 190, "sum after");

// An array's length: truncation drops elements, extension adds holes; a
// non-writable length is kept (strict: throws).
function setLen(a, n) { a.length = n; }
for (var k = 0; k < 30; k++) {
  var a = [1, 2, 3, 4];
  setLen(a, 2);
  check(a.length, 2, "truncated");
  check(a[2], undefined, "dropped element");
  setLen(a, 5);
  check(a.length, 5, "extended");
  check(3 in a, false, "hole");
}
var fixed = [1, 2, 3];
Object.defineProperty(fixed, "length", { writable: false });
setLen(fixed, 1);
check(fixed.length, 3, "non-writable length kept");
check(fixed[2], 3, "elements kept");

// A sealed array's truncation fails (strict: throws); a sparse
// non-configurable element stops one.
function setLenStrict(a, n) { "use strict"; a.length = n; }
for (var k = 0; k < 30; k++) setLenStrict([1, 2, 3], 1);
var sealed = Object.seal([1, 2, 3]);
var threw = false;
try { setLenStrict(sealed, 0); } catch (e) { threw = e instanceof TypeError; }
check(threw, true, "sealed truncation throws");
check(sealed.length, 3, "sealed length kept");
setLen(sealed, 0);
check(sealed.length, 3, "sloppy sealed truncation ignored");
var sparse = [1, 2, 3];
Object.defineProperty(sparse, 1, { value: 2, configurable: false });
setLen(sparse, 0);
check(sparse.length, 2, "stopped at a non-configurable element");
