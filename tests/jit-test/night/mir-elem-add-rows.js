// `obj[name] = v` adding a property under a run-time atom key (a for-in's)
// replays a cached shape transition. The replay must give the object the
// same keys in the same order, never bypass a setter or a read-only
// property that appears on the prototype chain after the row was cached,
// and never add to an object that cannot take it.

function copy(src) {
  var dst = {};
  for (var k in src) dst[k] = src[k];
  return dst;
}
function C() {}
function copyInto(dst, src) {
  for (var k in src) dst[k] = src[k];
  return dst;
}

var srcs = [{ a: 1, b: 2, c: 3 }, { b: 1, a: 2 }, { x: "x", y: { z: 1 }, a: [1] }, { children: "c", key: null }];
for (var i = 0; i < 3000; i++) {
  if (i % 500 == 0) gc();
  if (i % 73 == 0) minorgc();
  var s = srcs[i % 4];
  var d = copy(s);
  assertEq(Object.keys(d).join(), Object.keys(s).join());
  for (var k in s) assertEq(d[k], s[k]);
  var e = copyInto(new C(), s);
  assertEq(Object.keys(e).join(), Object.keys(s).join());
  assertEq(Object.getPrototypeOf(e), C.prototype);
}

// A setter on the prototype, added after the rows are hot.
var seen = [];
Object.defineProperty(C.prototype, "b", { set(v) { seen.push(v); }, configurable: true });
for (var r = 0; r < 100; r++) {
  var e = copyInto(new C(), { a: r, b: r + 1 });
  assertEq(Object.keys(e).join(), "a");
  assertEq(seen[seen.length - 1], r + 1);
}
assertEq(seen.length, 100);
delete C.prototype.b;
// A read-only property on Object.prototype: the add silently fails (sloppy).
Object.defineProperty(Object.prototype, "c", { value: "ro", writable: false, configurable: true });
for (var r = 0; r < 100; r++) {
  var d = copy({ a: 1, c: 3 });
  assertEq(Object.keys(d).join(), "a");
  assertEq(d.c, "ro");
}
delete Object.prototype.c;
for (var r = 0; r < 100; r++) assertEq(copy({ a: 1, c: 3 }).c, 3);
// In strict code the same store throws.
function strictCopy(src) { "use strict"; var dst = {}; for (var k in src) dst[k] = src[k]; return dst; }
for (var r = 0; r < 100; r++) assertEq(strictCopy({ a: 1, b: 2 }).b, 2);
Object.defineProperty(Object.prototype, "b", { value: "ro", writable: false, configurable: true });
var threw = false;
try { strictCopy({ a: 1, b: 2 }); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);
delete Object.prototype.b;
// Objects that cannot take the property.
var frozen = Object.freeze({});
var sealed = Object.seal({ a: 0 });
for (var r = 0; r < 100; r++) {
  copyInto(frozen, { a: 1 });
  assertEq(Object.keys(frozen).length, 0);
  copyInto(sealed, { a: r, b: 2 });
  assertEq(Object.keys(sealed).join(), "a");
  assertEq(sealed.a, r);
}
// The global object keeps its own path.
for (var r = 0; r < 50; r++) copyInto(globalThis, { addedByCopy: r });
assertEq(globalThis.addedByCopy, 49);
