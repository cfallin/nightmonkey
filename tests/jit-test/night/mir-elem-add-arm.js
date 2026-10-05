// `obj[key] = v` adding an atom-named property, in MIR: the transition the
// runtime learned for (the object's shape, the key) replayed from the
// element-add table, as a named add site replays its own row. Everything
// the replay must not do itself goes back to the runtime: another key or
// shape, a prototype that changed (a setter added), a non-extensible
// object, a dynamic slot.

function copy(src) {
  var dst = {};
  for (var k in src) dst[k] = src[k];
  return dst;
}
function strictCopy(src, dst) {
  "use strict";
  for (var k in src) dst[k] = src[k];
  return dst;
}
function keysVals(o) {
  var r = [];
  for (var k in o) r.push(k + "=" + (typeof o[k] == "object" ? JSON.stringify(o[k]) : o[k]));
  return r.join(",");
}

var srcs = [
  { className: "a", id: 1 },
  { className: "b", id: 2.5, title: "t" },
  { href: { x: 1 }, rel: "r" },
  { a: 1, b: 2, c: 3, d: 4, e: 5, f: 6, g: 7 },      // past the fixed slots
  { "0": "zero", name: "n" },                          // an index key
];
for (var i = 0; i < 300; i++) {
  for (var j = 0; j < srcs.length; j++) assertEq(keysVals(copy(srcs[j])), keysVals(srcs[j]));
}

// A tenured target, nursery values, a minor GC: the store's barrier (in
// a function: the top level runs in baseline).
function barrier() {
  var targets = [];
  for (var i = 0; i < 200; i++) targets.push({});
  gc();
  for (var i = 0; i < 200; i++) {
    var t = targets[i];
    var key = i & 1 ? "left" : "right";
    t[key] = { v: i, s: "s" + i };
  }
  minorgc();
  // Reuse the nursery, so a pointer the GC did not update reads junk.
  var junk = [];
  for (var i = 0; i < 20000; i++) junk.push({ v: -1, s: "junk" });
  minorgc();
  for (var i = 0; i < 200; i++) {
    var key = i & 1 ? "left" : "right";
    assertEq(targets[i][key].v, i);
    assertEq(targets[i][key].s, "s" + i);
  }
}
for (var r = 0; r < 3; r++) barrier();

// Non-extensible: sloppy fails silently, strict throws.
for (var i = 0; i < 50; i++) {
  var ne = Object.preventExtensions({});
  assertEq(keysVals(Object.assign(copy({}), {})), "");
  var src = { className: "x", id: i };
  var d = {};
  for (var k in src) d[k] = src[k];
  assertEq(d.id, i);
  var thrown = false;
  try { strictCopy(src, ne); } catch (e) { thrown = e instanceof TypeError; }
  assertEq(thrown, true);
  assertEq(Object.keys(ne).length, 0);
}

// Delete and add again, alternating shapes.
for (var i = 0; i < 100; i++) {
  var o = copy(srcs[0]);
  delete o.className;
  o.className = "again";
  assertEq(keysVals(o), "id=1,className=again");
}

// Many keys added to one shape (the empty object's): more than the table
// has rows, so rows collide, and each add must replay its own key's.
var many = {};
for (var i = 0; i < 3000; i++) many["p" + i] = i;
function addOne(k) { var o = {}; o[k] = 1; return o; }
for (var r = 0; r < 3; r++) {
  for (var k in many) {
    var o = addOne(k);
    for (var only in o) assertEq(only, k);
  }
}

// Last: a setter for one of the keys on Object.prototype. The adds must
// call it (the prototype's shape is no longer the one the rows recorded).
for (var i = 0; i < 300; i++) copy(srcs[1]);   // the rows again, after the collisions
var set = 0;
Object.defineProperty(Object.prototype, "title", {
  set(v) { set++; },
  get() { return "proto"; },
  configurable: true,
});
for (var i = 0; i < 50; i++) {
  var o = copy(srcs[1]);
  assertEq(o.hasOwnProperty("title"), false);
  assertEq(o.title, "proto");
}
assertEq(set, 50);
