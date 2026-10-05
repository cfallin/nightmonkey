// A for-in's start in MIR from the iterator its object's shape caches (the
// JIT's ObjectToIterator): the iterator is reused only when no for-in is
// using it, its object and prototypes have no dense elements, and the
// prototypes' shapes are the ones it recorded. Starting it stores the
// object in it raw and joins it to the compartment's active list; the
// engine reads both when a property is deleted mid-iteration (the deleted,
// unvisited key must not be visited), including after a minor GC has moved
// a nursery object (the whole-cell barrier on the iterator object).

function keys(o) {
  var r = [];
  for (var k in o) r.push(k);
  return r.join();
}

function make(i) { return { a: i, b: i + 1, c: i + 2 }; }

// The same shape over and over: the cache serves every start after the
// first.
for (var i = 0; i < 200; i++) assertEq(keys(make(i)), "a,b,c");

// Nested over the same object: the inner start finds the cached iterator
// active and must make its own.
function nested(o) {
  var r = [];
  for (var x in o) for (var y in o) r.push(x + y);
  return r.join();
}
for (var i = 0; i < 50; i++) assertEq(nested(make(i)), "aa,ab,ac,ba,bb,bc,ca,cb,cc");

// Prototypes: an enumerable prototype property is listed; adding one to the
// prototype changes its shape, so the cached iterator no longer fits.
function P() {}
P.prototype.p = 1;
function withProto(i) { var o = new P(); o.x = i; o.y = i; return o; }
for (var i = 0; i < 50; i++) assertEq(keys(withProto(i)), "x,y,p");
P.prototype.q = 2;
for (var i = 0; i < 50; i++) assertEq(keys(withProto(i)), "x,y,p,q");
delete P.prototype.p;
for (var i = 0; i < 50; i++) assertEq(keys(withProto(i)), "x,y,q");

// Dense elements on the object or a prototype: never from the cache.
function withElems(i) { var o = make(i); o[0] = 5; o[1] = 6; return o; }
for (var i = 0; i < 50; i++) assertEq(keys(withElems(i)), "0,1,a,b,c");
function Q() {}
Q.prototype[0] = 7;
function protoElems(i) { var o = new Q(); o.z = i; return o; }
for (var i = 0; i < 50; i++) assertEq(keys(protoElems(i)), "z,0");
for (var i = 0; i < 50; i++) assertEq(keys(make(i)), "a,b,c");

// A deletion mid-iteration skips the deleted key: the engine finds this
// for-in through the active list by the object it holds.
function deleting(o, gcFirst) {
  var r = [];
  for (var k in o) {
    if (k == "a") {
      if (gcFirst) minorgc();
      delete o.c;
    }
    r.push(k);
  }
  return r.join();
}
for (var i = 0; i < 100; i++) {
  assertEq(deleting(make(i), false), "a,b");
  // A fresh object is in the nursery: the minor GC moves it, so the
  // iterator must have been traced to follow it.
  assertEq(deleting(make(i), true), "a,b");
}

// Many for-ins at once, each closing in turn: the list stays well formed
// (a broken link would show at the next deletion or in a GC).
function many(n) {
  var t = 0;
  var objs = [];
  for (var i = 0; i < n; i++) objs.push({ u: i, v: i, w: i });
  function rec(j) {
    if (j == n) return 0;
    var s = 0;
    for (var k in objs[j]) {
      s += objs[j][k] + rec(j + 1);
      if (k == "u") delete objs[j].w;
      break;
    }
    return s;
  }
  t += rec(0);
  for (var i = 0; i < n; i++) assertEq(keys(objs[i]), "u,v");
  gc();
  return t;
}
for (var i = 0; i < 20; i++) assertEq(many(8), 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7);
