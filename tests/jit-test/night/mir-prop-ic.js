// MIR's property-read inline cache (`--pipeline mir`): an unpredicted
// `GetProp` probes the site's ways and the shared megamorphic table, and a
// miss runs the generic get and fills the ways. Each case changes what the
// cached ways describe after the site is hot.
function A() {}
A.prototype.m = function () { return 1; };
function callM(o) { return o.m(); }
var a = new A();
for (var i = 0; i < 100; i++) assertEq(callM(a), 1);

// The prototype's method is replaced, then shadowed on the instance, then
// deleted from both.
A.prototype.m = function () { return 2; };
assertEq(callM(a), 2);
a.m = function () { return 3; };
assertEq(callM(a), 3);
delete a.m;
assertEq(callM(a), 2);
delete A.prototype.m;
var threw = false;
try { callM(a); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);

// The prototype itself is swapped.
function B() {}
B.prototype.k = 10;
function getK(o) { return o.k; }
var b = new B();
for (var i = 0; i < 100; i++) assertEq(getK(b), 10);
Object.setPrototypeOf(b, { k: 20 });
assertEq(getK(b), 20);

// Many shapes through one site (megamorphic), and a getter.
var objs = [];
for (var i = 0; i < 40; i++) {
  var o = {};
  o["f" + i] = i;
  o.v = i;
  objs.push(o);
}
function getV(o) { return o.v; }
for (var n = 0; n < 5; n++) {
  var t = 0;
  for (var o of objs) t += getV(o);
  assertEq(t, 780);
}
var calls = 0;
var g = { get v() { calls++; gc(); return 7; } };
for (var i = 0; i < 20; i++) assertEq(getV(g), 7);
assertEq(calls, 20);

// Primitive receivers, and a missing property.
function len(s) { return s.length; }
for (var i = 0; i < 50; i++) assertEq(len("abc"), 3);
assertEq(len([1, 2]), 2);
function missing(o) { return o.nope; }
for (var i = 0; i < 50; i++) assertEq(missing({}), undefined);
threw = false;
try { missing(undefined); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);

// Property writes through the set IC: own-slot overwrites of many shapes,
// objects, a GC between, a frozen object, and a setter on the prototype.
function setV(o, v) { o.v = v; return o.v; }
for (var n = 0; n < 5; n++) {
  for (var o of objs) assertEq(setV(o, n), n);
}
var holder = { v: 0 };
gc();
for (var i = 0; i < 50; i++) setV(holder, { i: i });
minorgc();
gc();
assertEq(holder.v.i, 49);
var fr = Object.freeze({ v: 1 });
assertEq(setV(fr, 2), 1);
function strictSetV(o, v) { "use strict"; o.v = v; return o.v; }
for (var i = 0; i < 20; i++) strictSetV(holder, i);
threw = false;
try { strictSetV(fr, 3); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);
var seen = [];
var P = { set v(x) { seen.push(x); } };
var q = Object.create(P);
for (var i = 0; i < 5; i++) setV(q, i);
assertEq(seen.join(), "0,1,2,3,4");
assertEq(Object.keys(q).length, 0);
