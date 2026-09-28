// Element stores past the initialized length or into holes take MIR's
// call-free append arm when the append cache proves them plain: the
// array grows, a plain object's elements grow without a length, and a
// frozen or non-extensible array, a sparse store, or an indexed setter on
// the prototype chain still behave as the engine's.

function fill(a, n) { for (var i = 0; i < n; i++) a[i] = i * 3; return a; }
function fillDown(a, n) { for (var i = n - 1; i >= 0; i--) a[i] = i; return a; }
function put(a, i, v) { a[i] = v; return a; }

for (var round = 0; round < 60; round++) {
  var a = fill([], 50);
  assertEq(a.length, 50);
  assertEq(a[49], 147);
  var o = fill({}, 10);
  assertEq(o.length, undefined);
  assertEq(o[9], 27);
  var d = fillDown(new Array(20), 20);
  assertEq(d.length, 20);
  assertEq(d.join(","), "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19");
  var h = [1, , 3];
  put(h, 1, "x");
  assertEq(h.join(), "1,x,3");
  var s = put([], 100, 7);
  assertEq(s.length, 101);
  assertEq(1 in s, false);
  var f = Object.freeze([1, 2]);
  put(f, 2, 9);
  assertEq(f.length, 2);
  var ne = Object.preventExtensions([1]);
  put(ne, 1, 9);
  assertEq(ne.length, 1);
  var objs = fill([], 5);
  put(objs, 5, { k: round });
  assertEq(objs[5].k, round);
}

var hits = 0;
Object.defineProperty(Array.prototype, 3, {
  set: function (v) { hits++; },
  configurable: true,
});
var p = fill([], 6);
assertEq(hits, 1);
assertEq(p.length, 6);
assertEq(p.hasOwnProperty(3), false);
delete Array.prototype[3];
var q = fill([], 6);
assertEq(q[3], 9);
