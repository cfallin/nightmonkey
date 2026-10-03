// `arr.push(a, b, ...)` with several arguments stores them inline when the
// array has room for all of them; any obstacle (no room for the last one, a
// frozen or non-extensible array, a non-writable length, an indexed
// prototype, a holey array, a non-array) takes the call, which must see the
// array untouched.

function push2(a, x, y) { return a.push(x, y); }
function push5(a, x) { return a.push(x, x + 1, x + 2, x + 3, x + 4); }
function push8(a) { return a.push(1, 2, 3, 4, 5, 6, 7, 8); }

var arr = [];
var want = [];
for (var i = 0; i < 2000; i++) {
  if (i % 300 == 0) gc();
  if (i % 41 == 0) minorgc();
  var n;
  switch (i % 3) {
    case 0: n = push2(arr, i, { o: i }); want.push(i, { o: i }); break;
    case 1: n = push5(arr, i); want.push(i, i + 1, i + 2, i + 3, i + 4); break;
    default: n = push8(arr); want.push(1, 2, 3, 4, 5, 6, 7, 8); break;
  }
  assertEq(n, want.length);
  assertEq(arr.length, want.length);
}
for (var i = 0; i < want.length; i++) {
  if (typeof want[i] == "object") assertEq(arr[i].o, want[i].o);
  else assertEq(arr[i], want[i]);
}

// Room for some but not all: every capacity boundary.
for (var start = 0; start < 40; start++) {
  var a = [];
  for (var k = 0; k < start; k++) a.push(k);
  assertEq(push5(a, 100), start + 5);
  for (var k = 0; k < 5; k++) assertEq(a[start + k], 100 + k);
}

// Obstacles.
var frozen = Object.freeze([1, 2]);
var sealed = Object.seal([1, 2]);
var nonext = Object.preventExtensions([1, 2]);
var fixedLen = [1, 2];
Object.defineProperty(fixedLen, "length", { writable: false });
for (var r = 0; r < 100; r++) {
  for (var x of [frozen, sealed, nonext, fixedLen]) {
    var threw = false;
    try { push2(x, 3, 4); } catch (e) { threw = e instanceof TypeError; }
    assertEq(threw, true);
    assertEq(x.length, 2);
    assertEq(2 in x, false);
  }
}
// A holey array and an array-like.
var holey = [1, , 3];
assertEq(push2(holey, 4, 5), 5);
assertEq(1 in holey, false);
assertEq(holey[4], 5);
var like = { length: 1, 0: "a" };
assertEq(Array.prototype.push.call(like, "b", "c"), 3);
assertEq(like[2], "c");
// An indexed property on the prototype, appearing after the arm has run.
var pa = [];
for (var r = 0; r < 200; r++) push2(pa, r, r);
var setterHits = [];
Object.defineProperty(Array.prototype, 400, { set(v) { setterHits.push(v); }, configurable: true });
push2(pa, "x", "y");
assertEq(setterHits.join(), "x");
assertEq(pa.length, 402);
assertEq(pa[401], "y");
delete Array.prototype[400];
// A replaced push.
var orig = Array.prototype.push;
Array.prototype.push = function () { return "mine"; };
assertEq(push5([], 1), "mine");
Array.prototype.push = orig;
assertEq(push5([], 1), 5);
