// MIR's builtin arms for `Array.prototype.push(v)` and `pop()` on dense
// arrays: an append within capacity (the receiver's shape in the append
// cache, its protos unchanged) and a shrink by one run inline. Growth,
// holes, non-writable length, indexed properties on the prototype, sparse
// receivers and monkeypatched natives take the generic call.
function fill(a, n) { for (var i = 0; i < n; i++) a.push(i * 2); return a.length; }
function drain(a) { var s = 0, x; while (a.length > 0) { x = a.pop(); s = (s + x) | 0; } return s; }
function pushObj(a, n) { for (var i = 0; i < n; i++) a.push({ v: i }); return a[n - 1].v; }
function popOne(a) { return a.pop(); }
function pushRet(a, v) { return a.push(v); }
for (var n = 0; n < 40; n++) {
  var a = [];
  assertEq(fill(a, 100), 100);
  assertEq(a[99], 198);
  assertEq(drain(a), 9900);
  assertEq(a.length, 0);
  assertEq(popOne(a), undefined);
  assertEq(pushObj([], 50), 49);
  assertEq(pushRet([1, 2], 3), 3);
  // A hole at the end: pop reads through the prototype chain.
  var h = [1, 2, , ];
  h.length = 3;
  assertEq(popOne(h), undefined);
  assertEq(h.length, 2);
}
// Non-writable length: push throws, pop throws.
var f = [1, 2, 3];
Object.defineProperty(f, "length", { writable: false });
var threw = false;
try { pushRet(f, 4); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);
threw = false;
try { popOne(f); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);
// An indexed setter on the prototype sees the push.
var seen = -1;
Object.defineProperty(Array.prototype, 5, { set: function (v) { seen = v; }, configurable: true });
var p = [0, 1, 2, 3, 4];
pushRet(p, 42);
assertEq(seen, 42);
assertEq(p.length, 6);
delete Array.prototype[5];
// A plain object with push borrowed.
var o = { length: 0, push: Array.prototype.push, pop: Array.prototype.pop };
assertEq(pushRet(o, 7), 1);
assertEq(o[0], 7);
assertEq(popOne(o), 7);
// Monkeypatched natives.
Array.prototype.push = function (v) { return -v; };
assertEq(pushRet([], 5), -5);
Array.prototype.pop = function () { return "patched"; };
assertEq(popOne([1]), "patched");
