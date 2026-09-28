// The iterator protocol and spread in MIR: for-of over arrays (the
// optimized path), strings, Maps, generators and user iterators; an early
// exit closing the iterator (`return` called); a non-callable
// `Symbol.iterator` and a non-object `next()` result throwing; spread
// calls and `new` with spread; array spread.

function sumOf(xs) {
  var t = 0;
  for (var x of xs) t += x;
  return t;
}
function firstBig(xs, lim) {
  for (var x of xs) {
    if (x > lim) return x;
  }
  return -1;
}
function* gen(n) { for (var i = 0; i < n; i++) yield i; }

var closed = 0;
function counter(n) {
  var i = 0;
  var it = {
    next() { return i < n ? { value: i++, done: false } : { value: undefined, done: true }; },
    return() { closed++; return {}; },
  };
  return { [Symbol.iterator]() { return it; } };
}
function badNext() {
  return { [Symbol.iterator]() { return { next() { return 3; } }; } };
}

function add3(a, b, c) { return a + b * 10 + c * 100; }
function spreadIt(xs) { return add3(...xs); }
function P(a, b) { this.a = a; this.b = b; }
function newSpread(xs) { var p = new P(...xs); return p.a - p.b; }
function arrSpread(xs, ys) { return [...xs, 0, ...ys].length; }

class K {
  constructor(x) { this.x = x; }
  get twice() { return this.x * 2; }
}
function makeK(i) { return new K(i).twice; }

var m = new Map([[1, 2], [3, 4]]);
for (var r = 0; r < 400; r++) {
  assertEq(sumOf([1, 2, 3, r]), 6 + r);
  assertEq(sumOf("123".split("").map(Number)), 6);
  assertEq(sumOf(gen(5)), 10);
  assertEq(sumOf(new Set([4, 5])), 9);
  var kv = 0;
  for (var [k, v] of m) kv += k * v;
  assertEq(kv, 14);
  var c0 = closed;
  assertEq(firstBig(counter(10), 4), 5);
  assertEq(closed, c0 + 1);
  assertEq(firstBig(counter(3), 4), -1);
  assertEq(closed, c0 + 1);

  var e = null;
  try { sumOf({ [Symbol.iterator]: 3 }); } catch (x) { e = x; }
  assertEq(e instanceof TypeError, true);
  e = null;
  try { sumOf(badNext()); } catch (x) { e = x; }
  assertEq(e instanceof TypeError, true);
  e = null;
  try { sumOf(r); } catch (x) { e = x; }
  assertEq(e instanceof TypeError, true);

  assertEq(spreadIt([1, 2, 3]), 321);
  assertEq(spreadIt(gen(3)), 210);
  assertEq(newSpread([r, 1]), r - 1);
  assertEq(arrSpread([1, 2], gen(3)), 6);
  assertEq(makeK(r), 2 * r);
  e = null;
  try { K(r); } catch (x) { e = x; }
  assertEq(e instanceof TypeError, true);
}
