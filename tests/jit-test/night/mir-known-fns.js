// Calls of closures the frame knows: a lambda called where it is made,
// and one passed to a helper that is inlined, whose call of its formal
// then has exactly that callee (context-sensitive: the helper's own
// call site sees every lambda any caller passes). The helpers also run
// with other callees, a non-function, and a loop header onramp, so the
// known-callee paths meet everything else.

function each(a, f) {
  var s = 0;
  for (var i = 0; i < a.length; i++) s += f(a[i], i);
  return s;
}
function apply2(f, x) { return f(x) + f(x + 1); }

function sumSquares(a) { return each(a, function (x) { return x * x; }); }
function sumIdx(a) { return each(a, function (x, i) { return i; }); }
function twice(n) { return apply2(function (y) { return y * 2; }, n); }
function local(n) {
  var g = function (z) { return z + n; };
  return g(1) + g(2);
}
function reassigned(n, h) {
  var g = function (z) { return z - 1; };
  if (n % 7 == 0) g = h;
  return g(n);
}

var arr = [1, 2, 3, 4];
for (var n = 0; n < 300; n++) {
  assertEq(sumSquares(arr), 30);
  assertEq(sumIdx(arr), 6);
  assertEq(twice(n), 4 * n + 2);
  assertEq(local(n), 2 * n + 3);
  assertEq(reassigned(n, function (z) { return z * 10; }), n % 7 == 0 ? n * 10 : n - 1);
  assertEq(each(arr, Math.max), 1 + 2 + 3 + 4);
  assertEq(apply2(String, n), String(n) + String(n + 1));
}
var threw = false;
try { each(arr, 5); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);
