// Int32 ranges through block params (`opt::narrow_ints`), an onramp's
// range guards (`opt::onramp_ranges`), products only ToInt32 sees
// (`trunc_demand` on a multiply in range), shifts by a constant, and the
// one-compare overflow check of `x + c` / `x - c`. Every compiled result
// is compared with the same computation in global code.

// A loop-invariant product of masked values: no overflow is possible, so
// the multiply needs no check; the loop-carried sum still overflows to a
// double.
function maskedProducts(x, n) {
  var lo = x & 0x3fff, hi = x >> 14;
  var s = 0, t = 0;
  for (var i = 0; i < n; i++) {
    var l = (i * 7) & 0x3fff;
    var m = hi * l + lo * l;       // in int32, but -0 when hi < 0, l == 0
    t = (t + (m >> 3) + ((m & 0x3fff) << 14)) | 0;
    s = s + hi * hi * l;           // past int32: a double
  }
  return [s, t, 1 / (hi * 0)];
}

// The loop-carried count may not keep the range its start has: a wrong
// range here makes `i * k` unchecked, which overflows silently.
function growingCount(n, k) {
  var s = 0;
  for (var i = 0; i < n; i++) s = s + i * k;
  return s;
}

// Loop-invariant ranges with an onramp: an exit inside the loop (the
// double `0.5`) sends the rest of the iteration to baseline, which then
// re-enters at the loop header through the onramp, whose range guards
// re-check the invariants.
function onrampInvariants(x, n, at) {
  var lo = x & 0xff, hi = x >> 24;
  var s = 0;
  for (var i = 0; i < n; i++) {
    var y = i;
    if (i == at) y = 0.5;
    s = (s + lo * hi * (y | 0)) | 0;
    s = s + ((lo << 20) | 0);
    s = s | 0;
  }
  return s;
}

// A product past 2^53 under ToInt32: the double rounds before `| 0` sees
// it, so it is not the wrapped int32 product, and keeps its check.
function bigMul(a, b) { var x = a | 0, y = b | 0; return (x * y) | 0; }
function maskedMul(a, b) { return ((a & 0xffff) * (b >> 16)) | 0; }

// x + c and x - c at the int32 edges.
function addC(x) { x |= 0; return x + 5; }
function subC(x) { x |= 0; return x - 5; }
function addNeg(x) { x |= 0; return x + -7; }
function subNeg(x) { x |= 0; return x - -7; }
function subMin(x) { x |= 0; return x - (-2147483648); }
function cPlus(x) { x |= 0; return 3 + x; }

function maskedProductsG(x, n) {
  var lo = x & 0x3fff, hi = x >> 14;
  var s = 0, t = 0;
  for (var i = 0; i < n; i++) {
    var l = (i * 7) & 0x3fff;
    var m = hi * l + lo * l;
    t = (t + (m >> 3) + ((m & 0x3fff) << 14)) | 0;
    s = s + hi * hi * l;
  }
  return [s, t, 1 / (hi * 0)];
}

for (var r = 0; r < 200; r++) {
  if (r % 61 == 0) gc();
  for (var x of [0, 1, 0x7fffffff, -0x80000000, -1, 123456789, -987654321, 0x3fff, -0x4000]) {
    var got = maskedProducts(x, 300);
    var want = maskedProductsG(x, 300);
    assertEq(got[0], want[0]);
    assertEq(got[1], want[1]);
    assertEq(got[2], want[2]);
  }
  assertEq(growingCount(1000, 3000000), 1498500000000);
  assertEq(growingCount(100, -50000000), -247500000000);
}

var wantOn = (function (x, n, at) {
  var lo = x & 0xff, hi = x >> 24;
  var s = 0;
  for (var i = 0; i < n; i++) {
    var y = i;
    if (i == at) y = 0.5;
    s = (s + lo * hi * (y | 0)) | 0;
    s = s + ((lo << 20) | 0);
    s = s | 0;
  }
  return s;
});
for (var r = 0; r < 100; r++) {
  for (var x of [0x7f0000ff, -0x7fffff01, 0x12345678, -1]) {
    var at = (r * 37) % 500;
    assertEq(onrampInvariants(x, 2000, at), wantOn(x, 2000, at));
  }
}

var muls = [[0x12345678, 0x9abcdef], [2147483647, 2147483647], [-2147483648, 3], [123456789, -987654321],
            [65535, 65537], [-1, -2147483648], [0, -5]];
for (var r = 0; r < 300; r++) {
  for (var p of muls) {
    var a = p[0], b = p[1];
    assertEq(bigMul(a, b), (a * b) | 0);
    assertEq(maskedMul(a, b), ((a & 0xffff) * (b >> 16)) | 0);
  }
}

var edges = [2147483647, 2147483646, 2147483642, 2147483643, -2147483648, -2147483647, -2147483643,
             -2147483644, -2147483641, -2147483642, 2147483640, 2147483641, 0, -1, 1];
for (var r = 0; r < 300; r++) {
  for (var x of edges) {
    assertEq(addC(x), x + 5);
    assertEq(subC(x), x - 5);
    assertEq(addNeg(x), x + -7);
    assertEq(subNeg(x), x - -7);
    assertEq(subMin(x), x + 2147483648);
    assertEq(cPlus(x), x + 3);
  }
}
