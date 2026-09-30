// Typed `%` and range-proven integer arithmetic in MIR (`--pipeline mir`):
// int32 `%` is `i32.rem.ovf`, failing on a zero divisor (NaN) and on a -0
// result (a negative dividend with remainder 0, INT_MIN % -1) into
// baseline; number `%` is fmod; and an op whose operands' ranges prove an
// int32 result (masked operands, a nonzero constant divisor) takes no
// check at all. Every case must match the spec.
function same(x, y) { return Object.is(x, y); }
function check(got, want, what) {
  if (!same(got, want)) throw new Error(what + " = " + got + ", want " + want);
}

function imod(a, b) { return a % b; }
function dmod(a, b) { return a % b; }
// Ranges: (a & 0xff) % 7 cannot fail; (a & 0xffff) * (b & 0x7fff) fits
// int32; (a & 0xffff) * (b & 0xffff) may not, and is checked.
function masked_mod(a) { return (a & 0xff) % 7; }
function masked_mul(a, b) { return (a & 0xffff) * (b & 0x7fff); }
function wide_mul(a, b) { return (a & 0xffff) * (b & 0xffff); }
function shr_mul(a, b) { return (a >> 16) * (b >> 16); }
// A remainder that reaches ToInt32 only.
function hash(s, n) {
  var h = 0;
  for (var i = 0; i < n; i++) h = ((h * 31) + (s & 0x3ff) + i) % 1000003 | 0;
  return h;
}

// The exact product of two integers, with the sign rule for zero (BigInt
// has no -0).
function imul_ref(x, y) {
  var p = Number(BigInt(x) * BigInt(y));
  return p === 0 && (x < 0) != (y < 0) ? -0 : p;
}

// Literal arguments, so the analysis types each call exactly.
function ints() {
  check(imod(7, 3), 1, "7 % 3");
  check(imod(-7, 3), -1, "-7 % 3");
  check(imod(7, -3), 1, "7 % -3");
  check(imod(-7, -3), -1, "-7 % -3");
  check(imod(6, 3), 0, "6 % 3");
  check(imod(2147483647, 10), 7, "INT_MAX % 10");
  check(imod(-2147483648, 10), -8, "INT_MIN % 10");
  check(imod(0, 5), 0, "0 % 5");
}
// Each fails `i32.rem.ovf` into baseline.
function edges() {
  check(imod(-6, 3), -0, "-6 % 3");
  check(imod(-2147483648, -1), -0, "INT_MIN % -1");
  check(imod(5, 0), NaN, "5 % 0");
  check(imod(0, 0), NaN, "0 % 0");
}
function dbls() {
  check(dmod(7.5, 2.5), 0, "7.5 % 2.5");
  check(dmod(-7.5, 2), -1.5, "-7.5 % 2");
  check(dmod(7.25, 2.5), 2.25, "7.25 % 2.5");
  check(dmod(1e300, 7.5), 1e300 % 7.5, "1e300 % 7.5");
  check(dmod(Infinity, 2.5), NaN, "Infinity % 2.5");
  check(dmod(5.5, Infinity), 5.5, "5.5 % Infinity");
  check(dmod(-0, 5.5), -0, "-0 % 5.5");
}
for (var n = 0; n < 2000; n++) {
  ints();
  if (n % 100 == 0) edges();
  dbls();
  var a = n * 7919 - 5000000, b = n * 104729 + 12345;
  check(masked_mod(a), (a & 0xff) - 7 * Math.floor((a & 0xff) / 7), "masked_mod(" + a + ")");
  check(masked_mul(a, b), Number(BigInt(a & 0xffff) * BigInt(b & 0x7fff)), "masked_mul");
  check(wide_mul(a, b), Number(BigInt(a & 0xffff) * BigInt(b & 0xffff)), "wide_mul");
  check(shr_mul(a, b), imul_ref(a >> 16, b >> 16), "shr_mul");
}
var h = 0n;
for (var i = 0; i < 1000; i++) h = (h * 31n + BigInt(12345 & 0x3ff) + BigInt(i)) % 1000003n;
check(hash(12345, 1000), Number(h), "hash(12345, 1000)");
