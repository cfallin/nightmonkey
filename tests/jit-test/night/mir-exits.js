// MIR bodies (`--pipeline mir`) and their exits into baseline: every
// function here is in the MIR builder's subset, and each case leaves the
// fast path somewhere -- a failed overflow check mid-loop, a type the
// entry guards did not expect, a generic op that throws. The results must
// match the interpreter's. (Other lanes run the same code, unexited.)

// int32 overflow mid-loop: the add's check fails, and baseline finishes
// the loop from that iteration.
function sumFrom(start, n) {
  var s = start;
  for (var i = 0; i < n; i++) s += i;
  return s;
}
assertEq(sumFrom(0, 100), 4950);
assertEq(sumFrom(2147483000, 100), 2147487950);
assertEq(sumFrom(-2147483000, 100), -2147478050);

// Inc/Dec and Neg at the edges. (Each checked function stays inside the
// builder's subset: no array or string literals.)
function inc(x) { var a = x; a++; return a; }
function dec(x) { var a = x; a--; return a; }
function neg(x) { return -x; }
assertEq(inc(2147483647), 2147483648);
assertEq(dec(2147483647), 2147483646);
assertEq(neg(2147483647), -2147483647);
assertEq(inc(-2147483648), -2147483647);
assertEq(dec(-2147483648), -2147483649);
assertEq(neg(-2147483648), 2147483648);
assertEq(Object.is(neg(0), -0), true);
assertEq(inc(1.5), 2.5);

// Mul's -0 and overflow checks.
function mul(a, b) { return a * b; }
assertEq(mul(3, 4), 12);
assertEq(Object.is(mul(0, -3), -0), true);
assertEq(mul(65536, 65536), 4294967296);

// A loop whose accumulator changes type: int32, then double, then string.
function mixed(n, ex) {
  var s = 0;
  for (var i = 0; i < n; i++) {
    if (i == 5) s = s + 0.5;
    if (i == 8) s = s + ex;
    s = s + 1;
  }
  return s;
}
assertEq(mixed(4, "!"), 4);
assertEq(mixed(7, "!"), 7.5);
assertEq(mixed(10, "!"), "8.5!11");

// Arguments of unexpected types reach the generic path.
function add(a, b) { return a + b; }
for (var k = 0; k < 50; k++) assertEq(add(k, 1), k + 1);
assertEq(add("x", 1), "x1");
assertEq(add(1.5, 1.25), 2.75);
assertEq(add(undefined, 1) !== add(undefined, 1), true);
assertEq(add(true, true), 2);

// A generic op that throws: the throw exit hands the pending exception
// to baseline, which propagates it.
var thrower = { valueOf() { throw new Error("boom"); } };
var caught = null;
try { add(thrower, 1); } catch (e) { caught = e.message; }
assertEq(caught, "boom");
function lt(a, b) { return a < b; }
caught = null;
try { lt(1, thrower); } catch (e) { caught = e.message; }
assertEq(caught, "boom");
var calls = 0;
var counter = { valueOf() { calls++; return 3; } };
assertEq(add(counter, 1), 4);
assertEq(calls, 1);

// Doubles: NaN compares, -0, ToBoolean.
function le(a, b) { return a <= b; }
function eq(a, b) { return a == b; }
function seq(a, b) { return a === b; }
function ne(a, b) { return a != b; }
function cmp(a, b) {
  var r = 0;
  if (lt(a, b)) r = r + 1;
  if (le(a, b)) r = r + 2;
  if (eq(a, b)) r = r + 4;
  if (seq(a, b)) r = r + 8;
  if (ne(a, b)) r = r + 16;
  return r;
}
assertEq(cmp(NaN, NaN), 16);
assertEq(cmp(0, -0), 2 + 4 + 8);
assertEq(cmp(1.5, 2), 1 + 2 + 16);
assertEq(cmp(2, 2), 2 + 4 + 8);
assertEq(cmp(1, "1"), 2 + 4);
function not(x) { return !x; }
assertEq(not(0), true);
assertEq(not(-0), true);
assertEq(not(NaN), true);
assertEq(not(0.5), false);
assertEq(not(""), true);
assertEq(not("a"), false);
assertEq(not(null), true);
assertEq(not(thrower), false);
function div(a, b) { return a / b; }
assertEq(div(1, 0), Infinity);
assertEq(Object.is(div(0, -1), -0), true);
assertEq(div(7, 2), 3.5);

// ToInt32 on doubles, and >>> producing values above 2^31.
function or0(a) { return a | 0; }
function and(a, b) { return a & b; }
function xor(a, b) { return a ^ b; }
function shl(a) { return a << 1; }
function shr(a) { return a >> 1; }
function ushr(a) { return a >>> 0; }
function bnot(a) { return ~a; }
function bits(a, b) {
  return String([or0(a), and(a, b), xor(a, b), shl(a), shr(a), ushr(a), bnot(a)]);
}
assertEq(bits(2.9, 7), "2,2,5,4,1,2,-3");
assertEq(bits(-2.9, 7), "-2,6,-7,-4,-1,4294967294,1");
assertEq(bits(4294967297.5, 3), "1,1,2,2,0,1,-2");
assertEq(bits(-1, 1), "-1,1,-2,-2,-1,4294967295,0");
assertEq(bits(1e21, 0), "-559939584,0,-559939584,-1119879168,-279969792,3735027712,559939583");
assertEq(bits(NaN, Infinity), "0,0,0,0,0,0,-1");
assertEq(bits(-2147483648.5, -1), "-2147483648,-2147483648,2147483647,0,-1073741824,2147483648,2147483647");

// A nested loop with an exit in the inner loop.
function nest(n) {
  var t = 0;
  for (var i = 0; i < n; i++)
    for (var j = 0; j < n; j++)
      t += i * j * 1000000;
  return t;
}
assertEq(nest(3), 9000000);
assertEq(nest(60), 3132900000000);
