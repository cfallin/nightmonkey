// Edges of the baseline tier's inline int32 and ToBoolean fast paths: each
// case either stays on the fast path or must fall back to the helper and
// get the generic answer.
function add(a, b) { return a + b; }
function sub(a, b) { return a - b; }
function mul(a, b) { return a * b; }
function mod(a, b) { return a % b; }
function band(a, b) { return a & b; }
function bor(a, b) { return a | b; }
function bxor(a, b) { return a ^ b; }
function lsh(a, b) { return a << b; }
function rsh(a, b) { return a >> b; }
function ursh(a, b) { return a >>> b; }
function bnot(a) { return ~a; }
function inc(a) { return ++a; }
function dec(a) { return --a; }
function postinc(a) { var r = a++; return [r, a]; }
function lt(a, b) { return a < b; }
function le(a, b) { return a <= b; }
function gt(a, b) { return a > b; }
function ge(a, b) { return a >= b; }
function eq(a, b) { return a == b; }
function ne(a, b) { return a != b; }
function seq(a, b) { return a === b; }
function sne(a, b) { return a !== b; }
function not(a) { return !a; }
function truthy(a) { if (a) return 1; return 0; }
function and(a, b) { return a && b; }
function or(a, b) { return a || b; }

const MAX = 2147483647, MIN = -2147483648;

// Int32 overflow: the result is a double, not a wrapped int32.
assertEq(add(MAX, 1), 2147483648);
assertEq(add(MIN, -1), -2147483649);
assertEq(add(1, 2), 3);
assertEq(add(1, "2"), "12");
assertEq(add(1, 0.5), 1.5);
assertEq(sub(MIN, 1), -2147483649);
assertEq(sub(MAX, -1), 2147483648);
assertEq(sub(0, MIN), 2147483648);
assertEq(sub(5, 7), -2);
assertEq(mul(65536, 65536), 4294967296);
assertEq(mul(MIN, -1), 2147483648);
assertEq(mul(-3, 7), -21);
assertEq(inc(MAX), 2147483648);
assertEq(dec(MIN), -2147483649);
assertEq(inc(-1), 0);
assertEq(dec(0), -1);
assertEq(inc(1.5), 2.5);
assertEq(inc("1"), 2);
assertEq(String(postinc(MAX)), "2147483647,2147483648");
assertEq(String(postinc("7")), "7,8");

// -0: from Mul with a negative operand, and from Sub only when the input
// is already -0 (a double).
assertEq(Object.is(mul(0, -5), -0), true);
assertEq(Object.is(mul(-5, 0), -0), true);
assertEq(Object.is(mul(0, 5), 0), true);
assertEq(Object.is(mul(0, 0), 0), true);
assertEq(Object.is(sub(0, 0), 0), true);
assertEq(Object.is(sub(-0, 0), -0), true);
assertEq(Object.is(add(-0, 0), 0), true);
assertEq(Object.is(add(-0, -0), -0), true);
assertEq(Object.is(mod(-4, 2), -0), true);
assertEq(Object.is(mod(4, 2), 0), true);
assertEq(Object.is(bnot(-1), 0), true);

// Shifts: counts are taken mod 32; >>> over 2^31 is a double.
assertEq(lsh(1, 31), MIN);
assertEq(lsh(1, 32), 1);
assertEq(lsh(1, 33), 2);
assertEq(lsh(3, -1), MIN);
assertEq(rsh(MIN, 31), -1);
assertEq(rsh(-8, 33), -4);
assertEq(ursh(-1, 0), 4294967295);
assertEq(ursh(-1, 1), MAX);
assertEq(ursh(MIN, 0), 2147483648);
assertEq(ursh(-1, 32), 4294967295);
assertEq(ursh(16, 2), 4);
assertEq(band(-1, 255), 255);
assertEq(bor(MIN, 1), -2147483647);
assertEq(bxor(-1, MAX), MIN);
assertEq(bnot(MAX), MIN);
assertEq(band(1.5, 3), 1);
assertEq(bor("8", 1), 9);

// Compares: NaN, mixed int32/double, and the equality fast path's tags.
assertEq(lt(1, 2), true);
assertEq(lt(2, 1), false);
assertEq(lt(MIN, MAX), true);
assertEq(le(3, 3), true);
assertEq(gt(-1, 0), false);
assertEq(ge(0, -1), true);
assertEq(lt(1, 1.5), true);
assertEq(lt(NaN, 1), false);
assertEq(ge(NaN, NaN), false);
assertEq(lt("10", "9"), true);
assertEq(eq(1, 1), true);
assertEq(eq(1, 1.0), true);
assertEq(eq(1, "1"), true);
assertEq(ne(1, 2), true);
assertEq(seq(1, 1), true);
assertEq(seq(1, 2), false);
assertEq(seq(1, "1"), false);
assertEq(seq(NaN, NaN), false);
assertEq(sne(NaN, NaN), true);
var nan = 0 / 0;
assertEq(seq(nan, nan), false);
assertEq(seq(0, -0), true);
assertEq(seq(-0, 0), true);
assertEq(eq(-0, 0), true);
assertEq(seq(true, true), true);
assertEq(seq(true, false), false);
assertEq(eq(true, 1), true);
assertEq(seq(undefined, undefined), true);
assertEq(seq(null, null), true);
assertEq(eq(null, undefined), true);
assertEq(seq(null, undefined), false);
var o = {}, p = {};
assertEq(seq(o, o), true);
assertEq(seq(o, p), false);
assertEq(eq(o, p), false);
assertEq(ne(o, o), false);
assertEq(seq("a" + "b", "ab"), true);
assertEq(eq(1n, 1n), true);
assertEq(seq(1n, 1), false);

// ToBoolean: inline for int32, boolean, undefined and null; everything
// else through the helper.
assertEq(truthy(0), 0);
assertEq(truthy(-1), 1);
assertEq(truthy(MIN), 1);
assertEq(truthy(true), 1);
assertEq(truthy(false), 0);
assertEq(truthy(undefined), 0);
assertEq(truthy(null), 0);
assertEq(truthy(0.5), 1);
assertEq(truthy(-0), 0);
assertEq(truthy(NaN), 0);
assertEq(truthy(""), 0);
assertEq(truthy("0"), 1);
assertEq(truthy({}), 1);
assertEq(truthy(0n), 0);
assertEq(not(0), true);
assertEq(not(7), false);
assertEq(not(null), true);
assertEq(not(NaN), true);
assertEq(not(""), true);
assertEq(and(1, 2), 2);
assertEq(and(0, 2), 0);
assertEq(and(null, 2), null);
assertEq(or(0, 2), 2);
assertEq(or(undefined, "x"), "x");
assertEq(or(3, 2), 3);
if (typeof createIsHTMLDDA === "function") {
  var dda = createIsHTMLDDA();
  assertEq(truthy(dda), 0);
  assertEq(eq(dda, undefined), true);
}

// A loop that crosses the int32 range mid-way.
function sumTo(n) {
  var s = MAX - 5;
  for (var i = 0; i < n; i++) s += 1;
  return s;
}
assertEq(sumTo(10), 2147483652);

// GetElem: the inline arm reads only in-bounds, non-hole dense elements of
// native objects; everything else must see the generic answer.
function get(o, i) { return o[i]; }
var arr = [10, 20, , 40];
assertEq(get(arr, 0), 10);
assertEq(get(arr, 3), 40);
assertEq(get(arr, 2), undefined);
assertEq(get(arr, 4), undefined);
assertEq(get(arr, -1), undefined);
Array.prototype[2] = "proto";
assertEq(get(arr, 2), "proto");
delete Array.prototype[2];
Object.prototype[7] = "oproto";
assertEq(get(arr, 7), "oproto");
delete Object.prototype[7];
var negIdx = [1];
negIdx[-1] = "minus";
assertEq(get(negIdx, -1), "minus");
assertEq(get(arr, 1.0), 20);
assertEq(get(arr, "1"), 20);
assertEq(get(arr, 1.5), undefined);
var ta = new Int32Array([5, 6, 7]);
assertEq(get(ta, 1), 6);
assertEq(get(ta, 3), undefined);
var fa = new Float64Array([0.5]);
assertEq(get(fa, 0), 0.5);
assertEq(get("abc", 1), "b");
var px = new Proxy([1, 2, 3], { get(t, k) { return "p" + k; } });
assertEq(get(px, 1), "p1");
function argsGet() { return get(arguments, 1); }
assertEq(argsGet(8, 9), 9);
var getter = [];
Object.defineProperty(getter, 0, { get() { return "g"; } });
assertEq(get(getter, 0), "g");
var frozen = Object.freeze([3, 4]);
assertEq(get(frozen, 1), 4);
var objIdx = { 0: "zero", 1: "one" };
assertEq(get(objIdx, 1), "one");
var mixed = [1, "s", {}, 2.5, null, undefined];
assertEq(get(mixed, 1), "s");
assertEq(get(mixed, 3), 2.5);
assertEq(get(mixed, 4), null);
assertEq(get(mixed, 5), undefined);
var big = [];
for (var k = 0; k < 1000; k++) big.push(k * 2);
var bs = 0;
for (var k = 0; k < 1000; k++) bs += get(big, k);
assertEq(bs, 999000);

// Double arms: IEEE results boxed as the engine's NumberValue (integral
// doubles become int32s, -0 and NaN stay doubles).
function div(a, b) { return a / b; }
function neg(a) { return -a; }
function pos(a) { return +a; }
assertEq(add(1.5, 1.5), 3);
assertEq(add(0.1, 0.2), 0.30000000000000004);
assertEq(add(MAX, 0.5), 2147483647.5);
assertEq(sub(2.5, 0.5), 2);
assertEq(mul(1.5, 2), 3);
assertEq(mul(1e200, 1e200), Infinity);
assertEq(Object.is(mul(-0.5, 0), -0), true);
assertEq(Object.is(add(-0, -0), -0), true);
assertEq(Object.is(sub(-0.0, 0.0), -0), true);
assertEq(div(1, 2), 0.5);
assertEq(div(6, 3), 2);
assertEq(div(1, 0), Infinity);
assertEq(div(-1, 0), -Infinity);
assertEq(Object.is(div(0, -1), -0), true);
assertEq(Object.is(div(0, 0), NaN), true);
assertEq(div(MIN, -1), 2147483648);
assertEq(Object.is(add(NaN, 1), NaN), true);
assertEq(Object.is(mul(Infinity, 0), NaN), true);
assertEq(mod(7, 3), 1);
assertEq(mod(7, -3), 1);
assertEq(mod(-7, 3), -1);
assertEq(Object.is(mod(0, 5), 0), true);
assertEq(Object.is(mod(5, 0), NaN), true);
assertEq(mod(MIN, -1) === 0, true);
assertEq(mod(5.5, 2), 1.5);
assertEq(Object.is(neg(0), -0), true);
assertEq(Object.is(neg(-0), 0), true);
assertEq(neg(MIN), 2147483648);
assertEq(neg(5), -5);
assertEq(neg(2.5), -2.5);
assertEq(neg("3"), -3);
assertEq(pos("4"), 4);
assertEq(Object.is(pos(-0), -0), true);
assertEq(inc(0.5), 1.5);
assertEq(dec(0.5), -0.5);
assertEq(inc(2147483647.5), 2147483648.5);
assertEq(inc(NaN) !== inc(NaN), true);
assertEq(lt(0.5, 1), true);
assertEq(lt(1, 0.5), false);
assertEq(le(NaN, NaN), false);
assertEq(gt(Infinity, MAX), true);
assertEq(ge(-0, 0), true);
assertEq(eq(0.5, 0.5), true);
assertEq(seq(3, 3.0), true);
assertEq(seq(div(6, 2), 3), true);
assertEq(ne(NaN, NaN), true);
assertEq(truthy(0.0000001), 1);
assertEq(truthy(-Infinity), 1);
assertEq(not(-0), true);
assertEq(not(0.5), false);
assertEq(and(NaN, 1) !== and(NaN, 1), true);
assertEq(or(-0, "d"), "d");
// An integral double result must behave as an int32 afterwards.
var ix = [7, 8, 9];
assertEq(get(ix, div(4, 2)), 9);
assertEq(get(ix, add(0.5, 0.5)), 8);
