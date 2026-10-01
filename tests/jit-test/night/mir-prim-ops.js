// `prim.*` (a generic numeric op or compare on operands that run no code
// in it): primitives of any type compute in MIR; an object whose
// conversion calls user code (`valueOf`, `toString`, `Symbol.toPrimitive`)
// exits before the op, for baseline to run it; the op's own TypeError or
// RangeError (a Symbol operand, BigInt mixing, a BigInt divided by zero)
// throws. Every case must match the spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + String(got) + ", want " + String(want));
}

// Operands of no static type: whatever an untyped array holds.
function mul(a, b) { return a * b; }
function add(a, b) { return a + b; }
function sub(a, b) { return a - b; }
function lt(a, b) { return a < b; }
function eq(a, b) { return a == b; }
function seq(a, b) { return a === b; }
function neg(a) { return -a; }
function inc(a) { a++; return a; }
function bitand(a, b) { return a & b; }

var vals = [1, 2.5, "3", "x", true, null, undefined, -0];
for (var k = 0; k < 30; k++) {
  for (var i = 0; i < vals.length; i++) {
    for (var j = 0; j < vals.length; j++) {
      var x = vals[i], y = vals[j];
      check(mul(x, y), x * y, "mul");
      check(add(x, y), x + y, "add");
      check(sub(x, y), x - y, "sub");
      check(lt(x, y), x < y, "lt");
      check(eq(x, y), x == y, "eq");
      check(seq(x, y), x === y, "seq");
      check(bitand(x, y), x & y, "bitand");
    }
    check(neg(vals[i]), -vals[i], "neg");
    check(inc(vals[i]), +vals[i] + 1, "inc");
  }
}

// Objects whose conversion runs user code: the op exits and baseline
// calls it, once per op.
var calls = 0;
var v = { valueOf: function () { calls++; return 6; } };
var s = { toString: function () { calls++; return "s"; }, valueOf: undefined };
var p = { [Symbol.toPrimitive]: function (hint) { calls++; return hint === "number" ? 7 : "p"; } };
check(mul(v, 2), 12, "valueOf mul");
check(add(v, 1), 7, "valueOf add");
check(add("a", s), "as", "toString add");
check(sub(p, 1), 6, "toPrimitive sub");
check(add(p, 1), "p1", "toPrimitive add");
check(lt(v, 10), true, "valueOf lt");
check(eq(v, 6), true, "valueOf loose eq");
check(neg(v), -6, "valueOf neg");
check(calls, 8, "conversion calls");

// Equalities that run no code on objects: two objects, an object and null
// or undefined, and every strict one.
var o1 = {}, o2 = {};
calls = 0;
check(eq(o1, o1), true, "same object");
check(eq(o1, o2), false, "two objects");
check(eq(v, null), false, "object == null");
check(eq(undefined, v), false, "undefined == object");
check(seq(v, 6), false, "strict object");
check(calls, 0, "no conversion for these");

// The op's own errors.
function throwsType(f) {
  try { f(); } catch (e) { return e instanceof TypeError; }
  return false;
}
check(throwsType(function () { return mul(Symbol("q"), 2); }), true, "Symbol * 2");
check(throwsType(function () { return add(1n, 1); }), true, "1n + 1");
check(mul(3n, 4n), 12n, "BigInt mul");
check(add(2n, 5n), 7n, "BigInt add");
var threw = false;
try { mul(1n, 0n) / 0n; } catch (e) { threw = e instanceof RangeError; }
check(threw, true, "BigInt division by zero");
function div(a, b) { return a / b; }
threw = false;
try { div(1n, 0n); } catch (e) { threw = e instanceof RangeError; }
check(threw, true, "BigInt division by zero (generic)");

// In a loop, with an invariant receiver's fields: the ops are no writers,
// so the field reads hoist; a valueOf object exits and baseline finishes.
function dot(a, b, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s = s + a.x * b.x + a.y * b.y;
  return s;
}
var pa = { x: 1, y: 2 }, pb = { x: 3, y: "4" };
for (var k = 0; k < 50; k++) check(dot(pa, pb, 10), 110, "dot");
calls = 0;
check(dot({ x: v, y: 0 }, pb, 3), 54, "dot valueOf");
check(calls, 3, "dot valueOf calls");
check(dot({ x: "a", y: 0 }, pb, 2), NaN, "dot NaN");

// Objects whose conversion is Object.prototype's own: computed in MIR,
// with the builtin conversion's results.
var plain = {};
for (var k = 0; k < 30; k++) {
  check(add("", plain), "[object Object]", "plain concat");
  check(eq(plain, "[object Object]"), true, "plain == its string");
  check(lt(plain, 1), false, "plain < 1");
  check(mul(plain, 2), NaN, "plain * 2");
}
// A @@toStringTag getter is user code; so is an own toString, and a
// Date's @@toPrimitive is not Object.prototype's.
calls = 0;
var tagged = {};
Object.defineProperty(tagged, Symbol.toStringTag, { get: function () { calls++; return "T"; } });
check(add("", tagged), "[object T]", "toStringTag getter");
check(calls, 1, "toStringTag getter ran");
var d = new Date(5);
check(sub(d, 1), 4, "Date - 1");
check(add(d, "").length > 10, true, "Date + string");
Object.prototype.toString = function () { calls++; return "O"; };
check(add("", {}), "O", "own Object.prototype.toString");
check(calls, 2, "patched toString ran");
delete Object.prototype.toString;
