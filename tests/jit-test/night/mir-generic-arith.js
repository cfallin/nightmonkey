// MIR's inline arms for generic arithmetic (`--pipeline mir`): operands of
// types the analysis cannot know (here, through an array of mixed values)
// try int32, then doubles, then the runtime, and every edge case must
// match the interpreter.
var vals = [0, -0, 1, -1, 2, 7, -7, 0.5, -2.5, 2147483647, -2147483648,
            4294967295, NaN, Infinity, -Infinity, "3", "x", true, null,
            undefined, 1e300];
function add(a, b) { return a + b; }
function sub(a, b) { return a - b; }
function mul(a, b) { return a * b; }
function div(a, b) { return a / b; }
function mod(a, b) { return a % b; }
function band(a, b) { return a & b; }
function bor(a, b) { return a | b; }
function bxor(a, b) { return a ^ b; }
function lsh(a, b) { return a << b; }
function rsh(a, b) { return a >> b; }
function ursh(a, b) { return a >>> b; }
function lt(a, b) { return a < b; }
function le(a, b) { return a <= b; }
function gt(a, b) { return a > b; }
function ge(a, b) { return a >= b; }
function inc(a) { return ++a; }
function dec(a) { return --a; }
function neg(a) { return -a; }
function bnot(a) { return ~a; }
function pos(a) { return +a; }
var bins = [add, sub, mul, div, mod, band, bor, bxor, lsh, rsh, ursh, lt, le, gt, ge];
var uns = [inc, dec, neg, bnot, pos];
function same(x, y) { return Object.is(x, y); }
// The interpreter's answers first (these calls are cold), then hot.
var want = [];
for (var f of bins) for (var a of vals) for (var b of vals) want.push(f(a, b));
for (var f of uns) for (var a of vals) want.push(f(a));
for (var n = 0; n < 20; n++) {
  var k = 0;
  for (var f of bins) for (var a of vals) for (var b of vals) {
    var r = f(a, b);
    if (!same(r, want[k])) throw new Error(f.name + "(" + String(a) + ", " + String(b) + ") = " + r + ", want " + want[k]);
    k++;
  }
  for (var f of uns) for (var a of vals) {
    var r = f(a);
    if (!same(r, want[k])) throw new Error(f.name + "(" + String(a) + ") = " + r + ", want " + want[k]);
    k++;
  }
}
