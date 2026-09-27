// MIR's native Math arms: a call whose callee is the pristine native
// (matched by its JSNative) runs inline on number arguments; `new Array()`
// with the pristine constructor bump-allocates like `[]`. Non-numbers,
// replaced natives and a shadowed `Array` take the generic call.
function un(f, x) { return f(x); }
function bin(f, x, y) { return f(x, y); }
function mk() { return new Array(); }
// Values live across the allocation, rooted on its helper path.
function mk2(o, s) { var a = new Array(); a.push(o.k, s + "!"); var b = new Array(); b.push(a); return o.k + b[0][1]; }
function isNegZero(x) { return x === 0 && 1 / x === -Infinity; }
var xs = [0, -0, 1, -1, 2.5, -2.5, 0.49999999999999994, 1e300, -1e-300, NaN, Infinity, -Infinity, 2147483648, -2147483649, 4294967296 * 3 + 5];
for (var n = 0; n < 30; n++) {
  for (var i = 0; i < xs.length; i++) {
    var x = xs[i];
    assertEq(un(Math.sqrt, x), Math.sqrt(x));
    assertEq(un(Math.abs, x), Math.abs(x));
    assertEq(un(Math.floor, x), Math.floor(x));
    assertEq(un(Math.ceil, x), Math.ceil(x));
    assertEq(un(Math.trunc, x), Math.trunc(x));
    assertEq(un(Math.fround, x), Math.fround(x));
    assertEq(un(Math.sin, x), Math.sin(x));
    assertEq(un(Math.cos, x), Math.cos(x));
    assertEq(un(Math.clz32, x), Math.clz32(x));
    for (var j = 0; j < xs.length; j += 3) {
      var y = xs[j];
      assertEq(bin(Math.min, x, y), Math.min(x, y));
      assertEq(bin(Math.max, x, y), Math.max(x, y));
      assertEq(bin(Math.pow, x, y), Math.pow(x, y));
      assertEq(bin(Math.imul, x, y), Math.imul(x, y));
    }
  }
  assertEq(isNegZero(un(Math.floor, -0)), true);
  assertEq(isNegZero(un(Math.ceil, -0.5)), true);
  assertEq(isNegZero(bin(Math.min, 0, -0)), true);
  assertEq(isNegZero(bin(Math.max, -0, -0)), true);
  assertEq(un(Math.floor, "3.7"), 3);
  assertEq(bin(Math.max, "5", 2), 5);
  assertEq(un(Math.abs, { valueOf: function () { return -4; } }), 4);
  var a = mk();
  assertEq(Array.isArray(a), true);
  assertEq(a.length, 0);
  a.push(1);
  assertEq(mk().length, 0);
  assertEq(mk2({ k: "x" }, "y"), "xy!");
}
Math.sqrt = function (x) { return "patched"; };
assertEq(un(Math.sqrt, 4), "patched");
var Array = function () { this.shadowed = true; };
assertEq(mk().shadowed, true);
