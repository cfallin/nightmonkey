// MIR for scripts that read their actuals (`--pipeline mir`): the frame's
// variable region starts past the actuals beyond the formals (`vp`), and
// `arguments`, rest parameters and the actual count read them. Exits and
// onramps must agree with baseline on that layout.
"use strict";
function sum() {
  var t = 0;
  for (var i = 0; i < arguments.length; i++) t += arguments[i];
  return t;
}
for (var n = 0; n < 30; n++) {
  assertEq(sum(), 0);
  assertEq(sum(1), 1);
  assertEq(sum(1, 2, 3, 4, 5), 15);
}
// An exit mid-loop in a frame with extra actuals (a string joins).
assertEq(sum(1, 2, "x", 4), "3x4");

function firstAndRest(a, ...rest) { return a + rest.length * 100 + (rest[0] | 0); }
for (var n = 0; n < 30; n++) {
  assertEq(firstAndRest(1), 1);
  assertEq(firstAndRest(1, 7, 8, 9), 1 + 300 + 7);
}

function count(a, b) { return arguments.length * 10 + (a | 0) + (b | 0); }
for (var n = 0; n < 30; n++) {
  assertEq(count(), 0);
  assertEq(count(1, 2, 3, 4), 43);
}

// The prototype.js pattern: a constructor forwarding its actuals.
function Klass() { this.initialize.apply(this, arguments); }
Klass.prototype.initialize = function (x, y, z) { this.x = x; this.y = y; this.z = z; };
function build(n) {
  var t = 0;
  for (var i = 0; i < n; i++) { var k = new Klass(i, i * 2, i * 3); t += k.x + k.y + k.z; }
  return t;
}
assertEq(build(100), 6 * 4950);

// The arguments object is one object per activation, before and after an
// exit, and survives a GC.
function same() {
  var a = arguments;
  gc();
  var r = a === arguments;
  var s = "" + arguments[0];
  return r && s == "q" && arguments.length == 3;
}
for (var n = 0; n < 30; n++) assertEq(same("q", 2, 3), true);

// A loop long enough to onramp, in a frame with extra actuals.
function longLoop(n) {
  var t = 0;
  for (var i = 0; i < n; i++) t += arguments.length;
  return t;
}
assertEq(longLoop(20000, 1, 2), 60000);
