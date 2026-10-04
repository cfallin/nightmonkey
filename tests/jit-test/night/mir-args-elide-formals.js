// An arguments object read only for its length and elements is never made,
// now also in a function with formals, when no formal is ever written and
// none is closed over: a mapped object would then only read the actuals.
// The functions that write a formal, or close over one, keep the object,
// and see their writes through it (sloppy) or not (strict).

function variadic(type, config, children) {
  var n = arguments.length - 2, out = [type, config];
  for (var i = 0; i < n; i++) out.push(arguments[i + 2]);
  return out.join("|");
}
function strictVariadic(a, b) {
  "use strict";
  var s = arguments.length + ":";
  for (var i = 0; i < arguments.length; i++) s += arguments[i] + ",";
  return s;
}
function oob(a, b, c) { return [arguments.length, arguments[0], arguments[2], arguments[5], arguments[-1]].join(); }
function writesFormal(a, b) { a = "w"; return arguments[0] + arguments.length; }
function strictWritesFormal(a, b) { "use strict"; a = "w"; return arguments[0] + arguments.length; }
function closesOver(a, b) {
  function set() { a = "inner"; }
  set();
  return arguments[0] + arguments.length;
}

for (var r = 0; r < 500; r++) {
  if (r % 100 == 0) gc();
  assertEq(variadic("t", r), "t|" + r);
  assertEq(variadic("t", r, "c"), "t|" + r + "|c");
  assertEq(variadic("t", r, "c", "d", { toString() { return "e"; } }), "t|" + r + "|c|d|e");
  assertEq(variadic(), "|");
  assertEq(strictVariadic(), "0:");
  assertEq(strictVariadic(r), "1:" + r + ",");
  assertEq(strictVariadic(1, 2, 3), "3:1,2,3,");
  assertEq(oob(1), "1,1,,,");
  assertEq(oob(1, 2, 3, 4, 5, 6), "6,1,3,6,");
  assertEq(writesFormal("x"), "w1");
  assertEq(writesFormal("x", "y"), "w2");
  assertEq(strictWritesFormal("x"), "x1");
  assertEq(closesOver("x", 2), "inner2");
}
// An indexed property on Object.prototype shows through a missing element.
Object.prototype[5] = "proto5";
assertEq(oob(1, 2, 3), "3,1,3,proto5,");
delete Object.prototype[5];
assertEq(oob(1, 2, 3), "3,1,3,,");
