// MIR's generic ops in sloppy code (`--pipeline mir`): `this` boxing,
// string constants, global assignment, and switch statements.

function thisObj() { return this; }
var o = { m: thisObj };
assertEq(o.m(), o);
assertEq(thisObj(), this);
assertEq(typeof thisObj.call(5), "object");
assertEq(thisObj.call(5).valueOf(), 5);
assertEq(thisObj.call(null), this);

function str(n) { var s = "a"; for (var i = 0; i < n; i++) s = s + "b"; return s + "!"; }
assertEq(str(3), "abbb!");
function gcStr(n) { var s = "x"; for (var i = 0; i < n; i++) { if (i % 50 == 0) gc(); s = "y" + s; } return s.length; }
assertEq(gcStr(200), 201);

var counter = 0;
function bump(n) { for (var i = 0; i < n; i++) counter = counter + 1; return counter; }
assertEq(bump(10), 10);
assertEq(bump(5), 15);
function makeGlobal() { freshGlobal = 7; return freshGlobal; }
assertEq(makeGlobal(), 7);
assertEq(freshGlobal, 7);
function strictUndeclared() { "use strict"; undeclaredStrict = 1; }
var threw = false;
try { strictUndeclared(); } catch (e) { threw = e instanceof ReferenceError; }
assertEq(threw, true);

function sw(x) {
  switch (x) {
    case 0: return 10;
    case 1: return 11;
    case 2: return 12;
    case 5: return 15;
    default: return -1;
  }
}
assertEq(sw(0), 10);
assertEq(sw(2), 12);
assertEq(sw(5), 15);
assertEq(sw(3), -1);
assertEq(sw(-1), -1);
assertEq(sw(2.0), 12);
assertEq(sw(2.5), -1);
assertEq(sw(-0), 10);
assertEq(sw("2"), -1);
assertEq(sw(null), -1);
assertEq(sw(true), -1);

function swStr(x) {
  switch (x) {
    case "a": return 1;
    case "b": return 2;
    default: return 0;
  }
}
assertEq(swStr("a"), 1);
assertEq(swStr("b"), 2);
assertEq(swStr("c"), 0);
assertEq(swStr(1), 0);

function swLoop(n) {
  var t = 0;
  for (var i = 0; i < n; i++) {
    switch (i % 4) {
      case 0: t += 1; break;
      case 1: t += 10; break;
      case 3: t += 100; break;
    }
  }
  return t;
}
assertEq(swLoop(20), 5 * 111);
