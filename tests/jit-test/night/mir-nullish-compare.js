// MIR compiles a compare against a null or undefined constant as tag
// tests (no user code runs, so no fence): strictly by tag; loosely null
// and undefined, and an object only if it emulates undefined.
function looseNull(x) { return x == null; }
function looseNotUndef(x) { return x != undefined; }
function strictNull(x) { return x === null; }
function strictNotUndef(x) { return x !== undefined; }
function nullOnLeft(x) { return null == x; }
var vals = [null, undefined, 0, "", false, {}, [], 1.5, "s", true, Symbol()];
function check(x) {
  var n = x === null || x === undefined;
  assertEq(looseNull(x), n);
  assertEq(looseNotUndef(x), !n);
  assertEq(strictNull(x), x === null);
  assertEq(strictNotUndef(x), x !== undefined);
  assertEq(nullOnLeft(x), n);
}
for (var i = 0; i < 60; i++) {
  for (var v of vals) check(v);
}
// An object that emulates undefined, once the functions are compiled.
if (typeof createIsHTMLDDA === "function") {
  var dda = createIsHTMLDDA();
  for (var i = 0; i < 10; i++) {
    assertEq(looseNull(dda), true);
    assertEq(looseNotUndef(dda), false);
    assertEq(nullOnLeft(dda), true);
    assertEq(strictNull(dda), false);
    assertEq(strictNotUndef(dda), true);
  }
}
