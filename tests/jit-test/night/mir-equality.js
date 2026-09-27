// MIR's inline equality and truthiness arms (`--pipeline mir`): operands
// whose bits decide the answer compare inline; everything else (numbers
// of mixed representation, strings, coercions, objects emulating
// `undefined`) goes through the runtime.
function eq(a, b) { return a == b; }
function ne(a, b) { return a != b; }
function seq(a, b) { return a === b; }
function sne(a, b) { return a !== b; }
function truthy(a) { return a ? 1 : 0; }

var o = {}, p = {}, s = Symbol("s");
var cases = [
  [null, undefined], [undefined, null], [null, null], [o, o], [o, p],
  [o, null], [null, o], [undefined, o], [1, 1], [1, 2], [true, true],
  [true, false], [1, true], [0, false], ["a", "a"], ["a", "b"],
  [1.5, 1.5], [1, 1.0], [NaN, NaN], [0, -0], [s, s], [s, Symbol("s")],
  ["1", 1], [null, 0], [undefined, 0], [0, ""], [o, "[object Object]"],
  [10n, 10n], [10n, 10],
];
// The interpreter's answers, then the same calls hot.
var want = cases.map(([a, b]) => [a == b, a != b, a === b, a !== b]);
for (var n = 0; n < 30; n++) {
  for (var i = 0; i < cases.length; i++) {
    var [a, b] = cases[i];
    assertEq(eq(a, b), want[i][0]);
    assertEq(ne(a, b), want[i][1]);
    assertEq(seq(a, b), want[i][2]);
    assertEq(sne(a, b), want[i][3]);
  }
}
var vals = [0, 1, -1, 0.5, -0, NaN, "", "x", null, undefined, true, false, o, s, 0n, 1n];
for (var n = 0; n < 30; n++) {
  for (var v of vals) assertEq(truthy(v), v ? 1 : 0);
}

// An object that emulates undefined, created after the arms are hot.
if (typeof createIsHTMLDDA === "function") {
  var dda = createIsHTMLDDA();
  for (var n = 0; n < 5; n++) {
    assertEq(eq(dda, null), true);
    assertEq(eq(dda, undefined), true);
    assertEq(eq(null, dda), true);
    assertEq(eq(dda, dda), true);
    assertEq(eq(dda, o), false);
    assertEq(seq(dda, undefined), false);
    assertEq(truthy(dda), 0);
    assertEq(truthy(o), 1);
    assertEq(eq(o, null), false);
  }
}
