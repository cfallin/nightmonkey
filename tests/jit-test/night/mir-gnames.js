// MIR's inline global reads (`--pipeline mir`): a syntactic global
// binding reads its value-fuse cell, else its cached slot while the
// global's shape is unchanged, else re-resolves; lexicals, deleted and
// redefined globals go through the runtime.
var counter = 0;
function Thing(v) { this.v = v; }
var table = { a: 1 };
function readMany(n) {
  var t = 0;
  for (var i = 0; i < n; i++) { counter++; t += table.a + new Thing(i).v; }
  return t;
}
assertEq(readMany(100), 100 + 4950);
assertEq(counter, 100);
// The binding changes value, then the global object changes shape.
table = { a: 2 };
assertEq(readMany(10), 20 + 45);
globalThis.newGlobal1 = 1;
globalThis.newGlobal2 = 2;
assertEq(readMany(10), 20 + 45);
// Redefined as an accessor, then deleted (configurable implicit global).
function readImplicit() { return implicitG; }
globalThis.implicitG = 5;
for (var i = 0; i < 30; i++) assertEq(readImplicit(), 5);
var gets = 0;
Object.defineProperty(globalThis, "implicitG", { get() { gets++; return 6; }, configurable: true });
assertEq(readImplicit(), 6);
assertEq(gets, 1);
delete globalThis.implicitG;
var threw = false;
try { readImplicit(); } catch (e) { threw = e instanceof ReferenceError; }
assertEq(threw, true);
// A global lexical shadows a var-less global property.
globalThis.shadowMe = 1;
function readShadow() { return shadowMe; }
for (var i = 0; i < 30; i++) assertEq(readShadow(), 1);
evaluate("let shadowMe = 2;");
assertEq(readShadow(), 2);
