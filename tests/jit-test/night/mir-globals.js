// Syntactic globals in MIR as `load_gname`/`store_gname` behind
// `check.binding` (§3): reads and writes of `var` globals in loops, a
// global changed by a callee between reads, non-writable globals (a store
// fails silently in sloppy code, throws in strict), a global redefined as
// an accessor, a global deleted and re-added, and fused literals written
// to other values.

var counter = 0;
var scale = 3;
this.label = "x";
var fused = 7;
function bump() { counter++; }
function sumLoop(n) { var t = 0; for (var i = 0; i < n; i++) { t += scale; counter += 1; } return t; }
function readAround() { var a = counter; bump(); return counter - a; }
function writeNaN() { NaN = 5; return NaN; }
function writeStrict() { "use strict"; try { undefined = 1; return "no"; } catch (e) { return e instanceof TypeError ? "te" : "other"; } }
function readLabel() { return label + fused; }
this.gone = 1;
function readGone() { return typeof gone == "undefined" ? "u" : gone; }

for (var r = 0; r < 300; r++) {
  counter = 0;
  assertEq(sumLoop(10), 10 * scale);
  assertEq(counter, 10);
  assertEq(readAround(), 1);
  assertEq(writeNaN() !== writeNaN(), true);
  assertEq(writeStrict(), "te");
  if (r == 100) scale = 4;
  if (r == 150) fused = "f";
  var lab = r > 220 ? "y" : r > 200 ? "g" : "x";
  assertEq(readLabel(), lab + (r >= 150 ? "f" : "7"));
  if (r == 200) {
    Object.defineProperty(this, "label", { get() { return "g"; }, configurable: true });
  }
  if (r == 220) {
    delete this.label;
    this.label = "y";
  }
  if (r == 250) delete this.gone;
  if (r == 260) this.gone = 2;
  assertEq(readGone(), r >= 250 && r < 260 ? "u" : r >= 260 ? 2 : 1);
}
assertEq(scale, 4);
