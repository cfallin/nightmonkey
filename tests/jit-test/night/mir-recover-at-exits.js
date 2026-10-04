// A sum or product only ToInt32 sees is unchecked (`trunc_demand`) even
// where an exit holds it: the exit recomputes its exact value from the
// operands (`recover_at_exits`). Baseline then continues with the exact
// value. That shows where a guard fails and baseline does something other
// than the int arithmetic MIR assumed: here a field the analysis predicts
// int32 (only int writes are visible to it; the string arrives through a
// computed-name call, whose arguments it cannot bind) holds a string, and
// `m + s` puts m's digits in a number.

function Box() { this.v = 1; }
var box = new Box();
var setter = { setv: function (x) { box.v = x; } };
function setByName(x) { setter[["set", "v"].join("")](x); }

function mixed(a, b) {
  var x = (a & 0x7fff) * (b & 0x7fff);   // an int32 product
  var m = x + x + x;                     // past int32
  var t = m & 0xff;
  var s = box.v;              // predicted int32
  return ((m + s) | 0) + t;
}
function chain(a, b, c) {
  var x = (a & 0x7fff) * (b | 0x4000);
  var y = x + (c | 0);
  var z = y + x;              // a chain of wrapped sums
  var s = box.v;
  return ((z + s) >> 1) ^ (z & 7);
}

var big = [0x7fffffff, 65537, -0x80000000, 123456789, -987654321, 3, 0];
function check() {
  for (var a of big) {
    for (var b of big) {
      var p = (a & 0x7fff) * (b & 0x7fff), m = p + p + p, s = box.v;
      assertEq(mixed(a, b), ((m + s) | 0) + (m & 0xff));
      var c = big[(a & 3)];
      var x = (a & 0x7fff) * (b | 0x4000), y = x + (c | 0), z = y + x;
      assertEq(chain(a, b, c), ((z + s) >> 1) ^ (z & 7));
    }
  }
}
for (var r = 0; r < 200; r++) {
  box.v = r & 7;
  check();
}
// The field's guard fails: baseline concatenates the exact values.
for (var s of ["e-1", "0", ".5e1", "e2", "", "e-2"]) {
  setByName(s);
  check();
}
box.v = 5;
check();
