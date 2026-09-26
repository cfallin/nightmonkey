// Onramps (`--pipeline mir`): after an exit, baseline runs the loop for a
// while, then calls back into the MIR body at the loop header's onramp
// root, whose guards re-check the frame. Run with `--mir-stress N` too,
// which forces exits all over these loops.

// Re-entry after a one-off exit: the overflow check fails once, when `s`
// passes 2^31, and `s` stays a double, so the onramp's guards re-deopt
// and baseline finishes the loop.
function crossesInt32(n) {
  var s = 2147483000;
  for (var i = 0; i < n; i++) s = s + 1;
  return s;
}
assertEq(crossesInt32(2000), 2147485000);

// A one-off exit whose cause goes away: `x` is a double for one iteration
// only, so the frame at the header is int32 again and the onramp holds.
function oneDouble(n) {
  var s = 0;
  for (var i = 0; i < n; i++) {
    var x = i;
    if (i == 10) x = 0.5;
    s = (s + (x | 0)) | 0;
  }
  return s;
}
assertEq(oneDouble(1000), 499500 - 10);

// Nested loops: an onramp into the inner loop side-enters the outer one
// (an irreducible MIR CFG that waffle's reducifier duplicates).
function grid(n, m) {
  var t = 0;
  for (var i = 0; i < n; i++) {
    for (var j = 0; j < m; j++) {
      t = (t + i * j) | 0;
      if (j == 7 && i == 3) t = t + 0.25;
      t = t | 0;
    }
  }
  return t;
}
assertEq(grid(20, 30), 82650);

// Three levels.
function cube(n) {
  var t = 0;
  for (var i = 0; i < n; i++)
    for (var j = 0; j < n; j++)
      for (var k = 0; k < n; k++)
        t = (t + ((i ^ j) & k)) | 0;
  return t;
}
assertEq(cube(12), 4368);

// Loop-carried values of every representation through an onramp: int32,
// double, boolean, and a boxed string.
function mixedState(n, str) {
  var a = 0, d = 0.5, b = false, s = str;
  for (var i = 0; i < n; i++) {
    a = a + 1;
    d = d * 1.5;
    b = !b;
    if (i == n - 1) s = s + a;
  }
  return s + a + d + b;
}
assertEq(mixedState(40, "x"), "x40" + 40 + 0.5 * Math.pow(1.5, 40) + false);
