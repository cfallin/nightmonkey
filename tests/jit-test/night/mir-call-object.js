// MIR for a script that makes its own environment (a call object for its
// closed-over bindings, a named lambda's scope): the entry makes it once
// and it is fixed for the activation; exits and loop onramps find it in
// the frame.
function counter(start) {
  var n = start;
  function inc(d) { n += d; return n; }
  return { inc: inc, get: function () { return n; } };
}
function sumLoop(k) {
  var acc = 0;
  var add = function (x) { acc += x; };
  for (var i = 0; i < k; i++) add(i);
  return acc;
}
var fact = function f(n) { return n <= 1 ? 1 : n * f(n - 1); };
function capFormal(a, b) {
  var g = function () { return a * 10 + b; };
  a = a + 1;
  return g();
}
for (var r = 0; r < 60; r++) {
  var c = counter(r);
  assertEq(c.inc(2), r + 2);
  assertEq(c.inc(3), r + 5);
  assertEq(c.get(), r + 5);
  assertEq(sumLoop(10), 45);
  assertEq(fact(5), 120);
  assertEq(capFormal(1, 2), 22);
  assertEq(capFormal(1), NaN);
}
// A long loop (onramp) and exits (a string and a double reach `acc`).
assertEq(sumLoop(20000), 199990000);
var c = counter("s");
assertEq(c.inc(1), "s1");
assertEq(counter(0.5).inc(1), 1.5);
assertEq(capFormal(1.5, "x"), "25x");
