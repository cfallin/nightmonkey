// MIR for a sloppy script with no formals that reads `arguments` (a mapped
// arguments object with nothing to map): scheme runtimes' variadic list
// builders. `arguments.callee` and element writes see one object.
function Pair(car, cdr) { this.car = car; this.cdr = cdr; }
function list() {
  var res = null;
  var a = arguments;
  for (var i = a.length - 1; i >= 0; i--) res = new Pair(a[i], res);
  return res;
}
function len(l) { var n = 0; while (l !== null) { n++; l = l.cdr; } return n; }
function self() { return arguments.callee; }
function bump() {
  arguments[0] = arguments[0] + 1;
  arguments[arguments.length] = 5;
  return arguments[0] * 10 + arguments.length;
}
for (var n = 0; n < 40; n++) {
  assertEq(list(), null);
  assertEq(len(list(1, 2, 3)), 3);
  assertEq(list(1, 2, 3).cdr.car, 2);
  assertEq(self(), self);
  assertEq(bump(1, 2), 22);
}
// An exit mid-loop (a double and a string reach `a[i]`).
assertEq(list(1.5, "s", 3).cdr.car, "s");
assertEq(list(1.5).car, 1.5);

// With a call object too (a closure over a local): the arguments object
// records the activation's call object, not the callee's environment,
// and survives a GC.
function withEnv() {
  var a = arguments;
  var k = 3;
  var f = function () { return a.length * k; };
  if (a.length > 2) gc();
  return f() + (a[0] | 0);
}
for (var n = 0; n < 60; n++) {
  assertEq(withEnv(), 0);
  assertEq(withEnv(1, 2), 7);
}
assertEq(withEnv(1, 2, 3), 10);
