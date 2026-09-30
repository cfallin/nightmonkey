// Scalar replacement of literals in MIR (MIR-MEMORY.md §5): a literal
// whose only uses are its own field reads is never allocated, and an exit
// taken while it is live rebuilds it from the fields added so far, so
// baseline continues with a real object. The exits here are guards on
// arguments that are usually int32 and sometimes double.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + got + ", want " + want);
}

// No exit with the object live: nothing to rebuild.
function sum(a, b) {
  var o = {x: a, y: b};
  return o.x + o.y;
}

// An exit after the literal is complete (`k` a double): baseline reads
// both fields of the rebuilt object.
function after(a, b, k) {
  var o = {x: a, y: b};
  var t = o.x * (k + 1);
  return t + o.y;
}

// An exit between the inits (`k + 1` on a double): the object is rebuilt
// with `x` only, and baseline adds `y`.
function between(a, k) {
  var o = {x: a, y: k + 1};
  return o.x * 1000 + o.y;
}

// A field overwritten before the exit: the rebuilt object has the new
// value.
function overwrite(a, k) {
  var o = {x: a, y: 2};
  o.x = a + 5;
  var t = k + 1;
  return o.x + o.y + t;
}

for (var i = 0; i < 20000; i++) {
  var k = (i % 1000 == 999) ? 0.5 : i;
  check(sum(i, 3), i + 3, "sum");
  check(after(i, 7, k), i * (k + 1) + 7, "after(" + i + ", " + k + ")");
  check(between(i, k), i * 1000 + (k + 1), "between(" + i + ", " + k + ")");
  check(overwrite(i, k), i + 5 + 2 + k + 1, "overwrite(" + i + ", " + k + ")");
}
