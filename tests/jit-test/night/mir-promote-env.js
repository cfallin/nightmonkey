// Loop-carried caching of closure variables (`promote`): a variable a
// loop reads and writes is carried in a register; memory is written back
// where something else may read it (a call, an exit, leaving the loop) and
// reloaded where something else may write it. Every case must match the
// spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + String(got) + ", want " + String(want));
}

// The variable lives in the closure's environment.
function counter() {
  var n = 0;
  function bump(k) { for (var i = 0; i < k; i++) n = n + i; return n; }
  function get() { return n; }
  function set(v) { n = v; }
  // A call inside the loop that reads it, one that writes it.
  function withReads(k) {
    var seen = 0;
    for (var i = 0; i < k; i++) { n = n + 1; seen += get(); }
    return seen;
  }
  function withWrites(k) {
    for (var i = 0; i < k; i++) { n = n + 1; if (i == 2) set(100); }
    return n;
  }
  // An exit in the middle of the loop (a type guard fails on the last
  // element): baseline must see the current value.
  function sumInto(a) {
    for (var i = 0; i < a.length; i++) n = n + a[i];
    return n;
  }
  return { bump, get, set, withReads, withWrites, sumInto };
}

for (var k = 0; k < 30; k++) {
  var c = counter();
  check(c.bump(10), 45, "bump");
  check(c.get(), 45, "written back after the loop");
  c.set(0);
  check(c.withReads(4), 1 + 2 + 3 + 4, "a call reads it in the loop");
  check(c.get(), 4, "after withReads");
  c.set(0);
  check(c.withWrites(5), 102, "a call writes it in the loop");
  c.set(0);
  check(c.sumInto([1, 2, 3]), 6, "sumInto ints");
}
var c = counter();
check(c.sumInto([1, 2, 3.5, "x"]), "6.5x", "an exit mid-loop");
check(c.get(), "6.5x", "the value baseline finished with");

// Two closures over one variable, a loop in each, and a nested one
// writing it.
function shared() {
  var t = 0;
  function inner() { t = t * 2; }
  function loop(k) {
    for (var i = 0; i < k; i++) { t = t + 1; if (i % 3 == 0) inner(); }
    return t;
  }
  return loop;
}
for (var k = 0; k < 30; k++) {
  var l = shared();
  // i=0: t=1, *2=2; i=1: 3; i=2: 4; i=3: 5, *2=10; i=4: 11
  check(l(5), 11, "shared with a nested writer");
}

// A throw out of the loop: the handler sees the current value.
function thrower() {
  var v = 0;
  function run(k) {
    try {
      for (var i = 0; i < k; i++) { v = v + 1; if (i == 3) throw new Error("x"); }
    } catch (e) {
      return v;
    }
    return -1;
  }
  return run;
}
for (var k = 0; k < 30; k++) check(thrower()(10), 4, "throw out of the loop");
