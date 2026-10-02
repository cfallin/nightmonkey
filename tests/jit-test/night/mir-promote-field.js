// Loop-carried caching of object fields (`promote`): a field a loop
// reads and writes through one object from before the loop is carried in
// a register, written back where something else may read it (a call, an
// alias of the object, an exit, leaving the loop) and reloaded where
// something else may write it. Every case must match the spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + String(got) + ", want " + String(want));
}

function Acc() { this.total = 0; this.n = 0; }

// The plain case: the field is only read and written through `a`.
function sum(a, k) {
  for (var i = 0; i < k; i++) a.total = a.total + i;
  return a.total;
}
// A call that reads the object in the loop.
function peek(a) { return a.total; }
function sumPeek(a, k) {
  var seen = 0;
  for (var i = 0; i < k; i++) { a.total = a.total + 1; seen += peek(a); }
  return seen;
}
// A call that writes it.
function reset(a) { a.total = 100; }
function sumReset(a, k) {
  for (var i = 0; i < k; i++) { a.total = a.total + 1; if (i == 2) reset(a); }
  return a.total;
}
// A write through another reference to the same object (or another
// object of the class) in the loop.
function sumAlias(a, b, k) {
  for (var i = 0; i < k; i++) { a.total = a.total + 1; b.total = b.total + 10; }
  return a.total;
}
// An exit in the middle (a type guard on the element fails).
function sumArr(a, arr) {
  for (var i = 0; i < arr.length; i++) a.total = a.total + arr[i];
  return a.total;
}

for (var k = 0; k < 40; k++) {
  var a = new Acc();
  check(sum(a, 10), 45, "sum");
  check(a.total, 45, "written back after the loop");
  a = new Acc();
  check(sumPeek(a, 4), 1 + 2 + 3 + 4, "a call reads it");
  a = new Acc();
  check(sumReset(a, 5), 102, "a call writes it");
  a = new Acc();
  check(sumAlias(a, a, 3), 33, "an alias of the object");
  var b = new Acc();
  a = new Acc();
  check(sumAlias(a, b, 3), 3, "another object of the class");
  check(b.total, 30, "the other object");
  a = new Acc();
  check(sumArr(a, [1, 2, 3]), 6, "sumArr ints");
}
var a = new Acc();
check(sumArr(a, [1, 2, 2.5, "x"]), "5.5x", "an exit mid-loop");
check(a.total, "5.5x", "the value baseline finished with");

// A getter installed on the object by a call in the loop: the reads
// after it must see it (the class's layout claim is gone, so the caching
// must not survive it).
function sumDefine(a, k) {
  for (var i = 0; i < k; i++) {
    a.total = a.total + 1;
    if (i == 1) Object.defineProperty(a, "total", { value: 50, writable: true });
  }
  return a.total;
}
for (var k = 0; k < 40; k++) check(sumDefine(new Acc(), 4), 52, "redefined in the loop");

// A throw out of the loop: the handler sees the current value.
function sumThrow(a, k) {
  try {
    for (var i = 0; i < k; i++) { a.total = a.total + 1; if (i == 3) throw 0; }
  } catch (e) {
    return a.total;
  }
  return -1;
}
for (var k = 0; k < 40; k++) check(sumThrow(new Acc(), 9), 4, "throw out of the loop");
