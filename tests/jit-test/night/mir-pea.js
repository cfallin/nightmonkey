// Partial escape of literal objects (`pea`): a literal stays virtual until
// it escapes, and on each path the first escape makes the one real object
// every later use, escape and exit sees (identity is observable). Every
// case must match the spec.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + String(got) + ", want " + String(want));
}

var kept = [];
function keep(o) { kept.push(o); return o; }
function bump(o) { o.a = o.a + 100; }

// Escapes on one path only; the other never allocates it.
function one(c, x) {
  var o = { a: x, b: 1 };
  var s = o.a + o.b;
  if (c) {
    keep(o);
    return o.a + s;
  }
  return s;
}
// Two escapes: the same object both times.
function twice(x) {
  var o = { a: x, b: 2 };
  var s = o.b;
  var p = keep(o);
  var q = keep(o);
  return (p === q && q === o) ? s + o.a : -1;
}
// A write through the escaped reference is seen afterwards.
function seen(x) {
  var o = { a: x, b: 3 };
  var s = o.a;
  bump(o);
  return o.a - s;
}
// An exit while virtual (a type guard on the argument fails after the
// literal is made): baseline gets the object with its fields.
function exitVirtual(x, y) {
  var o = { a: x, b: 4 };
  var t = y + 1;
  if (t > 1000) keep(o);
  return o.a + o.b + t;
}

for (var k = 0; k < 60; k++) {
  check(one(false, k), k + 1, "one, no escape");
  check(one(true, k), 2 * k + 1, "one, escape");
  check(twice(k), k + 2, "twice");
  check(seen(k), 100, "write through the escaped reference");
  check(exitVirtual(k, 5), k + 10, "exitVirtual");
}
// The call it escapes into changes its layout (a new property, a
// redefined one): the reads after it must not use the literal's layout.
function grow(o) { o.c = 7; }
function regrow(o) { Object.defineProperty(o, "a", { get: function () { return 42; } }); }
function reshaped(x, g) {
  var o = { a: x, b: 5 };
  var s = o.a;
  g(o);
  return s + o.a + o.b + (o.c === undefined ? 0 : o.c);
}
for (var k = 0; k < 60; k++) {
  check(reshaped(k, grow), 2 * k + 12, "a property added by the call");
  check(reshaped(k, regrow), k + 47, "a getter installed by the call");
}

check(exitVirtual(1, 2.5), 8.5, "exitVirtual after an exit");
check(exitVirtual(1, "s"), "5s1", "exitVirtual, string");
check(kept.length > 0 && kept.every(o => typeof o.a === "number"), true, "kept objects");
var last = kept[kept.length - 1];
check(last.b, 2, "last kept is twice's");
