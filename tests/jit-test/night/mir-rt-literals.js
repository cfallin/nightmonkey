// MIR for getter/setter literals, regexp literals and formals read in a
// script that also uses `arguments` (unmapped: GetFrameArg).
function box(v) {
  return {
    get x() { return v; },
    set x(w) { v = w * 2; },
    y: 1,
  };
}
function words(s) {
  var re = /[a-z]+/g;
  var n = 0;
  while (re.exec(s)) n++;
  return n;
}
function strictArgs(a, b) {
  "use strict";
  a = a + 1;
  return a * 10 + b + arguments.length + arguments[0];
}
for (var i = 0; i < 60; i++) {
  var o = box(i);
  assertEq(o.x, i);
  o.x = 3;
  assertEq(o.x, 6);
  assertEq(o.y, 1);
  assertEq(words("ab cd, ef!"), 3);
  assertEq(strictArgs(1, 2), 20 + 2 + 2 + 1);
}
assertEq(strictArgs(1.5, "z"), "25z21.5");

// A literal with accessors in a callee small enough to inline: the
// spliced definitions keep their names.
function mk() { return { x: 0, get p() { return ++this.x; }, set p(v) { this.x = v + 2; } }; }
function useMk() {
  var o = mk();
  var r = 0;
  for (var i = 0; i < 100; i++) { r += o.p; o.p = i; }
  return r;
}
for (var i = 0; i < 5; i++) assertEq(useMk(), 5149);
