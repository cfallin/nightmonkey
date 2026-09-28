// Narrowing from dynamic tests: a tag test that a branch consumes (a
// compare with null or undefined, `typeof x === "number"` and the other
// tag-exact types, `x?.y`) narrows the tested value on the branch it
// proves. Each function sees both outcomes, and values of several types.

function strictNull(x) {
  if (x === null) return -1;
  return typeof x === "number" ? x + 1 : String(x);
}
function looseUndef(x) {
  if (x != undefined) return x * 2;
  return 0;
}
function typeofNum(x) {
  if (typeof x === "number") return x * x;
  if (typeof x !== "string") return -2;
  return x.length;
}
function typeofBool(x) {
  if (typeof x == "boolean") return x ? 1 : 0;
  return 5;
}
function optional(o) {
  return o?.v ?? 7;
}
function undefConst(x) {
  // `x === undefined` compiles to a constant strict compare.
  if (x === undefined) return "u";
  return x;
}
function loop(a) {
  var s = 0;
  for (var i = 0; i < a.length; i++) {
    var x = a[i];
    if (x !== null && typeof x === "number") s += x;
  }
  return s;
}

var vals = [0, 3, 2.5, null, undefined, "abc", true, false, { v: 4 }];
for (var n = 0; n < 200; n++) {
  assertEq(strictNull(null), -1);
  assertEq(strictNull(n), n + 1);
  assertEq(strictNull("s"), "s");
  assertEq(strictNull(undefined), "undefined");
  assertEq(looseUndef(n), 2 * n);
  assertEq(looseUndef(null), 0);
  assertEq(looseUndef(undefined), 0);
  assertEq(typeofNum(n), n * n);
  assertEq(typeofNum(1.5), 2.25);
  assertEq(typeofNum("abcd"), 4);
  assertEq(typeofNum(null), -2);
  assertEq(typeofBool(true), 1);
  assertEq(typeofBool(false), 0);
  assertEq(typeofBool(0), 5);
  assertEq(optional({ v: n }), n);
  assertEq(optional(null), 7);
  assertEq(optional(undefined), 7);
  assertEq(optional({}), 7);
  assertEq(undefConst(undefined), "u");
  assertEq(undefConst(n), n);
  assertEq(undefConst(null), null);
  assertEq(loop(vals), 5.5);
}
