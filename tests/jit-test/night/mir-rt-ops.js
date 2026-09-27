// MIR's generic operations through runtime helpers (`--pipeline mir`):
// instanceof, in, delete, object and array literals, typeof, throw.
function A() { this.a = 1; }
function B() { this.b = 2; }
B.prototype = Object.create(A.prototype);
function kind(x) { return (x instanceof B ? 2 : 0) + (x instanceof A ? 1 : 0); }
var objs = [new A(), new B(), {}, null, 3, "s"];
for (var n = 0; n < 20; n++) {
  assertEq(objs.map(kind).join(), "1,3,0,0,0,0");
}
var threw = false;
try { kind2(); } catch (e) { threw = e instanceof ReferenceError; }
function kind2() { return 1 instanceof 3; }
threw = false;
try { for (var i = 0; i < 5; i++) kind2(); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);

function has(o, k) { return k in o; }
for (var n = 0; n < 20; n++) {
  assertEq(has({ x: 1 }, "x"), true);
  assertEq(has({ x: 1 }, "y"), false);
  assertEq(has([1, 2], 1), true);
  assertEq(has(new B(), "a"), false);
}

function del(o) { delete o.x; return "x" in o; }
function delStrict(o) { "use strict"; delete o.x; return "x" in o; }
function delElem(a, i) { delete a[i]; return a.length + (i in a ? 10 : 0); }
for (var n = 0; n < 20; n++) {
  assertEq(del({ x: 1, y: 2 }), false);
  assertEq(delElem([1, 2, 3], 1), 3);
}
var frozen = Object.freeze({ x: 1 });
assertEq(del(frozen), true);
threw = false;
try { delStrict(frozen); } catch (e) { threw = e instanceof TypeError; }
assertEq(threw, true);

function lit(i) { return { a: i, b: [i, i + 1, "x"], c: { d: i * 2 } }; }
function sumLits(n) { var t = 0; for (var i = 0; i < n; i++) { var o = lit(i); t += o.a + o.b[1] + o.c.d; } return t; }
assertEq(sumLits(100), 4950 + 5050 + 9900);
function keyed(k, v) { return { [k]: v, z: 1 }; }
for (var n = 0; n < 20; n++) assertEq(JSON.stringify(keyed("q" + n, n)), '{"q' + n + '":' + n + ',"z":1}');

function ty(x) { return typeof x; }
var vals = [1, 1.5, "s", true, undefined, null, {}, [], function () {}, Symbol(), 1n];
var want = vals.map(v => typeof v).join();
for (var n = 0; n < 20; n++) assertEq(vals.map(ty).join(), want);

function thrower(x) { if (x > 5) throw new RangeError("r" + x); return x; }
function catcher(n) {
  var t = 0;
  for (var i = 0; i < n; i++) {
    try { t += thrower(i); } catch (e) { t += 100; }
  }
  return t;
}
assertEq(catcher(10), 15 + 400);
function throwsObj(o) { throw o; }
var got = null;
var tok = { t: 1 };
for (var n = 0; n < 10; n++) {
  try { throwsObj(tok); } catch (e) { got = e; }
}
assertEq(got, tok);
