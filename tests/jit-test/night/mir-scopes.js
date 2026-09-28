// Scopes that push environments in MIR: block scopes whose bindings a
// closure captures, per-iteration `let` bindings (freshened each
// iteration), a class body's scope, `with`, and names looked up through
// the dynamic chain (GetName/BindName/SetName/DelName under `with` and
// in sloppy functions a direct eval can extend). A throw from inside a
// scope exits, and baseline's unwind pops the environments.

function blockClosure(n) {
  var fs = [];
  for (let i = 0; i < n; i++) {
    let j = i * 2;
    fs.push(() => i + j);
  }
  var t = 0;
  for (var f of fs) t += f();
  return t;
}
function nested(x) {
  var r;
  {
    let a = x + 1;
    {
      let b = a * 2;
      r = () => a + b;
    }
  }
  return r();
}
function throwingScope(x) {
  try {
    let k = x;
    var g = () => k;
    if (x % 3 == 0) throw g;
    return g();
  } catch (e) {
    return -e();
  }
}
function classScope(v) {
  class C { m() { return C.tag + v; } }
  C.tag = 100;
  return new C().m();
}
function withRead(o) {
  var y = 7;
  with (o) {
    return x + y;
  }
}
function withWrite(o, v) {
  with (o) {
    x = v;
    z = v + 1;
  }
  return o.x;
}
var z = 0;
function evalScope(s) {
  eval(s);
  return typeof q == "undefined" ? -1 : q;
}
function evalLocal(r) {
  var a = 1;
  let b = 2;
  eval("a = a + r; b = b * r");
  return a * 1000 + b;
}
function strictEval(r) {
  "use strict";
  var a = r;
  eval("var a = 99; a = 5");
  return a + eval("a + 1");
}
function notEval(r) {
  var eval = function (s) { return s + "!"; };
  return eval("x" + r);
}
var gv = 5;
function delGlobal() {
  return delete notDeclared;
}

for (var r = 0; r < 400; r++) {
  assertEq(blockClosure(4), 0 + 3 + 6 + 9);
  assertEq(nested(r), (r + 1) * 3);
  assertEq(throwingScope(r), r % 3 == 0 ? -r : r);
  assertEq(classScope(r), 100 + r);
  assertEq(withRead({ x: r }), r + 7);
  assertEq(withRead({ y: 1, x: r }), r + 1);
  var o = { x: 0 };
  assertEq(withWrite(o, r), r);
  assertEq(z, r + 1);
  assertEq(evalScope(r % 2 ? "var q = " + r : ""), r % 2 ? r : -1);
  assertEq(delGlobal(), true);
  assertEq(evalLocal(r), (1 + r) * 1000 + 2 * r);
  assertEq(strictEval(r), 2 * r + 1);
  assertEq(notEval(r), "x" + r + "!");
}
