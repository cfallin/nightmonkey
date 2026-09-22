// A throw from inside a block with its own environment must leave the
// handler at the Try's environment: aliased reads there see the outer scope.
function f() {
  let t = "outer";
  function g() { return t; }
  try {
    { let u = "inner"; function h() { return u; } throw 1; }
  } catch (e) {
    return t;
  }
}
assertEq(f(), "outer");

function f2() {
  let t = "outer";
  function g() { return t; }
  var seen;
  try {
    { let u = "inner"; function h() { return u; } throw 1; }
  } finally {
    seen = t;
  }
}
try { f2(); } catch (e) {}

function f3() {
  var t = "outer";
  function g() { return t; }
  try {
    { let u = "inner"; function h() { return u; }
      { let w = "inner2"; function h2() { return w; } throw 1; } }
  } catch (e) {
    t = t + "+caught";
    return g();
  }
}
assertEq(f3(), "outer+caught");

// The async form: the generator object is an aliased variable, and the
// rejection path read it after unwinding.
var rejected = null;
(async function () {
  const t = { then(res, rej) { rej("R"); } };
  function* gen() { yield t; }
  await Array.fromAsync(gen());
})().then(() => { rejected = "resolved"; }, e => { rejected = e; });
drainJobQueue();
assertEq(rejected, "R");
