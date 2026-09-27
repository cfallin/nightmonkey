// MIR with an environment chain (`--pipeline mir`): a function whose own
// scope needs no environment but reads, writes and closes over its
// callee's (aliased variables of enclosing functions, `Lambda`), with the
// chain fixed for the whole activation.
function counter() {
  var n = 0;
  let step = 1;
  function bump(k) { for (var i = 0; i < k; i++) n += step; return n; }
  function get() { return n; }
  function setStep(s) { step = s; }
  return { bump, get, setStep };
}
var c = counter();
for (var i = 0; i < 50; i++) c.bump(10);
assertEq(c.get(), 500);
c.setStep(2);
assertEq(c.bump(5), 510);

// Two hops up, doubles and objects, and a GC while a closure is live.
function outer() {
  var total = 0.5;
  var box = { v: 1 };
  function mid() {
    function inner(k) {
      for (var i = 0; i < k; i++) { total += box.v; if (i % 50 == 0) gc(); }
      box = { v: box.v + 1 };
      return total;
    }
    return inner;
  }
  return mid();
}
var inner = outer();
assertEq(inner(100), 100.5);
assertEq(inner(100), 300.5);

// Closures created in a loop inside a MIR body, each over the same env.
function makeAdders(base) {
  var fs = [];
  for (var i = 0; i < 10; i++) fs.push(function (x) { return x + base; });
  return fs;
}
function sumAdders(n) {
  var t = 0;
  for (var j = 0; j < n; j++) { var fs = makeAdders(j); t += fs[3](1); }
  return t;
}
assertEq(sumAdders(40), 40 + 780);

// A TDZ read through the chain throws; after initialization it does not.
function tdz() {
  function read() { return x; }
  var r = [];
  for (var i = 0; i < 3; i++) {
    try { r.push(read()); } catch (e) { r.push(e instanceof ReferenceError); }
  }
  let x = 7;
  r.push(read());
  return r.join();
}
for (var i = 0; i < 10; i++) assertEq(tdz(), "true,true,true,7");

// An exit from a closure body (a type change) resumes baseline with the
// same environment.
function mk() {
  var acc = 0;
  return function (v) { for (var i = 0; i < 20; i++) acc = acc + v; return acc; };
}
var f = mk();
for (var i = 0; i < 30; i++) f(1);
assertEq(f("s").slice(0, 4), "600s");
