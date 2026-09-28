// Rarer ops in MIR: compound assignment to a name found through `with`
// (BindName/GetBoundName), an object literal with `__proto__` from a
// value (ObjWithProto), private names made per class evaluation
// (NewPrivateName), a direct eval with spread arguments (SpreadEval), and
// `using` declarations with their disposal (AddDisposable,
// TakeDisposeCapability, CreateSuppressedError) where the shell has them.

function withCompound(o, r) {
  with (o) {
    x += r;
    x *= 2;
  }
  return o.x;
}
function protoLit(p) {
  var o = { __proto__: p, own: 1 };
  return o.inherited + o.own;
}
function privateClass(v) {
  class C {
    #p = v;
    static get(o) { return o.#p; }
  }
  return C.get(new C());
}
function spreadEval(args) {
  var local = 10;
  return eval(...args);
}

var hasUsing = true;
try { Function("{ using x = null; }"); } catch (e) { hasUsing = false; }
var usingTest = hasUsing ? Function("log", `
  var r = 0;
  {
    using a = { [Symbol.dispose]() { log.push("a"); } };
    using b = { [Symbol.dispose]() { log.push("b"); } };
    r = 1;
  }
  try {
    using c = { [Symbol.dispose]() { throw new Error("dispose"); } };
    throw new Error("body");
  } catch (e) {
    r += (e instanceof SuppressedError) ? 10 : 100;
  }
  return r;
`) : null;

for (var r = 0; r < 400; r++) {
  assertEq(withCompound({ x: 1 }, r), (1 + r) * 2);
  assertEq(protoLit({ inherited: r }), r + 1);
  assertEq(privateClass(r), r);
  assertEq(spreadEval(["local + " + r]), 10 + r);
  if (usingTest) {
    var log = [];
    assertEq(usingTest(log), 11);
    assertEq(log.join(), "b,a");
  }
}
