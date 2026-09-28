// Assorted ops in MIR: `??`, tagged templates (the call-site object is the
// same object at every evaluation), computed-key accessors, `super` from an
// arrow (the method's home through its environment), a sure TDZ read
// (baseline throws), `debugger` with no debugger attached, and
// class-constructor features (fields, private names, statics, `#x in o`,
// calling a class throws), and derived classes: `super(...)`, spread
// `super`, `super.m()`/`super.x` reads and writes, static `super`, a
// default derived constructor, `this` before `super()` and a second
// `super()` throwing, a derived constructor returning an object, and one
// returning a primitive throwing.

function coalesce(a, b) { return (a ?? b) + (a?.length ?? -1); }
function tag(strs, ...vals) { return strs; }
function sameSite() { return tag`a${1}b`; }
function accessors(k, v) {
  var o = { get [k]() { return v; }, set [k + "s"](x) { this.last = x; } };
  o[k + "s"] = v * 2;
  return o[k] + o.last;
}
var A = { m() { return 3; } };
var B = { __proto__: A, m() { var f = () => super.m(); return f() + 1; } };
function tdz(r) {
  try {
    x = r;
    let x;
    return 0;
  } catch (e) {
    return e instanceof ReferenceError ? 1 : 2;
  }
}
function dbg(r) { debugger; return r + 1; }
class P {
  static count = 0;
  #secret;
  pub = 1;
  constructor(s) { this.#secret = s; P.count++; }
  reveal() { return this.#secret + this.pub; }
  static has(o) { return #secret in o; }
}
function classes(r) {
  var p = new P(r);
  var threw = false;
  try { P(r); } catch (e) { threw = e instanceof TypeError; }
  return p.reveal() + (P.has(p) ? 10 : 0) + (P.has({}) ? 100 : 0) + (threw ? 1000 : 0);
}

class Q { constructor(x) { this.x = x; } m() { return this.x; } static s() { return 1; } }
class D extends Q {
  constructor(x, y) { super(x); this.y = y; }
  m() { return super.m() + this.y; }
  get g() { return super.x; }
  set g(v) { super.x = v; }
  static s() { return super.s() + 1; }
}
class E extends Q { constructor(...a) { super(...a); } }
class F extends Q {}
class Early extends Q { constructor(k) { if (k == 0) this.z = 1; super(k); if (k == 1) super(k); } }
class Other extends Q { constructor(k) { super(k); return k == 2 ? 5 : { other: k }; } }
function derived(i) {
  var d = new D(i, 2);
  var t = d.m() + D.s();
  d.g = 5;
  t += d.x + new E(i).x + new F(1).x;
  var errs = 0;
  for (var k = 0; k < 3; k++) {
    try { new Early(k); } catch (e) { if (e instanceof ReferenceError) errs++; }
  }
  try { new Other(2); } catch (e) { if (e instanceof TypeError) errs += 10; }
  return t + errs * 1000 + new Other(i + 3).other;
}

var first = sameSite();
for (var r = 0; r < 400; r++) {
  assertEq(coalesce(null, 5), 4);
  assertEq(coalesce(undefined, 5), 4);
  assertEq(coalesce("ab", 5), "ab2");
  assertEq(coalesce(0, 5), -1);
  assertEq(sameSite() === first, true);
  var s = sameSite();
  assertEq(s.raw[0], "a");
  assertEq(accessors("k", r), 3 * r);
  assertEq(B.m(), 4);
  assertEq(tdz(r), 1);
  assertEq(dbg(r), r + 1);
  assertEq(classes(r), r + 1 + 10 + 1000);
  assertEq(derived(r), (r + 2 + 2) + 5 + r + 1 + 12000 + r + 3);
}
assertEq(P.count, 400);
