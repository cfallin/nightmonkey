// A read of a method the analysis predicts (one function, held by the
// receivers' prototype chain) takes it from a cell the runtime arms only
// while the chain resolves the name to that function through a constant
// (ObjectFuse) property, for receivers that are CLOSED (no own property
// outside their layout's row) and have the prototype the cell was armed
// for. Every way of changing what the name resolves to must be seen: the
// holder's property rewritten, deleted or made an accessor; the name added
// to the receiver, or to a prototype below the holder; the receiver's or a
// prototype's prototype changed. The changes go through computed keys and
// reflection, which the analysis does not follow, so the reads stay
// predicted. Each case has a class of its own: a property once rewritten
// is never constant again, so its cell never re-arms.

function key(s) { return s.split("").join(""); }
// A minor GC first: a cell arms only with a tenured prototype and function
// (until a GC, one that could not stays unarmed).
function check(n, f) {
  minorgc();
  for (var i = 0; i < n; i++) f(i);
}

// Each case's classes are written out: a class made by a factory is a
// closure of the factory's scripts, and the scripts are what a method cell
// is for (one cell per layout, name and script, armed for one prototype).

var Other = { m() { return "other"; } };

// Warm, with GCs.
function A(x, y) { this.x = x; this.y = y; }
A.prototype.m = function () { return this.x * this.x + this.y; };
function callA(p) { return p.m(); }
check(400, function (i) {
  if (i % 100 == 0) gc();
  if (i % 30 == 0) minorgc();
  assertEq(callA(new A(i, 1)), i * i + 1);
});

// The holder's property rewritten.
function B(x, y) { this.x = x; this.y = y; }
B.prototype.m = function () { return this.x * this.x + this.y; };
function callB(p) { return p.m(); }
check(200, function (i) { assertEq(callB(new B(i, 1)), i * i + 1); });
B.prototype[key("m")] = function () { return -this.x; };
check(200, function (i) { assertEq(callB(new B(i, 1)), -i); });

// The name added to some receivers (no longer CLOSED), an unrelated
// property to others (no longer CLOSED either; they still read the
// prototype's).
function C(x, y) { this.x = x; this.y = y; }
C.prototype.m = function () { return this.x * this.x + this.y; };
function callC(p) { return p.m(); }
check(200, function (i) { assertEq(callC(new C(i, 1)), i * i + 1); });
check(300, function (i) {
  var p = new C(i, 1);
  if (i % 3 == 0) p[key("m")] = function () { return "own"; };
  if (i % 3 == 1) p[key("extra")] = 1;
  assertEq(callC(p), i % 3 == 0 ? "own" : i * i + 1);
});

// An accessor in place of the method.
function D(x, y) { this.x = x; this.y = y; }
D.prototype.m = function () { return this.x * this.x + this.y; };
function callD(p) { return p.m(); }
check(200, function (i) { assertEq(callD(new D(i, 1)), i * i + 1); });
Object.defineProperty(D.prototype, key("m"), {
  get() { return function () { return "got"; }; },
  configurable: true,
});
check(100, function (i) { assertEq(callD(new D(i, 1)), "got"); });

// Deleted: the call throws.
function E(x, y) { this.x = x; this.y = y; }
E.prototype.m = function () { return this.x * this.x + this.y; };
function callE(p) { return p.m(); }
check(200, function (i) { assertEq(callE(new E(i, 1)), i * i + 1); });
delete E.prototype[key("m")];
check(50, function (i) {
  var threw = false;
  try { callE(new E(i, 1)); } catch (e) { threw = e instanceof TypeError; }
  assertEq(threw, true);
});

// The name added to a prototype below the holder.
function FBase() {}
FBase.prototype.m = function () { return "base:" + this.x; };
function FMid() {}
FMid.prototype = Object.create(FBase.prototype);
function FLeaf(x) { this.x = x; }
FLeaf.prototype = Object.create(FMid.prototype);
var F = { Base: FBase, Mid: FMid, Leaf: FLeaf };
function callF(o) { return o.m(); }
check(200, function (i) { assertEq(callF(new F.Leaf(i)), "base:" + i); });
F.Mid.prototype[key("m")] = function () { return "mid"; };
check(100, function (i) { assertEq(callF(new F.Leaf(i)), "mid"); });

// A prototype on the chain given another prototype.
function GBase() {}
GBase.prototype.m = function () { return "base:" + this.x; };
function GMid() {}
GMid.prototype = Object.create(GBase.prototype);
function GLeaf(x) { this.x = x; }
GLeaf.prototype = Object.create(GMid.prototype);
var G = { Base: GBase, Mid: GMid, Leaf: GLeaf };
function callG(o) { return o.m(); }
check(200, function (i) { assertEq(callG(new G.Leaf(i)), "base:" + i); });
Object.setPrototypeOf(G.Mid.prototype, Other);
check(100, function (i) { assertEq(callG(new G.Leaf(i)), "other"); });

// Some receivers given another prototype (their layout and CLOSED stay).
function HBase() {}
HBase.prototype.m = function () { return "base:" + this.x; };
function HMid() {}
HMid.prototype = Object.create(HBase.prototype);
function HLeaf(x) { this.x = x; }
HLeaf.prototype = Object.create(HMid.prototype);
var H = { Base: HBase, Mid: HMid, Leaf: HLeaf };
function callH(o) { return o.m(); }
check(200, function (i) { assertEq(callH(new H.Leaf(i)), "base:" + i); });
check(200, function (i) {
  var o = new H.Leaf(i);
  if (i % 2) Object.setPrototypeOf(o, Other);
  assertEq(callH(o), i % 2 ? "other" : "base:" + i);
});

// Receivers made with a reassigned `prototype`, so of another prototype
// from the start, alternating with the original's.
function I(x, y) { this.x = x; this.y = y; }
I.prototype.m = function () { return this.x * this.x + this.y; };
function callI(p) { return p.m(); }
check(200, function (i) { assertEq(callI(new I(i, 1)), i * i + 1); });
var protoA = I.prototype;
var protoB = Object.create(protoA);
protoB[key("m")] = function () { return "B"; };
check(200, function (i) {
  I.prototype = i % 2 ? protoB : protoA;
  assertEq(callI(new I(i, 1)), i % 2 ? "B" : i * i + 1);
});

// The name added to some receivers by a compiled add (an IC add way, not
// the engine's), where the analysis does not see the store reach them
// (they reach it through a computed global): a closure of the same script
// as the prototype's, so the read stays predicted, but another closure.
// The field's values are untyped (JSON's), so the stamp has no TYPES,
// which a store of a function would otherwise send to the engine.
function mkJ(tag) { return function () { return tag + this.x; }; }
function J(x) { this.x = x; }
J.prototype.m = mkJ("proto:");
function callJ(p) { return p.m(); }
function ownJ(p, f) { p.m = f; }
function K(x) { this.x = x; }
ownJ(new K(0), mkJ("k:"));
var ownM = mkJ("own:");
var ownJAlias = this[key("ownJ")];
check(200, function (i) { assertEq(callJ(new J(JSON.parse(String(i)))), "proto:" + i); });
check(300, function (i) {
  var p = new J(JSON.parse(String(i)));
  if (i % 2) ownJAlias(p, ownM);
  assertEq(callJ(p), (i % 2 ? "own:" : "proto:") + i);
});

// A receiver of no layout the read's site was predicted for, whose
// prototype holds the method (a JSON object given the class's prototype,
// reaching the read through a computed global; the analysis follows
// neither): the method, inlined built for the site's layout, must not read
// it as that layout (it holds the field at another slot, and another
// property, of the field's type, where the layout has the field).
function sharedM() { return this.x; }
function KA(x) { this.pad = -1; this.x = x; }
KA.prototype.m = sharedM;
function callK(o) { return o.m(); }
check(300, function (i) { assertEq(callK(new KA({ v: i })).v, i); });
var callKAlias = this[key("callK")];
var setProto = Object[key("setPrototypeOf")];
check(300, function (i) {
  var o = JSON.parse("{\"x\":{\"v\":" + i + "},\"y\":{\"v\":-1}}");
  setProto(o, KA.prototype);
  assertEq(callKAlias(o).v, i);
});
