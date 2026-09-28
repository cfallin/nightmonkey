// Facts are fixed in MIR: an op that may demote a class word keeps the
// caller's facts only on its clean edge, and its dirty edge leaves for
// baseline. These cases demote a layout the caller has proven, through an
// inlined callee (in MIR, and in the callee's baseline rest after it
// exits), a global getter, an element store's IC arm and a property IC
// arm, and read the object again after.

function Pt(x, y) { this.x = x; this.y = y; }

// Inlined callee: most calls do nothing, some reshape `p`.
function mess(p, k) {
  if (k) {
    delete p.x;
    p.x = "s";
  }
  return 1;
}
function viaCallee(p, k) {
  var a = p.x;
  mess(p, k);
  return a + p.x + p.y;
}

// The callee exits to baseline first (a type it has not seen), and its
// baseline rest reshapes `p`.
function messLate(p, k, z) {
  var t = z + 1;
  if (k) {
    delete p.y;
    p.y = [t];
  }
  return t;
}
function viaLate(p, k, z) {
  var a = p.y;
  messLate(p, k, z);
  return a + "" + p.y;
}

// A global getter that reshapes an object the caller has proven.
var victim = null;
Object.defineProperty(globalThis, "g", {
  get: function () {
    if (victim) {
      delete victim.x;
      victim.x = true;
    }
    return 2;
  },
  configurable: true,
});
function viaGetter(p) {
  var a = p.x;
  var b = g;
  return a + b + p.x;
}

// A property IC arm (a receiver of another layout) whose setter reshapes
// the proven object.
function viaSetter(p, q) {
  var a = p.x;
  q.w = 5;
  return a + p.x;
}

for (var n = 0; n < 300; n++) {
  var p = new Pt(n, 1);
  assertEq(viaCallee(p, false), n + n + 1);
  p = new Pt(n, 1);
  assertEq(viaLate(p, false, n), "1" + "1");
  p = new Pt(n, 1);
  assertEq(viaGetter(p), n + 2 + n);
  p = new Pt(n, 1);
  assertEq(viaSetter(p, {}), n + n);
}
for (var n = 0; n < 20; n++) {
  var p = new Pt(n, 1);
  assertEq(viaCallee(p, true), n + "s" + 1);
  p = new Pt(n, 1);
  assertEq(viaLate(p, true, n + 0.5), "1" + (n + 1.5));
  p = new Pt(n, 1);
  victim = p;
  assertEq(viaGetter(p), n + 2 + true);
  victim = null;
  p = new Pt(n, 1);
  var q = {
    set w(v) {
      delete p.x;
      p.x = "t";
    },
  };
  assertEq(viaSetter(p, q), n + "t");
}
