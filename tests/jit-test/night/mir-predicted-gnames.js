// A global the analysis predicts holds one function (`gname_fns`) is read
// in MIR as that function behind its value fuse's predicted state
// (`check.binding.fn`): a call or `new` through it needs no callee guard.
// Rewrites the analysis cannot see (computed-key stores on the global)
// move the binding to another function, to a non-function, and back to
// the predicted one; every read must see the current value, and the
// predicted state must come back with the predicted function.

function target(x) { return x + 1; }
function other(x) { return x * 2; }
function Pt(a) { this.a = a; }
function Other(a) { this.b = a; }

function callIt(x) { return target(x); }
function readIt() { return target; }
function callTwice(x) { return target(target(x)); }
function make(x) { return new Pt(x); }
function allocCall(n) {
  // Allocation between the read and the call, every iteration.
  var s = 0;
  for (var i = 0; i < n; i++) {
    var o = { v: i };
    s += target(o.v);
  }
  return s;
}

var g = this;
var key = ["tar", "get"].join("");
var ctorKey = ["P", "t"].join("");
var savedTarget = target;
var savedPt = Pt;

function expectCall(r, x) {
  if (r < 100 || r >= 300) return x + 1;
  if (r < 200) return x * 2;
  return "throws";
}

for (var r = 0; r < 400; r++) {
  // A GC resets the blown fuse; the next read re-arms it, armed, not in
  // the predicted state.
  if (r == 100) { g[key] = other; gc(); }
  if (r == 200) g[key] = 5;
  if (r == 300) g[key] = savedTarget;
  if (r == 150) g[ctorKey] = Other;
  if (r == 250) g[ctorKey] = savedPt;

  var want = expectCall(r, r);
  if (want === "throws") {
    var threw = false;
    try { callIt(r); } catch (e) { threw = e instanceof TypeError; }
    assertEq(threw, true);
    assertEq(readIt(), 5);
  } else {
    assertEq(callIt(r), want);
    assertEq(callTwice(r), expectCall(r, expectCall(r, r)));
    assertEq(readIt(), r < 100 || r >= 300 ? savedTarget : other);
    var n = 20, s = 0;
    for (var i = 0; i < n; i++) s += expectCall(r, i);
    assertEq(allocCall(n), s);
  }

  var p = make(r);
  if (r >= 150 && r < 250) {
    assertEq(p instanceof Other, true);
    assertEq(p.b, r);
  } else {
    assertEq(p instanceof savedPt, true);
    assertEq(p.a, r);
  }
}
assertEq(target, savedTarget);

// A global holding a class: never called as a plain function (its call
// throws), constructed as one.
var Klass = class { constructor(a) { this.k = a; } };
function callKlass(x) { return Klass(x); }
function newKlass(x) { return new Klass(x).k; }
for (var r = 0; r < 200; r++) {
  var threw = false;
  try { callKlass(r); } catch (e) { threw = e instanceof TypeError; }
  assertEq(threw, true);
  assertEq(newKlass(r), r);
}
