// An object under construction is typed by the set of its layout's fields
// it has had added, in any order (MIR.md §2.3): its class word carries the
// set (bit i, field i at slot i) beside the CONSTRUCTING sentinel, and an
// add past its span (a field ahead of others in the row) leaves the slots
// it skips holding undefined until their fields come. The objects must be
// exactly what the constructors' stores make, in insertion order, whatever
// the order, with GCs among the adds, with `this` leaked half-made, and
// with a setter for a field's name arriving on the prototype.

function keysOf(o) { return Object.keys(o).join(); }

// A half-made object whose set of fields reads as another layout's
// identity, where code typed for that layout reads it (reached through a
// computed global, which the analysis does not follow, so that code is
// typed for the layout alone): it is no instance of that layout (the guard
// sees the sentinel), so the read finds the prototype's property, not a
// slot. B leaks with every set of its first four fields, 1 to 15 (its row
// is the dead branch's order; the adds, through computed keys, are the
// engine's, whose hook records each in the set): one of them is A's
// identity, whatever layout A is. A's values are JSON's, untyped, so its
// guard asks no TYPES, which the engine's stores drop from B.
function key(s) { return s.split("").join(""); }
function A(a, b) { this.a = a; this.b = b; }
function readB(o) { return o.b; }
for (var i = 0; i < 300; i++) {
  var a = new A(JSON.parse("[" + i + "]"), JSON.parse("{\"v\":" + i + "}"));
  assertEq(readB(a).v, i);
}
var readBAlias = this[key("readB")];
var fieldNames = [key("p"), key("q"), key("r"), key("s")];
var leakedB = [];
function B(x, t) {
  if (x === "never") { this.p = 0; this.q = 0; this.r = 0; this.s = 0; }
  for (var k = 0; k < 4; k++) {
    if (t & (1 << k)) this[fieldNames[k]] = x;
  }
  leakedB.push(readBAlias(this));
  this.b = x;
}
B.prototype.b = "proto-b";
for (var i = 0; i < 600; i++) {
  leakedB.length = 0;
  var b = new B(i, 1 + i % 15);
  assertEq(leakedB[0], "proto-b");
  assertEq(b.b, i);
}

// Two orders at one site: the row is the first branch's order.
function P(a, b, flip) {
  if (flip) { this.y = b; this.x = a; } else { this.x = a; this.y = b; }
  this.z = a + b;
}
function mkP(i) { return new P(i, i * 2, i & 1); }
for (var i = 0; i < 400; i++) {
  var p = mkP(i);
  assertEq(keysOf(p), i & 1 ? "y,x,z" : "x,y,z");
  assertEq(p.x + p.y + p.z, 6 * i);
  assertEq(p.hasOwnProperty("x") && p.hasOwnProperty("y"), true);
}

// The last field first, a GC with the first two slots skipped (they must
// hold undefined: the GC traces the span), then the rest.
// (Object values throughout: reused nursery memory then holds stale
// pointers where a slot is not initialized.)
function Q(a, b, c) {
  this.c = c;
  if (a.v < 0) { this.a = a; this.b = b; } else { this.b = b; gcIf(b.v); this.a = a; }
}
Q.prototype.a = "proto-a";
function gcIf(n) { if (n % 50 == 0) gc(); else if (n % 7 == 0) minorgc(); }
function mkQ(i) { return new Q({ v: i }, { v: i + 1 }, { v: i + 2 }); }
var held = [];
for (var i = 0; i < 400; i++) {
  var q = mkQ(i);
  if (i % 3 == 0) held.push(q);
  assertEq(keysOf(q), "c,b,a");
}
gc();
for (var i = 0; i < held.length; i++) {
  assertEq(held[i].a.v, 3 * i);
  assertEq(held[i].b.v, 3 * i + 1);
  assertEq(held[i].c.v, 3 * i + 2);
}

// Different sets on two paths, then a field both add: the object is still
// exactly what was added.
function R(m, n) {
  if (m & 1) this.u = m;
  this.v = n;
  if (m & 2) this.w = m + n;
}
function mkR(i) { return new R(i, -i); }
for (var i = 0; i < 400; i++) {
  var r = mkR(i);
  var want = (i & 1 ? "u," : "") + "v" + (i & 2 ? ",w" : "");
  assertEq(keysOf(r), want);
  assertEq(r.v, -i);
}

// `this` leaked half-made, out of order: a callee sees the fields so far
// (and the prototype's for the rest).
var seen = [];
function look(o) { seen.push(keysOf(o) + "|" + o.s); }
function S(s, t) { this.t = t; look(this); this.s = s; look(this); }
S.prototype.s = "proto-s";
function mkS(i) { return new S(i, -i); }
for (var i = 0; i < 300; i++) {
  seen.length = 0;
  var o = mkS(i);
  assertEq(seen[0], "t|proto-s");
  assertEq(seen[1], "t,s|" + i);
  assertEq(keysOf(o), "t,s");
}

// A setter for a field's name on the prototype, arriving mid-run: an add
// out of order must still run it.
function T(p, q, flip) {
  if (flip) { this.q = q; this.p = p; } else { this.p = p; this.q = q; }
}
function mkT(i) { return new T(i, i * 3, i & 1); }
var setterLog = 0;
for (var i = 0; i < 400; i++) {
  if (i == 200) {
    Object.defineProperty(T.prototype, "p", {
      set(v) { setterLog++; }, get() { return "got-p"; }, configurable: true,
    });
  }
  var t = mkT(i);
  if (i >= 200) {
    assertEq(keysOf(t), "q");
    assertEq(t.p, "got-p");
  } else {
    assertEq(keysOf(t), i & 1 ? "q,p" : "p,q");
    assertEq(t.p, i);
  }
}
assertEq(setterLog, 200);
