// An inlined `new` of a constructor whose body starts by storing its
// formals into its first fields makes the object with those fields
// (`new_this.init`): the construct cell's final shape and one check of the
// prototype chain inline, else the runtime's adds. The object must be
// exactly what the constructor's stores make, whatever the prototype chain
// does meanwhile: a setter or a read-only property of a field's name added
// to it, a reassigned `prototype`, a longer chain; and with missing
// arguments, values outside a field's claim, and GCs.

function Pair(car, cdr) { this.car = car; this.cdr = cdr; }
function mkPair(a, b) { return new Pair(a, b); }

function Vec3(x, y, z) { this.x = x; this.y = y; this.z = z; this.len = x * x + y * y + z * z; }
function mkVec(i) { return new Vec3(i, i + 1, i + 2); }

function keysOf(o) { return Object.keys(o).join(); }
function desc(o, k) {
  var d = Object.getOwnPropertyDescriptor(o, k);
  return d ? [d.value, d.writable, d.enumerable, d.configurable].join() : "none";
}

// The plain case, and a prefix followed by more fields.
for (var r = 0; r < 200; r++) {
  var p = mkPair(r, "s" + r);
  assertEq(p.car, r);
  assertEq(p.cdr, "s" + r);
  assertEq(keysOf(p), "car,cdr");
  assertEq(desc(p, "car"), r + ",true,true,true");
  assertEq(p instanceof Pair, true);
  assertEq(Object.getPrototypeOf(p), Pair.prototype);
  var v = mkVec(r);
  assertEq(keysOf(v), "x,y,z,len");
  assertEq(v.len, r * r + (r + 1) * (r + 1) + (r + 2) * (r + 2));
}

// Fresh objects as values, with GCs among the constructions.
var held = [];
for (var r = 0; r < 300; r++) {
  if (r % 50 == 0) gc();
  if (r % 7 == 0) minorgc();
  var p = mkPair({ i: r }, [r]);
  held.push(p);
}
for (var r = 0; r < 300; r++) {
  assertEq(held[r].car.i, r);
  assertEq(held[r].cdr[0], r);
}

// Missing arguments: the fields hold undefined, in order.
function mkPartial(a) { return new Pair(a); }
for (var r = 0; r < 100; r++) {
  var p = mkPartial(r);
  assertEq(keysOf(p), "car,cdr");
  assertEq(p.cdr, undefined);
}

// A setter on the prototype for a field's name: the store runs it, and the
// object never gets that field.
function Pt(x, y) { this.x = x; this.y = y; }
function mkPt(i) { return new Pt(i, i * 2); }
var setterLog = [];
for (var r = 0; r < 300; r++) {
  if (r == 150) {
    Object.defineProperty(Pt.prototype, "y", {
      set(v) { setterLog.push(v); }, get() { return "proto-y"; }, configurable: true,
    });
  }
  if (r == 250) delete Pt.prototype.y;
  var p = mkPt(r);
  assertEq(p.x, r);
  if (r >= 150 && r < 250) {
    assertEq(keysOf(p), "x");
    assertEq(p.y, "proto-y");
  } else {
    assertEq(keysOf(p), "x,y");
    assertEq(p.y, r * 2);
  }
}
assertEq(setterLog.length, 100);
assertEq(setterLog[0], 300);

// A read-only property of a field's name further up the chain: the
// (sloppy) store does nothing.
function Q(a, b) { this.a = a; this.b = b; }
function mkQ(i) { return new Q(i, -i); }
for (var r = 0; r < 300; r++) {
  if (r == 100) Object.defineProperty(Object.prototype, "b", { value: "ro", writable: false, configurable: true });
  if (r == 200) delete Object.prototype.b;
  var q = mkQ(r);
  if (r >= 100 && r < 200) {
    assertEq(keysOf(q), "a");
    assertEq(q.b, "ro");
  } else {
    assertEq(keysOf(q), "a,b");
    assertEq(q.b, -r);
  }
}

// A reassigned `prototype`, and back.
function R(m, n) { this.m = m; this.n = n; }
function mkR(i) { return new R(i, i + 1); }
var protoA = R.prototype;
var protoB = { kind: "B" };
for (var r = 0; r < 300; r++) {
  if (r == 100) R.prototype = protoB;
  if (r == 200) R.prototype = protoA;
  var o = mkR(r);
  assertEq(Object.getPrototypeOf(o), r >= 100 && r < 200 ? protoB : protoA);
  assertEq(keysOf(o), "m,n");
  assertEq(o.n, r + 1);
}

// A longer prototype chain.
function Base() {}
function Deep(u, w) { this.u = u; this.w = w; }
Deep.prototype = Object.create(Object.create(Base.prototype));
function mkDeep(i) { return new Deep(i, String(i)); }
for (var r = 0; r < 200; r++) {
  var d = mkDeep(r);
  assertEq(d instanceof Base, true);
  assertEq(keysOf(d), "u,w");
  assertEq(d.w, String(r));
}

// Values outside what the analysis saw for a field (a number field given
// strings and objects later).
function N(k, v) { this.k = k; this.v = v; }
function mkN(i, v) { return new N(i, v); }
for (var r = 0; r < 300; r++) {
  var val = r < 200 ? r * 1.5 : r < 250 ? "str" + r : { r: r };
  var o = mkN(r, val);
  assertEq(o.k, r);
  if (r < 200) assertEq(o.v, r * 1.5);
  else if (r < 250) assertEq(o.v, "str" + r);
  else assertEq(o.v.r, r);
}
