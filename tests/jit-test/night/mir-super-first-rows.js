// A constructor's layout row puts the fields its `.call` delegates (a base
// constructor) add before its own, wherever the call sits, so subclasses
// of one base share the base's fields at the same slots and a base method
// reads them through one guard over the subclasses. The objects are still
// exactly what the constructors' stores make, in insertion order: a
// subclass that adds its own fields before calling its base gets them at
// later slots than it adds them, which only the slots may show.

function keysOf(o) { return Object.keys(o).join(); }

function Base(a, b) { this.a = a; this.b = b; this.dir = 0; }
Base.prototype.sum = function () { return this.a + this.b + this.dir; };
Base.prototype.flip = function () { this.dir = this.dir ? 0 : 1; return this.dir; };

// Own fields first, then the base: its row is a, b, dir, s, t.
function Early(a, b, s) { this.dir = -1; this.s = s; this.t = s * 2; Base.call(this, a, b); }
Early.prototype = Object.create(Base.prototype);
// The base first: its row is the same order it adds in.
function Late(a, b, u) { Base.call(this, a, b); this.u = u; }
Late.prototype = Object.create(Base.prototype);
// The base in the middle.
function Mid(a, b, m) { this.m = m; Base.call(this, a, b); this.n = m + 1; }
Mid.prototype = Object.create(Base.prototype);

function sumOf(o) { return o.sum(); }
function make(i) {
  switch (i % 3) {
    case 0: return new Early(i, i + 1, i + 2);
    case 1: return new Late(i, i + 1, i + 2);
    default: return new Mid(i, i + 1, i + 2);
  }
}

var held = [];
for (var i = 0; i < 900; i++) {
  if (i % 100 == 0) gc();
  if (i % 37 == 0) minorgc();
  var o = make(i);
  assertEq(sumOf(o), 2 * i + 1);
  assertEq(o.flip(), 1);
  assertEq(sumOf(o), 2 * i + 2);
  switch (i % 3) {
    case 0:
      assertEq(keysOf(o), "dir,s,t,a,b");
      assertEq(o.t, 2 * (i + 2));
      assertEq(JSON.stringify(o), JSON.stringify({ dir: 1, s: i + 2, t: 2 * (i + 2), a: i, b: i + 1 }));
      break;
    case 1:
      assertEq(keysOf(o), "a,b,dir,u");
      assertEq(o.u, i + 2);
      break;
    default:
      assertEq(keysOf(o), "m,a,b,dir,n");
      assertEq(o.n, i + 3);
      break;
  }
  if (i % 7 == 0) held.push(o);
}
gc();
for (var j = 0; j < held.length; j++) {
  var o = held[j];
  assertEq(o.a + 1, o.b);
  assertEq(o.dir, 1);
  var names = [];
  for (var k in o) if (o.hasOwnProperty(k)) names.push(k);
  assertEq(names.join(), keysOf(o));
}
