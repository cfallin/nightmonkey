// `Object.defineProperty` on a stamped object runs vouched (keeps TYPES)
// only when the define touches none of the layout's fields and can run no
// JS (`DefineKeepsTypes`). Covers the vouched case (an accessor on a name
// outside the layout, as pdfjs's canvas context gets), a descriptor whose
// `value` is a getter that writes a field off its predicted type, and
// defines that redefine a layout field (as a data property of another
// type, and as an accessor): each read after must see the new value, and
// the define's result is its target. Each case has its own class, so no
// case's writes widen another's claims. (On objects this small the engine
// reports these defines as a structural change and resets the word, so
// the vouch itself is exercised by pdfjs's canvas context, not here.)

// Defines from compiled code: the intercept is on compiled calls (global
// code runs in the interpreter).
function def(o, k, d) { var r = Object.defineProperty(o, k, d); assertEq(r, o); return r; }

// Five copies, not closures of one script: a class is its constructor's
// script.
function A() { this.n = 1; this.log = []; this.p0 = 0; this.p1 = 1; this.p2 = 2; this.p3 = 3; this.p4 = 4; this.p5 = 5; this.p6 = 6; this.p7 = 7; this.p8 = 8; this.p9 = 9; this.p10 = 10; this.p11 = 11; this.p12 = 12; this.p13 = 13; this.p14 = 14; this.p15 = 15; this.p16 = 16; this.p17 = 17; this.p18 = 18; this.p19 = 19; this.p20 = 20; this.p21 = 21; this.p22 = 22; this.p23 = 23; this.p24 = 24; this.p25 = 25; this.p26 = 26; this.p27 = 27; this.p28 = 28; this.p29 = 29; this.p30 = 30; this.p31 = 31; this.p32 = 32; this.p33 = 33; this.p34 = 34; this.p35 = 35; }
A.prototype.step = function () { this.n = this.n + 1; this.log.push(this.n); return this.n; };
A.prototype.sum = function () { return this.n + this.log.length; };
function B() { this.n = 1; this.log = []; this.p0 = 0; this.p1 = 1; this.p2 = 2; this.p3 = 3; this.p4 = 4; this.p5 = 5; this.p6 = 6; this.p7 = 7; this.p8 = 8; this.p9 = 9; this.p10 = 10; this.p11 = 11; this.p12 = 12; this.p13 = 13; this.p14 = 14; this.p15 = 15; this.p16 = 16; this.p17 = 17; this.p18 = 18; this.p19 = 19; this.p20 = 20; this.p21 = 21; this.p22 = 22; this.p23 = 23; this.p24 = 24; this.p25 = 25; this.p26 = 26; this.p27 = 27; this.p28 = 28; this.p29 = 29; this.p30 = 30; this.p31 = 31; this.p32 = 32; this.p33 = 33; this.p34 = 34; this.p35 = 35; }
B.prototype.step = function () { this.n = this.n + 1; this.log.push(this.n); return this.n; };
B.prototype.sum = function () { return this.n + this.log.length; };
function D() { this.n = 1; this.log = []; this.p0 = 0; this.p1 = 1; this.p2 = 2; this.p3 = 3; this.p4 = 4; this.p5 = 5; this.p6 = 6; this.p7 = 7; this.p8 = 8; this.p9 = 9; this.p10 = 10; this.p11 = 11; this.p12 = 12; this.p13 = 13; this.p14 = 14; this.p15 = 15; this.p16 = 16; this.p17 = 17; this.p18 = 18; this.p19 = 19; this.p20 = 20; this.p21 = 21; this.p22 = 22; this.p23 = 23; this.p24 = 24; this.p25 = 25; this.p26 = 26; this.p27 = 27; this.p28 = 28; this.p29 = 29; this.p30 = 30; this.p31 = 31; this.p32 = 32; this.p33 = 33; this.p34 = 34; this.p35 = 35; }
D.prototype.step = function () { this.n = this.n + 1; this.log.push(this.n); return this.n; };
D.prototype.sum = function () { return this.n + this.log.length; };
function E() { this.n = 1; this.log = []; this.p0 = 0; this.p1 = 1; this.p2 = 2; this.p3 = 3; this.p4 = 4; this.p5 = 5; this.p6 = 6; this.p7 = 7; this.p8 = 8; this.p9 = 9; this.p10 = 10; this.p11 = 11; this.p12 = 12; this.p13 = 13; this.p14 = 14; this.p15 = 15; this.p16 = 16; this.p17 = 17; this.p18 = 18; this.p19 = 19; this.p20 = 20; this.p21 = 21; this.p22 = 22; this.p23 = 23; this.p24 = 24; this.p25 = 25; this.p26 = 26; this.p27 = 27; this.p28 = 28; this.p29 = 29; this.p30 = 30; this.p31 = 31; this.p32 = 32; this.p33 = 33; this.p34 = 34; this.p35 = 35; }
E.prototype.step = function () { this.n = this.n + 1; this.log.push(this.n); return this.n; };
E.prototype.sum = function () { return this.n + this.log.length; };
function F() { this.n = 1; this.log = []; this.p0 = 0; this.p1 = 1; this.p2 = 2; this.p3 = 3; this.p4 = 4; this.p5 = 5; this.p6 = 6; this.p7 = 7; this.p8 = 8; this.p9 = 9; this.p10 = 10; this.p11 = 11; this.p12 = 12; this.p13 = 13; this.p14 = 14; this.p15 = 15; this.p16 = 16; this.p17 = 17; this.p18 = 18; this.p19 = 19; this.p20 = 20; this.p21 = 21; this.p22 = 22; this.p23 = 23; this.p24 = 24; this.p25 = 25; this.p26 = 26; this.p27 = 27; this.p28 = 28; this.p29 = 29; this.p30 = 30; this.p31 = 31; this.p32 = 32; this.p33 = 33; this.p34 = 34; this.p35 = 35; }
F.prototype.step = function () { this.n = this.n + 1; this.log.push(this.n); return this.n; };
F.prototype.sum = function () { return this.n + this.log.length; };

function run(c, k) {
  var t = 0;
  for (var i = 0; i < k; i++) { t += c.step(); t += c.sum(); }
  return t;
}

// Vouched: an accessor outside the layout.
var a = new A();
run(a, 200);
def(a, "extra", { get: function () { return this.n * 2; }, configurable: true });
assertEq(a.extra, a.n * 2);
var before = a.n;
run(a, 200);
assertEq(a.n, before + 200);
assertEq(a.extra, a.n * 2);

// A descriptor whose `value` is a getter: it runs JS, which writes `n`
// off its predicted type through the engine (`Object.assign`; a compiled
// store would demote the word itself). Not vouched, so the string is seen.
var b = new B();
run(b, 200);
var desc = {};
Object.defineProperty(desc, "value", { get: function () { Object.assign(b, { n: "s" }); return 7; }, enumerable: true });
def(b, "other", desc);
assertEq(b.other, 7);
assertEq(b.n, "s");
assertEq(b.sum(), "s" + b.log.length);

// An inherited descriptor field (`get` on the descriptor's prototype).
var f = new F();
run(f, 200);
var proto = { get: function () { return 42; } };
def(f, "inh", Object.create(proto));
assertEq(f.inh, 42);
run(f, 10);
assertEq(f.n, 211);

// A layout field redefined as data of another type, and as an accessor.
var d = new D();
run(d, 200);
def(d, "n", { value: "str", writable: true });
assertEq(d.n, "str");
assertEq(d.sum(), "str" + d.log.length);
var e = new E();
run(e, 200);
def(e, "n", { get: function () { return 0.5; }, set: function (v) {}, configurable: true });
assertEq(e.n, 0.5);
assertEq(e.sum(), 0.5 + e.log.length);
assertEq(e.step(), 0.5);
