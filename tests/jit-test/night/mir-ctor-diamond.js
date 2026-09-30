// A constructor reading another object's field through a typed site whose
// fallback is the generic op (crypto's Montgomery: `this.mt2 = 2 * m.t`),
// and an element of a typed array the same way (pdfjs's
// ArithmeticDecoder), with receivers of other layouts reaching the fallback
// and getters on it. The object under construction must come out whole.

function assertEq(a, b, msg) {
  if (a !== b) {
    throw new Error((msg || "") + ": got " + String(a) + ", expected " + String(b));
  }
}

function Big(t) {
  this.t = t;
  this.s = 0;
}
Big.prototype.inv = function () { return this.t * 3 + 1; };

function Other(t) {
  this.pad = 1;
  this.t = t;
}
Other.prototype.inv = function () { return 7; };

var withGetter = {
  inv: function () { return 9; },
  get t() { return 11; },
};

function Mont(m) {
  this.m = m;
  this.mp = m.inv();
  this.mpl = this.mp & 0x7fff;
  this.mph = this.mp >> 15;
  this.mt2 = 2 * m.t;
}

function Decoder(data, start, end) {
  this.data = data;
  this.bp = start;
  this.dataEnd = end;
  this.chigh = data[start];
  this.clow = 0;
  this.ct = 8;
}

function run() {
  var bytes = new Uint8Array([5, 6, 7, 8]);
  var arr = [50, 60, 70, 80];
  var total = 0;
  for (var i = 0; i < 2000; i++) {
    var m = i % 5 === 0 ? new Other(i) : i % 7 === 0 ? withGetter : new Big(i);
    var x = new Mont(m);
    var want = m === withGetter ? 22 : 2 * i;
    assertEq(x.mt2, want, "mt2 " + i);
    assertEq(x.m, m, "m");
    assertEq(x.mpl, x.mp & 0x7fff, "mpl");
    assertEq(Object.keys(x).join(","), "m,mp,mpl,mph,mt2", "keys");
    var src = i % 3 === 0 ? arr : bytes;
    var d = new Decoder(src, i & 3, 4);
    assertEq(d.chigh, src[i & 3], "chigh " + i);
    assertEq(d.ct, 8, "ct");
    // Out of bounds: the generic arm.
    var e = new Decoder(bytes, 10, 4);
    assertEq(e.chigh, undefined, "oob");
    total += x.mt2 + (d.chigh | 0);
  }
  return total;
}
var a = run();
var b = run();
assertEq(a, b, "stable");
