// Memory value numbering in loops (`mem::mem_vn`): two reads of one
// element in an iteration with no store between them are one read, though
// the loop stores elsewhere; a store that may alias the element between
// two reads keeps both, whichever array it goes through.

// The am3 shape: `a[i]` read twice before `w[j] = ...`.
function twice(a, w, n) {
  var s = 0;
  for (var i = 0, j = 0; i < n; i++, j++) {
    var l = a[i] & 0x3fff;
    var h = a[i] >> 14;
    w[j] = (l + h) | 0;
    s = (s + l * 3 + h) | 0;
  }
  return s;
}

// The store between the reads hits the read element when `w === a` and
// `k == i`; the second read must see it.
function storeBetween(a, w, n, k) {
  var s = 0;
  for (var i = 0; i < n; i++) {
    var x = a[i];
    w[k + i] = x + 1;
    var y = a[i];
    s = (s + x * 1000 + y) | 0;
  }
  return s;
}

// Reads on either side of a store through the same array in a nested
// loop, the store on the inner loop's back edge.
function nested(a, n) {
  var s = 0;
  for (var i = 0; i < n; i++) {
    var before = a[i];
    for (var j = 0; j < 3; j++) a[i] = a[i] + 1;
    s = (s + a[i] - before) | 0;
  }
  return s;
}

function fresh(n) {
  var a = [];
  for (var i = 0; i < n; i++) a.push(i * 1000003);
  return a;
}

for (var r = 0; r < 200; r++) {
  if (r % 50 == 0) gc();
  var a = fresh(64), w = fresh(64);
  var want = 0;
  for (var i = 0; i < 64; i++) {
    var l = a[i] & 0x3fff, h = a[i] >> 14;
    want = (want + l * 3 + h) | 0;
  }
  assertEq(twice(a, w, 64), want);
  for (var i = 0; i < 64; i++) assertEq(w[i], ((a[i] & 0x3fff) + (a[i] >> 14)) | 0);

  // Distinct arrays: both reads see the same element.
  var b = fresh(64), c = fresh(64);
  var wantB = 0;
  for (var i = 0; i < 64; i++) wantB = (wantB + b[i] * 1000 + b[i]) | 0;
  assertEq(storeBetween(b, c, 64, 0), wantB);

  // The same array, the store at the read index: y == x + 1.
  var d = fresh(64);
  var wantD = 0;
  for (var i = 0; i < 64; i++) wantD = (wantD + (i * 1000003) * 1000 + (i * 1000003 + 1)) | 0;
  assertEq(storeBetween(d, d, 64, 0), wantD);

  // The same array, the store one ahead: the next iteration's x is the
  // stored value.
  var e = fresh(65);
  var x = e[0], wantE = 0;
  for (var i = 0; i < 64; i++) {
    var y = x;
    wantE = (wantE + x * 1000 + y) | 0;
    x = x + 1;
  }
  assertEq(storeBetween(e, e, 64, 1), wantE);

  assertEq(nested(fresh(32), 32), 96);
}
