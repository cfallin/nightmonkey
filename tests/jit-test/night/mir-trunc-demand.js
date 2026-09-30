// Truncation demand over SSA (`opt::trunc_demand`): an int32 add or sub
// whose result only reaches ToInt32 (bit ops, shifts, other such sums,
// through locals and block params) is a wrapping add, with no overflow
// check. Each compiled function is checked against the same computation
// in global code, which the interpreter runs.

// A hash mix: the sums pass through the local before their truncating
// uses, and go out of int32 range every iteration.
function jenkins(key, len) {
  var hash = 0;
  for (var i = 0; i < len; ++i) {
    hash += key[i];
    hash += (hash << 10);
    hash ^= (hash >> 6);
  }
  hash += (hash << 3);
  hash ^= (hash >> 11);
  hash += (hash << 15);
  return hash;
}

// Sub, and a chain of several sums before the truncation.
function mix(a, b, c) {
  var t = a - b;
  var u = t + c;
  var w = u - a;
  return (w + t) | 0;
}

// Not demanded: a sum carried around a loop grows past 2^53, where the
// double rounds; only its final value is truncated, and that must be
// ToInt32 of the rounded double, not the wrapped sum.
function carried(n, d) {
  var s = 0;
  for (var i = 0; i < n; i++) s = s + d;
  return s | 0;
}

var keys = [];
for (var i = 0; i < 64; i++) keys.push((i * 7919) % 1000);

var ref = [];
for (var r = 0; r < 4; r++) {
  var hash = 0;
  for (var i = 0; i < keys.length; ++i) {
    hash += keys[i];
    hash += (hash << 10);
    hash ^= (hash >> 6);
  }
  hash += (hash << 3);
  hash ^= (hash >> 11);
  hash += (hash << 15);
  ref.push(hash);
  keys[r] += 1;
}
keys[0] -= 1; keys[1] -= 1; keys[2] -= 1; keys[3] -= 1;
for (var r = 0; r < 4; r++) {
  for (var k = 0; k < 300; k++) assertEq(jenkins(keys, keys.length), ref[r]);
  keys[r] += 1;
}

var big = 0x7fffffff, neg = -0x80000000;
var cases = [[1, 2, 3], [big, neg, big], [neg, big, neg], [big, big, big], [neg, neg, neg], [0, big, 1]];
for (var c = 0; c < cases.length; c++) {
  var a = cases[c][0], b = cases[c][1], cc = cases[c][2];
  var t = a - b, u = t + cc, w = u - a;
  var want = (w + t) | 0;
  for (var k = 0; k < 300; k++) assertEq(mix(a, b, cc), want);
}

// 2^22 adds of 2^31-1 pass 2^53; 5M of them round many times.
var n = 5000000, s = 0;
for (var i = 0; i < n; i++) s = s + big;
assertEq(carried(n, big), s | 0);
