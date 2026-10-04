// An array literal's elements stored in place for every kind of value,
// strings and objects included. A literal tenured mid-initialization (an
// element expression runs a minor GC) owes the nursery values stored after
// it a post-barrier, or the next minor GC loses them.

function fresh(i) { return { i: i, s: "s" + i }; }
function tenureNow(i) { minorgc(); return fresh(i); }
function lit(i, s) { return [s, fresh(i), i, tenureNow(i + 1), fresh(i + 2), "t" + i, [i]]; }

var kept = [];
for (var i = 0; i < 600; i++) {
  var a = lit(i, "k" + i);
  if (i % 3 == 0) kept.push(a);
  if (i % 50 == 0) gc();
}
minorgc();
gc();
for (var j = 0; j < kept.length; j++) {
  var i = 3 * j, a = kept[j];
  assertEq(a.length, 7);
  assertEq(a[0], "k" + i);
  assertEq(a[1].i, i);
  assertEq(a[1].s, "s" + i);
  assertEq(a[2], i);
  assertEq(a[3].i, i + 1);
  assertEq(a[4].i, i + 2);
  assertEq(a[4].s, "s" + (i + 2));
  assertEq(a[5], "t" + i);
  assertEq(a[6][0], i);
}
// Holes still take the helper.
function holey(x) { return [x, , x]; }
for (var r = 0; r < 200; r++) {
  var h = holey({ r: r });
  assertEq(1 in h, false);
  assertEq(h[2].r, r);
}
