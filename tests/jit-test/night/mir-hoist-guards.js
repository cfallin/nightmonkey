// Guard hoisting (§10.2): guards on values from before a loop, whose
// facts nothing in the loop kills, run once in the preheader, and a
// failure exits at the loop header with the loop's entry state. Covers a
// receiver of another layout arriving at the loop (the hoisted guard
// fails: baseline runs the loop), a receiver changed inside the loop (not
// invariant: nothing hoists), a loop whose body adds a field to the
// receiver (a kill: nothing hoists), loops that run zero times, and
// guarded values that only some iterations use.

function P(x, y) { this.x = x; this.y = y; }
function Q(y, x) { this.y = y; this.x = x; }
function sum(o, n) { var t = 0; for (var i = 0; i < n; i++) t += o.x * o.y; return t; }
function swap(a, b, n) { var t = 0, o = a; for (var i = 0; i < n; i++) { t += o.x; o = (i & 1) ? a : b; } return t; }
function adds(o, n) { var t = 0; for (var i = 0; i < n; i++) { t += o.x; if (i == 5) o.z = 1; } return t; }
function some(o, n) { var t = 0; for (var i = 0; i < n; i++) { if (i % 3 == 0) t += o.x; } return t; }

var p = new P(2, 5), q = new Q(7, 3);
for (var r = 0; r < 400; r++) {
  assertEq(sum(p, 10), 100);
  assertEq(sum(p, 0), 0);
  if (r % 40 == 39) assertEq(sum(q, 10), 210);
  assertEq(swap(p, q, 6), 2 + 3 + 2 + 3 + 2 + 3);
  assertEq(adds(new P(1, 1), 10), 10);
  assertEq(some(p, 10), 8);
  if (r % 50 == 49) assertEq(some({ x: 4 }, 4), 8);
}
