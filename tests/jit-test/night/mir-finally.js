// try/finally in MIR: the normal entry into the finally block (completion,
// return, break and continue through it) runs in MIR; a throw exits, and
// baseline's unwind runs the finally block and rethrows.

var log = "";
function normal(i) {
  var r = 0;
  try { r = i + 1; } finally { log += "n"; }
  return r;
}
function returning(i) {
  try { return i * 2; } finally { log += "r"; }
}
function looping(n) {
  var t = 0;
  for (var i = 0; i < n; i++) {
    try {
      if (i == 3) continue;
      if (i == 7) break;
      t += i;
    } finally {
      t += 100;
    }
  }
  return t;
}
function throwing(i) {
  try {
    if (i % 5 == 0) throw new Error("x" + i);
    return i;
  } finally {
    log += "t";
  }
}
function nested(i) {
  var s = "";
  try {
    try { s += "a"; if (i % 3 == 0) throw 1; s += "b"; } finally { s += "c"; }
  } catch (e) {
    s += "d";
  } finally {
    s += "e";
  }
  return s;
}

for (var i = 0; i < 400; i++) {
  log = "";
  assertEq(normal(i), i + 1);
  assertEq(returning(i), i * 2);
  assertEq(looping(10), (0 + 1 + 2 + 4 + 5 + 6) + 800);
  var caught = null;
  try { throwing(i); } catch (e) { caught = e.message; }
  assertEq(caught, i % 5 == 0 ? "x" + i : null);
  assertEq(log, "nrt");
  assertEq(nested(i), i % 3 == 0 ? "acde" : "abce");
}
