// for-in in MIR: the property iterator, its names, and its close, over
// plain objects, arrays, prototype chains, with keys deleted and added
// during the loop, early exits (break, return), and a throw out of the
// loop body (baseline's unwind closes the iterator).

function keys(o) {
  var s = "";
  for (var k in o) s += k + ",";
  return s;
}
function sumVals(o) {
  var t = 0;
  for (var k in o) t += o[k];
  return t;
}
function firstOver(o, lim) {
  for (var k in o) {
    if (o[k] > lim) return k;
  }
  return null;
}
function countUntil(o, stop) {
  var n = 0;
  for (var k in o) {
    if (k === stop) break;
    n++;
  }
  return n;
}
function deleting(o) {
  var s = "";
  for (var k in o) {
    s += k;
    delete o.b;
  }
  return s;
}
function throwing(o) {
  var seen = 0;
  try {
    for (var k in o) {
      seen++;
      if (k === "c") throw new Error("stop");
    }
  } catch (e) {
    return seen * 10;
  }
  return -1;
}

function P() { this.x = 1; }
P.prototype.y = 2;

for (var i = 0; i < 400; i++) {
  var o = { a: 1, b: 2, c: 3, d: i };
  assertEq(keys(o), "a,b,c,d,");
  assertEq(sumVals(o), 6 + i);
  assertEq(firstOver(o, 2), "c");
  assertEq(countUntil(o, "c"), 2);
  assertEq(deleting({ a: 1, b: 2, c: 3 }), "ac");
  assertEq(throwing(o), 30);
  assertEq(keys([7, 8, 9]), "0,1,2,");
  assertEq(keys(new P()), "x,y,");
  assertEq(keys(null), "");
  assertEq(keys("ab"), "0,1,");
}
