// Values stored in a Map or Set flow, in the analysis, to what reads them
// back (`get`); the facts that buys are guarded like any other. Here a
// value of another class reaches the same map through a store the analysis
// cannot see as a `set` (a computed method name), and a user class with
// its own `get`/`set`/`add` methods is never treated as a collection.

function P(x) { this.x = x; this.y = 2; }
function Q(x) { this.y = 3; this.z = 0; this.x = x * 10; }
var m = new Map(), s = new Set(), w = new WeakMap();
function fill(n) {
  for (var i = 0; i < n; i++) { m.set("k" + i, new P(i)); s.add(new P(i)); }
}
function sum(k) { var p = m.get(k); return p ? p.x + p.y : -1; }
function chained() { var c = new Map().set("a", new P(5)).set("b", new P(6)); return c.get("a").x + c.get("b").x; }
function fromIterable() {
  var ss = new Set([new P(1), new P(2)]), mm = new Map([["a", new P(3)]]);
  var t = 0;
  for (var p of ss) t += p.x;
  return t + mm.get("a").x;
}
function Store() { this.vals = {}; }
Store.prototype.set = function (k, v) { this.vals[k] = v; return 42; };
Store.prototype.get = function (k) { return this.vals[k] || "none"; };
Store.prototype.add = function (v) { return "added " + v; };

fill(50);
var setName = "se" + "t";
for (var r = 0; r < 3000; r++) {
  if (r % 500 == 0) gc();
  var i = r % 60;
  if (r == 1500) for (var j = 0; j < 50; j++) m[setName]("k" + j, new Q(j));
  assertEq(sum("k" + i), i >= 50 ? -1 : r < 1500 ? i + 2 : i * 10 + 3);
  assertEq(chained(), 11);
  assertEq(fromIterable(), 6);
  var st = new Store();
  assertEq(st.set("a", 1), 42);
  assertEq(st.get("a"), 1);
  assertEq(st.get("b"), "none");
  assertEq(st.add(r), "added " + r);
}
var key = {};
w.set(key, new P(9));
assertEq(w.get(key).x, 9);
assertEq(w.get({}), undefined);
var t = 0;
s.forEach(function (p) { t += p.x; });
assertEq(t, 49 * 50 / 2);
