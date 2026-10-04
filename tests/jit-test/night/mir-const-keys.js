// Element accesses whose key is a string constant are the named accesses
// of that name: the MIR builder builds `o["x"]` as `o.x` where it knows the
// key (a literal, or a local holding one), and the analysis types
// `o[k] = v` / `o[k]` with `k` only string constants as the named write and
// read of each. Keys that are array indexes ("0", "12") stay element
// accesses, and every result must be what the generic access gives.

function Point(x, y) { this.x = x; this.y = y; }
Point.prototype.norm1 = function () { return Math.abs(this.x) + Math.abs(this.y); };

function getLit(o) { return o["x"] + o["y"]; }
function setLit(o, v) { o["x"] = v; o["y"] = v + 1; return o; }
function viaLocal(o) { var k = "x", j = "y"; o[k] = o[j] * 2; return o[k]; }
function protoMethod(o) { return o["norm1"](); }
function lengthOf(a) { return a["length"]; }
function indexStr(a) { return a["0"] + a["2"]; }
function setIndexStr(a, v) { a["1"] = v; return a[1]; }

// A dictionary written and read through keys passed as arguments.
function Registry() { this.table = {}; }
Registry.prototype.add = function (name, fn) { this.table[name] = fn; };
Registry.prototype.run = function (name, x) { return this.table[name](x); };

var acc = { _v: 3, get v() { return this._v * 10; }, set v(x) { this._v = x; } };
function getterLit(o) { return o["v"]; }
function setterLit(o, x) { o["v"] = x; return o._v; }

for (var r = 0; r < 300; r++) {
  if (r % 97 == 0) gc();
  var p = new Point(r, -r);
  assertEq(getLit(p), 0);
  setLit(p, r);
  assertEq(p.x, r);
  assertEq(p.y, r + 1);
  assertEq(viaLocal(p), (r + 1) * 2);
  assertEq(protoMethod(new Point(r, 2 * r)), 3 * r);
  // Another receiver shape at the same sites.
  var q = { y: 5, x: "s" };
  assertEq(getLit(q), "s5");
  assertEq(lengthOf([1, 2, 3, r]), 4);
  assertEq(lengthOf("abcd"), 4);
  assertEq(indexStr([r, 1, 2]), r + 2);
  var arr = [0, 0, 0];
  assertEq(setIndexStr(arr, r), r);
  assertEq(arr.length, 3);
  assertEq(getterLit(acc), acc._v * 10);
  assertEq(setterLit(acc, r), r);

  var reg = new Registry();
  reg.add("inc", function (x) { return x + 1; });
  reg.add("dbl", function (x) { return x * 2; });
  reg.add("str", function (x) { return "<" + x + ">"; });
  assertEq(reg.run("inc", r), r + 1);
  assertEq(reg.run("dbl", r), 2 * r);
  assertEq(reg.run("str", r), "<" + r + ">");
  // A key the dictionary got through the generic path.
  var name = ["d", "b", "l"].join("");
  assertEq(reg.run(name, 4), 8);
}

// A missing property, a shadowing own property, and a frozen object.
function missing(o) { return o["nope"]; }
for (var r = 0; r < 50; r++) assertEq(missing({}), undefined);
var shadow = new Point(1, 2);
shadow.norm1 = function () { return 42; };
assertEq(protoMethod(shadow), 42);
var frozen = Object.freeze({ x: 1, y: 2 });
setLit(frozen, 9);
assertEq(frozen.x, 1);
// A strict write keeps its strictness: a frozen receiver throws.
function setStrict(o, v) { "use strict"; o["x"] = v; return o.x; }
for (var r = 0; r < 200; r++) {
  assertEq(setStrict({ x: 0 }, r), r);
  var threw = false;
  try { setStrict(frozen, r); } catch (e) { threw = e instanceof TypeError; }
  assertEq(threw, true);
}
// A strict write to a getter-only accessor throws; a sloppy one is ignored.
var ro = { get w() { return 7; } };
function setWStrict(o, v) { "use strict"; o["w"] = v; return o["w"]; }
function setWSloppy(o, v) { o["w"] = v; return o["w"]; }
for (var r = 0; r < 200; r++) {
  var threw = false;
  try { setWStrict(ro, r); } catch (e) { threw = e instanceof TypeError; }
  assertEq(threw, true);
  assertEq(setWSloppy(ro, r), 7);
}
