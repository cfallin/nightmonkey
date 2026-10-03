// `typeof x == T` decided inline -- by the tag for a primitive, by the class
// for an object (the function classes, then a class with no call hook that is
// neither a proxy nor emulates undefined) -- and `a + b` of two strings made a
// nursery rope inline. Every kind of value meets every typeof compare at one
// site, and the objects the class test must not decide (a callable proxy, a
// plain proxy, an object that emulates undefined) reach the helper.

var dda = typeof createIsHTMLDDA === "function" ? createIsHTMLDDA() : undefined;
var values = [
  undefined, null, true, 0, -1.5, NaN, "", "s", Symbol("y"), 10n,
  {}, [], function () {}, () => 1, class K {}, Math.max, new Map(), /re/,
  new Proxy({}, {}), new Proxy(function () {}, {}), Object.create(null), new Date(0),
];
var expect = [
  "undefined", "object", "boolean", "number", "number", "number", "string", "string", "symbol", "bigint",
  "object", "object", "function", "function", "function", "function", "object", "object",
  "object", "function", "object", "object",
];
if (dda !== undefined) {
  values.push(dda);
  expect.push("undefined");
}

function kinds(v) {
  var r = "";
  if (typeof v == "undefined") r += "u";
  if (typeof v === "object") r += "o";
  if (typeof v == "function") r += "f";
  if (typeof v === "string") r += "s";
  if (typeof v == "number") r += "n";
  if (typeof v == "boolean") r += "b";
  if (typeof v == "symbol") r += "y";
  if (typeof v == "bigint") r += "g";
  if (typeof v != "object") r += "!o";
  if (typeof v !== "function") r += "!f";
  if (typeof v != "undefined") r += "!u";
  return r;
}
function want(t) {
  var r = { undefined: "u", object: "o", function: "f", string: "s", number: "n", boolean: "b", symbol: "y", bigint: "g" }[t];
  if (t != "object") r += "!o";
  if (t != "function") r += "!f";
  if (t != "undefined") r += "!u";
  return r;
}
for (var i = 0; i < 400; i++) {
  var j = i % values.length;
  assertEq(kinds(values[j]), want(expect[j]));
}

// Ropes: either half empty, Latin1 and two-byte halves, results at and past
// the inline-string limits (24 Latin1, 12 two-byte chars), long chains, and
// ropes kept across minor and major GCs.
function cat(a, b) { return a + b; }
function chain(n, a, b) { var r = ""; for (var k = 0; k < n; k++) { r += a; r += b; } return r; }
var kept = [];
for (var i = 0; i < 3000; i++) {
  if (i % 500 == 0) gc();
  if (i % 97 == 0) minorgc();
  var k = i % 30;
  var a = "abcdefghijklmnopqrstuvwxyz".slice(0, k);
  var b = "\u0100\u0101\u0102\u0103\u0104\u0105\u0106\u0107\u0108\u0109\u010a\u010b\u010c".slice(0, k % 14);
  var s = cat(a, b);
  assertEq(s.length, a.length + b.length);
  assertEq(s.slice(0, a.length), a);
  assertEq(s.slice(a.length), b);
  assertEq(cat("", s), s);
  assertEq(cat(s, ""), s);
  var t = cat(a, a);
  assertEq(t.length, 2 * a.length);
  assertEq(t, a.repeat(2));
  if (i % 50 == 0) kept.push([s, a, b]);
}
var big = chain(2000, "<div", ">x\u1234</div>");
assertEq(big.length, 2000 * 13);
assertEq(big.charCodeAt(big.length - 7), 0x1234);
assertEq(big.indexOf("</div><div"), 7);
gc();
for (var [s, a, b] of kept) {
  assertEq(s, a + b);
  assertEq(s.length, a.length + b.length);
}
