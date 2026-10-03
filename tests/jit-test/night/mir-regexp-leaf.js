// The pristine RegExp.prototype.exec/test on a non-global, non-sticky regexp
// decided in a leaf: a failed match (null / false) and a successful test()
// (true, with the legacy statics updated) return without a call; a
// successful exec() still builds its match. Everything else takes the call
// and must behave exactly as before.

var html = /["'&<>]/;
var word = /(w+)o/;
function ex(re, s) { return re.exec(s); }
function te(re, s) { return re.test(s); }

var plain = ["hello", "no specials here", "", "x".repeat(100)];
var hot = ["a<b", "\"q\"", "it's", "&amp;"];
for (var i = 0; i < 2000; i++) {
  if (i % 400 == 0) gc();
  var p = plain[i % 4], h = hot[i % 4];
  assertEq(ex(html, p), null);
  assertEq(te(html, p), false);
  var m = ex(html, h);
  assertEq(m.index, h.search(html));
  assertEq(m[0], h[m.index]);
  assertEq(m.input, h);
  assertEq(te(html, h), true);
}

// Statics: a successful test() sets them, a failed one leaves them.
assertEq(te(word, "awwwob"), true);
assertEq(RegExp.lastMatch, "wwwo");
assertEq(RegExp.$1, "www");
assertEq(te(word, "nothing"), false);
assertEq(RegExp.lastMatch, "wwwo");
assertEq(ex(word, "zz wo zz")[1], "w");
assertEq(RegExp.$1, "w");

// A rope input (built by concatenation) is flattened by the call path.
for (var i = 0; i < 100; i++) {
  var rope = "abcdefghijklmnopqrstuvwxyz".repeat(2) + (i % 2 ? "<" : "x") + "0123456789abcdefghijklmnop";
  assertEq(te(html, rope), i % 2 == 1);
}

// lastIndex: never written for a non-global regexp; a non-number is read.
html.lastIndex = 3;
assertEq(te(html, "<<"), true);
assertEq(html.lastIndex, 3);
var reads = 0;
html.lastIndex = { valueOf() { reads++; return 0; } };
assertEq(te(html, "plain"), false);
assertEq(reads, 1);
html.lastIndex = 0;

// Global and sticky regexps keep their lastIndex protocol.
var g = /a/g;
var seen = [];
for (var i = 0; i < 6; i++) seen.push(te(g, "aa"), g.lastIndex);
assertEq(seen.join(), "true,1,true,2,false,0,true,1,true,2,false,0");
var y = /b/y;
assertEq(te(y, "ab"), false);
y.lastIndex = 1;
assertEq(te(y, "ab"), true);
assertEq(y.lastIndex, 2);

// A replaced exec, on the instance or the prototype, is called.
var own = /x/;
own.exec = function () { return "own"; };
assertEq(ex(own, "x"), "own");
var origExec = RegExp.prototype.exec;
RegExp.prototype.exec = function () { return { proto: 1 }; };
assertEq(ex(/y/, "y").proto, 1);
assertEq(te(/y/, "y"), true);
RegExp.prototype.exec = origExec;
assertEq(ex(/y/, "z"), null);

// Non-string arguments are converted by the call.
assertEq(te(/1/, 31), true);
assertEq(ex(/u/, undefined)[0], "u");
assertEq(te(/null/, null), true);
