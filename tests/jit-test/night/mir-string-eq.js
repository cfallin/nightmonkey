// Equality of two strings decided inline: one pointer, different lengths,
// or two atoms (deduplicated); anything else (a built string against an
// atom of the same length) compares the characters.
function eq(a, b) { return a === b; }
function ne(a, b) { return a != b; }
function build(s) { return s.split("").join(""); }
var words = ["BT", "ET", "Tf", "Tj", "TJ", "q", "Q", "cm", "re", "f"];
for (var n = 0; n < 200; n++) {
  var w = words[n % words.length];
  assertEq(eq(w, "BT"), w == "BT");
  assertEq(ne(w, "Tj"), w != "Tj");
  var b = build(w);
  assertEq(eq(b, w), true);
  assertEq(eq(b + "x", w), false);
  assertEq(ne(b, w), false);
  var r = "ab" + n + "cd";
  assertEq(eq(r, "ab" + n + "cd"), true);
  assertEq(eq(r, "ab" + (n + 1) + "cd"), false);
  assertEq(eq("", ""), true);
  assertEq(eq(w, 5), false);
  assertEq(ne("5", 5), false);
}
