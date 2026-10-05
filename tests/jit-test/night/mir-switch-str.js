// `switch (x)` over string constants in MIR (`switch.str`): an atom subject
// is compared by pointer against the cases' atoms; a non-atom linear string
// by length and characters; a rope exits before the switch and baseline
// runs it; anything not a string takes the default. Duplicate labels: the
// first one wins. Fallthrough and the default's own use of `x` are the
// bytecode's, untouched.

function kind(x) {
  switch (x) {
    case "alpha": return 1;
    case "beta": return 2;
    case "gamma":
    case "delta": return 3;
    case "beta": return 99;          // never: the first "beta" wins
    case "": return 4;
    case "été": return 5;   // Latin-1 beyond ASCII
    case "中文": return 6;    // two-byte
    case "1": return 7;
    case "a-long-attribute-name-past-inline-limit": return 8;
    default: return typeof x == "string" ? -x.length : -100;
  }
}

function fallthrough(x) {
  var r = "";
  switch (x) {
    case "a": r += "a";
    case "b": r += "b";
    case "c": r += "c"; break;
    case "d": r += "d";
    default: r += "z" + x;
  }
  return r;
}

var dyn = "gam" + "ma";
function cases() {
  var flatNonAtom = ("xx" + dyn).slice(2);   // linear, not an atom
  var rope = dyn.substring(0, 2) + dyn.substring(2) + "";
  // Long enough to be a rope (short concatenations are inline strings).
  var half = "a-long-attribute-nam";
  var longRope = half + "e-past-inline-limit".slice(0, 19 + (i & 0));
  var longAtom = "a-long-attribute-name-past-inline-limit";
  return [
    ["alpha", 1], ["beta", 2], ["gamma", 3], ["delta", 3], ["", 4],
    ["été", 5], ["中文", 6], ["1", 7],
    ["epsilon", -7], ["alph", -4], ["alphaa", -6],
    [1, -100], [null, -100], [undefined, -100], [{ toString() { return "alpha"; } }, -100],
    [flatNonAtom, 3], [rope, 3], [("x" + "中文").slice(1), 6],
    ["beta".toUpperCase().toLowerCase(), 2],
    [longRope, 8], [longAtom, 8], [longRope + "x", -40],
  ];
}

for (var i = 0; i < 300; i++) {
  var cs = cases();
  for (var j = 0; j < cs.length; j++) assertEq(kind(cs[j][0]), cs[j][1]);
  assertEq(fallthrough("a"), "abc");
  assertEq(fallthrough("b"), "bc");
  assertEq(fallthrough("c"), "c");
  assertEq(fallthrough("d"), "dzd");
  assertEq(fallthrough("e" + i), "ze" + i);
  assertEq(fallthrough(i), "z" + i);
}
