// MIR for a script with try/catch: the try block is ordinary code whose
// throws exit to baseline at their pc (`exit.throw`), where the handler
// runs; the catch code is baseline's alone. Locals written in the try
// block reach the handler through the frame.
function parse(s) {
  var stage = 0;
  try {
    stage = 1;
    var v = JSON.parse(s);
    stage = 2;
    return v.x + stage;
  } catch (e) {
    return "caught at " + stage;
  }
}
function loopTry(n) {
  var t = 0;
  for (var i = 0; i < n; i++) {
    try {
      if (i % 7 == 6) throw i;
      t += i;
    } catch (e) {
      t -= e;
    }
  }
  return t;
}
function nested(o) {
  try {
    return o.a.b;
  } catch (e) {
    return e instanceof TypeError;
  }
}
for (var r = 0; r < 60; r++) {
  assertEq(parse('{"x": 1}'), 3);
  assertEq(parse("{"), "caught at 1");
  assertEq(loopTry(14), (0+1+2+3+4+5) - 6 + (7+8+9+10+11+12) - 13);
  assertEq(nested({a: {b: 4}}), 4);
  assertEq(nested({}), true);
}
assertEq(loopTry(20000) > 0, true);
