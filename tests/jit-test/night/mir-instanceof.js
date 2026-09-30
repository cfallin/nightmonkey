// `x instanceof C` narrows x to an object on the true branch. A custom
// Symbol.hasInstance may answer true for a primitive; that path must leave
// the narrowed code with the right result and the right branch taken.

function assertEq(a, b, msg) {
  if (a !== b) {
    throw new Error((msg || "") + ": got " + String(a) + ", expected " + String(b));
  }
}

function Pair(a, b) { this.car = a; this.cdr = b; }
function Nil() {}
var nil = new Nil();

function sum(l) {
  var s = 0;
  while (l instanceof Pair) {
    s += l.car;
    l = l.cdr;
  }
  return s;
}

function classify(x, C) {
  if (x instanceof C) {
    return x !== null && typeof x === "object" ? "obj:" + x.car : "prim:" + String(x);
  }
  return "no";
}

// A field read straight off the narrowed value: for a primitive a custom
// hasInstance let through, it must read the primitive's (absent) property.
function direct(x, C) {
  if (x instanceof C) {
    return "t:" + x.car;
  }
  return "f";
}

// Answers true for everything, primitives included.
var Anything = { [Symbol.hasInstance](v) { return true; } };
// Answers true for numbers only.
var Numbers = { [Symbol.hasInstance](v) { return typeof v === "number"; } };

function run() {
  var l = nil;
  for (var i = 0; i < 100; i++) l = new Pair(i, l);
  var vals = [new Pair(7, nil), 3, "s", null, undefined, nil, 2.5, true];
  var total = 0;
  for (var r = 0; r < 200; r++) {
    total += sum(l);
    for (var i = 0; i < vals.length; i++) {
      var x = vals[i];
      var a = classify(x, Pair);
      var b = classify(x, Anything);
      var c = classify(x, Numbers);
      assertEq(a, i === 0 ? "obj:7" : "no", "Pair " + i);
      assertEq(b, x !== null && typeof x === "object" ? "obj:" + x.car : "prim:" + String(x), "Anything " + i);
      assertEq(c, typeof x === "number" ? "prim:" + String(x) : "no", "Numbers " + i);
      if (x !== null && x !== undefined) {
        assertEq(direct(x, Anything), "t:" + (i === 0 ? 7 : undefined), "direct " + i);
        assertEq(direct(x, Numbers), typeof x === "number" ? "t:undefined" : "f", "direct num " + i);
      }
    }
  }
  assertEq(total, 200 * 4950, "sum");
}
run();
