// Generators and async functions in MIR: suspend writes the frame and
// saves it into the generator; a resume enters the yield's own root at
// its landing, the restored slots guarded back to their types. Covers
// yields in loops with live locals of several types, values sent in by
// next(v), return() and throw() resumptions (through finally blocks and
// catch), yield*, a generator exiting to baseline between yields,
// generators resumed after being started elsewhere, closures over
// generator locals, spread and destructuring of generators, and async
// functions awaiting values and promises, with rejections.

function* counter(n) {
  var s = "";
  var d = 0.5;
  for (var i = 0; i < n; i++) {
    var got = yield i;
    if (got !== undefined) s += got;
    d += 1;
  }
  return s + ":" + d;
}
function* withFinally(log) {
  try {
    yield 1;
    yield 2;
  } finally {
    log.push("f");
  }
}
function* catching() {
  var caught = 0;
  while (true) {
    try {
      yield caught;
    } catch (e) {
      caught += e;
    }
  }
}
function* inner() { yield "a"; yield "b"; return "r"; }
function* outer() {
  var r = yield* inner();
  yield r;
}
function* closures() {
  var k = 0;
  var bump = () => ++k;
  while (k < 5) {
    yield bump();
  }
}
function* shifty(n) {
  // The type of `x` changes across yields: the resume guards miss and
  // exit to baseline at the landing.
  var x = 0;
  for (var i = 0; i < n; i++) {
    yield x;
    x = (i % 7 == 6) ? "s" + i : i;
  }
}

async function adder(a, b) {
  var x = await a;
  var y = await Promise.resolve(b);
  return x + y;
}
async function rejecter(v) {
  try {
    await Promise.reject(v);
  } catch (e) {
    return "caught " + e;
  }
}
async function thrower() { await null; throw new Error("t"); }

for (var r = 0; r < 200; r++) {
  var g = counter(4);
  assertEq(g.next().value, 0);
  assertEq(g.next("x").value, 1);
  assertEq(g.next("y").value, 2);
  assertEq(g.next().value, 3);
  var last = g.next("z");
  assertEq(last.done, true);
  assertEq(last.value, "xyz:4.5");

  var log = [];
  var f = withFinally(log);
  assertEq(f.next().value, 1);
  var ret = f.return(9);
  assertEq(ret.value, 9);
  assertEq(ret.done, true);
  assertEq(log.join(), "f");

  var c = catching();
  c.next();
  assertEq(c.throw(2).value, 2);
  assertEq(c.throw(3).value, 5);

  assertEq([...outer()].join(), "a,b,r");
  assertEq([...closures()].join(), "1,2,3,4,5");
  var [p, q, ...rest] = counter(5);
  assertEq(p + q + rest.length, 4);

  var sh = [...shifty(20)];
  assertEq(sh.length, 20);
  assertEq(sh[7], "s6");
  assertEq(sh[8], 7);

  var e = null;
  var t = counter(2);
  t.next();
  try { t.throw(new Error("boom")); } catch (x) { e = x.message; }
  assertEq(e, "boom");
  assertEq(t.next().done, true);
}

var results = [];
for (var r = 0; r < 100; r++) {
  adder(r, 1).then(v => results.push(v));
  rejecter(r).then(v => results.push(v));
  thrower().catch(e => results.push(e.message));
}
drainJobQueue();
assertEq(results.length, 300);
assertEq(results.filter(x => typeof x == "number").reduce((a, b) => a + b, 0), 5050);
