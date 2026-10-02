// Closures and call objects made inline (the Lambda and environment rows)
// must be whole objects: callable, capturing their own environment, with
// each binding undefined until written, and surviving nursery and major
// collections between their creation and use.
function counters(n) {
  var fns = [];
  for (var i = 0; i < n; i++) {
    var k = i;
    fns.push(function(d) {
      var own;  // a binding of the inner call object, undefined at entry
      assertEq(own, undefined);
      own = k + d;
      return function() { return own * 2 + k; };
    });
    if (i % 7 == 0) {
      minorgc();
    }
  }
  return fns;
}

function run(round) {
  var fns = counters(50);
  if (round % 3 == 0) {
    gc();
  }
  var sum = 0;
  for (var i = 0; i < fns.length; i++) {
    var g = fns[i](round);
    if (i % 5 == 0) {
      minorgc();
    }
    // k is shared by every closure of one counters() call: its last value.
    sum += g();
  }
  return sum;
}

for (var round = 0; round < 40; round++) {
  // 50 closures, each (49 + round) * 2 + 49.
  assertEq(run(round), 50 * ((49 + round) * 2 + 49));
}

// A closure created in a loop over a fresh environment per iteration.
function perIteration() {
  var out = [];
  for (let i = 0; i < 30; i++) {
    out.push(() => i);
    if (i % 4 == 0) {
      minorgc();
    }
  }
  return out.map(f => f()).join(",");
}
var expect = [];
for (var i = 0; i < 30; i++) {
  expect.push(i);
}
for (var r = 0; r < 20; r++) {
  assertEq(perIteration(), expect.join(","));
}
