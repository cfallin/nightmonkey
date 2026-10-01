// A call whose predicted targets are all inlined: a callee none of them is
// (a function the analysis did not see reach the site, or no function)
// exits for baseline to call it, instead of a generic call rejoining. Every
// case must match the spec, in loops too.
function check(got, want, what) {
  if (!Object.is(got, want)) throw new Error(what + " = " + String(got) + ", want " + String(want));
}

function P(x) { this.x = x; }
P.prototype.get = function () { return this.x; };
function Q(x) { this.x = x; }
Q.prototype.get = function () { return -this.x; };

function sum(arr) {
  var s = 0;
  for (var i = 0; i < arr.length; i++) s += arr[i].get();
  return s;
}
var ps = [];
for (var i = 0; i < 20; i++) ps.push(new P(i));
for (var k = 0; k < 50; k++) check(sum(ps), 190, "monomorphic");

// A method the site never saw.
var mixed = ps.slice();
mixed[5] = { x: 3, get: function () { return 1000; } };
check(sum(mixed), 190 - 5 + 1000, "an unseen method");

// A replaced prototype method.
var old = P.prototype.get;
P.prototype.get = function () { return 1; };
check(sum(ps), 20, "replaced method");
P.prototype.get = old;
check(sum(ps), 190, "restored method");

// Not callable: a TypeError from baseline.
var bad = ps.slice();
bad[3] = { get: 5 };
var threw = false;
try { sum(bad); } catch (e) { threw = e instanceof TypeError; }
check(threw, true, "not callable");

// A function value called directly, the predicted one or another.
function twice(f, x) { return f(f(x)); }
function inc(x) { return x + 1; }
for (var k = 0; k < 50; k++) check(twice(inc, k), k + 2, "twice inc");
check(twice(function (x) { return x * 3; }, 2), 18, "twice another");
