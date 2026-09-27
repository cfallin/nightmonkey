// MIR's `T.apply(this, arguments)` forwarding (`--pipeline mir`): the
// arguments object is not made; the target runs inlined with its formals
// read from the frame's actuals, or through the runtime's forward. Any exit
// while the object is elided (the `arguments` local, the stack) must make
// it first. Run under `--mir-stress` too.
var arr1 = [];
var arr2 = [];
for (let i = 0; i < 10; i++) {
    arr1.push(function f(x) { return "" + x + ":" + i; });
    arr2.push(function () { return arr1[i].apply(null, arguments); });
}
for (var k = 0; k < 200; k++)
    for (var j = 0; j < 10; j++) assertEq(arr2[j].call(null, k), k + ":" + j);

function g() { return arguments.length; }
function F2() {
    var sum = 0;
    for (let i = 0; i < 1000; i++) sum += g.apply(null, arguments);
    return sum;
}
assertEq(F2(1, 2, 3), 3000);
var a = [];
for (var i = 0; i < 374; i++) a.push(i);
assertEq(F2.apply(null, a), 374000);

// The prototype.js constructor wrapper, polymorphic across classes.
function makeClass() { return function () { this.initialize.apply(this, arguments); }; }
var P = makeClass();
P.prototype.initialize = function (x, y) { this.x = x; this.y = y; };
var Q = makeClass();
Q.prototype.initialize = function (a) { this.a = a; };
function build(n) {
    var t = 0;
    for (var i = 0; i < n; i++) { var p = new P(i, 2); var q = new Q(i); t += p.x + p.y + q.a; }
    return t;
}
assertEq(build(300), 2 * 44850 + 600);
// A non-builtin `.apply`, and a target that is not a function.
P.prototype.initialize.apply = function () { return 7; };
var weird = { initialize: { apply: function (t, args) { return args.length; } } };
function fwd() { return weird.initialize.apply(this, arguments); }
for (var i = 0; i < 20; i++) assertEq(fwd(1, 2), 2);
