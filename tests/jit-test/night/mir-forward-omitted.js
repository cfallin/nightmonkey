// A constructor that forwards its `arguments` to an initializer
// (`this.init.apply(this, arguments)`, the Class.create idiom): the
// initializer's formals get as few actuals as the constructor does, so
// one a `new` leaves out reads `undefined` whatever the other calls pass.
// Such a formal takes no entry claim; its default (`if (x === undefined)
// x = 0`) and its uses still see the numbers.
//
// The analysis's half of this is only guarded: a formal wrongly claimed at
// entry exits on every call that leaves it out (box2d's b2Vec2, ~190k
// exits a run) and runs correctly in baseline. The results below hold
// either way; the exit census is what sees the difference.

function Vec() { this.init.apply(this, arguments); }
Vec.prototype.init = function (x, y) {
  if (x === undefined) x = 0;
  if (y === undefined) y = 0;
  this.x = x;
  this.y = y;
};
Vec.prototype.len2 = function () { return this.x * this.x + this.y * this.y; };

// A second level of forwarding: the outer wrapper's actuals reach `init`.
function Outer() { Vec.apply(this, arguments); }
Outer.prototype = Object.create(Vec.prototype);

function run(n) {
  var t = 0;
  for (var i = 0; i < n; i++) {
    t += new Vec(i, 1).len2();
    t += new Vec().len2();
    t += new Vec(2).len2();
    t += new Vec(0.5, i).len2();
    t += new Outer().len2() + new Outer(3, 4).len2();
  }
  return t;
}
function want(n) {
  var t = 0;
  for (var i = 0; i < n; i++) t += (i * i + 1) + 0 + 4 + (0.25 + i * i) + 0 + 25;
  return t;
}
for (var r = 0; r < 20; r++) assertEq(run(100), want(100));
