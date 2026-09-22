// A function's `name` is resolved lazily. A property cache populated by a
// function whose own `name` was deleted (same shape as an unresolved one)
// must not serve Function.prototype.name to a fresh function.
function sloppy(f) { var name = f.name; delete f.name; return [name, f.name]; }
function strictRead(f) { "use strict"; return f.name; }
assertEq(sloppy(function f() {}).join(","), "f,");
assertEq(strictRead(function f() {}), "f");
assertEq(strictRead(function g() {}), "g");
