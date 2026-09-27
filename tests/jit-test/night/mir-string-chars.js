// MIR's string char arms: `s.charCodeAt(i)`/`s.charAt(i)` read from
// String.prototype's cached natives and load the char of a linear string
// inline; `String.fromCharCode(c < 256)` is a static unit string; array,
// string and arguments `.length` inline. Ropes, two-byte chars above 255,
// out-of-bounds indices and monkeypatched natives take the generic path.
function codes(s) { var t = 0; for (var i = 0; i < s.length; i++) t = (t * 31 + s.charCodeAt(i)) | 0; return t; }
function chars(s) { var r = ""; for (var i = 0; i < s.length; i++) r += s.charAt(i); return r; }
function fcc(n) { var r = ""; for (var i = 0; i < n; i++) r += String.fromCharCode(65 + (i % 26)); return r; }
function argl() { return arguments.length; }
function argl2() { arguments.length = 7; return arguments.length; }
var lat = "hello world, abcdefghijklmnop";
var two = "héllo 世界";
var rope = lat + two + lat;
var want = 0;
for (var i = 0; i < lat.length; i++) want = (want * 31 + lat.charCodeAt(i)) | 0;
for (var n = 0; n < 60; n++) {
  assertEq(codes(lat), want);
  assertEq(chars(lat), lat);
  assertEq(chars(two), two);
  assertEq(chars(rope), rope);
  assertEq(fcc(30), "ABCDEFGHIJKLMNOPQRSTUVWXYZABCD");
  assertEq(argl(1, 2, 3), 3);
  assertEq(argl2(1), 7);
  assertEq([1, 2, 3].length, 3);
}
assertEq(lat.charCodeAt(99), NaN);
assertEq(lat.charAt(99), "");
assertEq(two.charCodeAt(6), 0x4e16);
assertEq(String.fromCharCode(0x4e16), "世");
String.prototype.charCodeAt = function () { return 1; };
assertEq(codes("ab"), 32);                        // the patched method
