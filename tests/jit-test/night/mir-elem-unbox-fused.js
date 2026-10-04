// `load_elem` followed by an unbox guard of the element (`lower.rs`'s
// `load_elem_unboxed`) tests the tag the guard wants first and takes the
// guard's `ok` edge directly; any other element goes the unfused way: a
// hole to the load's own `fail` (a generic read, which finds the
// prototype chain's element), anything else to the guard, which misses.
// A number unbox (`guard.unbox.f64num`) takes a double's bits and converts
// an int32.

function sumInts(a, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s = (s + (a[i] | 0)) | 0;
  return s;
}
function sumNums(a, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s = s + a[i] * 0.5;
  return s;
}
function firstFields(a, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s = (s + a[i].v) | 0;
  return s;
}

var ints = [];
var nums = [];
var objs = [];
for (var i = 0; i < 64; i++) {
  ints.push(i * 3);
  nums.push(i % 3 == 0 ? i : i + 0.25);
  objs.push({ v: i });
}
function expectInts(a, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s = (s + (a[i] | 0)) | 0;
  return s;
}
function expectNums(a, n) {
  var s = 0;
  for (var i = 0; i < n; i++) s = s + a[i] * 0.5;
  return s;
}

for (var r = 0; r < 300; r++) {
  if (r % 97 == 0) gc();
  assertEq(sumInts(ints, 64), 6048);
  assertEq(sumNums(nums, 64), expectNums(nums, 64));
  assertEq(firstFields(objs, 64), 2016);
}

// Holes whose reads find the prototype's element: the hole must reach the
// load's generic read, not the guard (whose exit would resume with the
// hole itself).
var holey = ints.slice();
delete holey[5];
delete holey[40];
var proto = [];
proto[5] = 1000;
proto[40] = 2000;
Object.setPrototypeOf(holey, proto);
for (var r = 0; r < 50; r++) {
  assertEq(sumInts(holey, 64), 6048 - 15 - 120 + 3000);
}
var holeyNums = nums.slice();
delete holeyNums[7];
Object.setPrototypeOf(holeyNums, proto);
proto[7] = 4.5;
for (var r = 0; r < 50; r++) {
  assertEq(sumNums(holeyNums, 64), expectNums(nums, 64) - nums[7] * 0.5 + 2.25);
}
// A hole with nothing behind it reads undefined: NaN for the numbers.
var bare = nums.slice();
delete bare[9];
for (var r = 0; r < 20; r++) assertEq(sumNums(bare, 64), NaN);

// Elements of another type than the loop's: the guard misses and the
// generic path converts.
var mixed = ints.slice();
mixed[10] = "7";
mixed[11] = 2.75;
mixed[12] = true;
mixed[13] = null;
for (var r = 0; r < 50; r++) {
  assertEq(sumInts(mixed, 64), expectInts(mixed, 64));
}
var mixedNums = nums.slice();
mixedNums[20] = "8";
mixedNums[21] = undefined;
for (var r = 0; r < 20; r++) assertEq(sumNums(mixedNums, 22), expectNums(mixedNums, 22));
var mixedObjs = objs.slice();
mixedObjs[3] = "str";
var wantObjs = 0;
for (var i = 0; i < 64; i++) wantObjs = (wantObjs + mixedObjs[i].v) | 0;
for (var r = 0; r < 20; r++) assertEq(firstFields(mixedObjs, 64), wantObjs);

// Int32 elements among doubles convert exactly, at the extremes too.
var extremes = [2147483647, -2147483648, 0, -0, 1.5, -1, 0.1];
var want = 0;
for (var i = 0; i < extremes.length; i++) want = want + extremes[i] * 0.5;
for (var r = 0; r < 200; r++) assertEq(sumNums(extremes, extremes.length), want);

// Past the initialized length: the load's own fail.
for (var r = 0; r < 20; r++) assertEq(sumNums(nums, 70), NaN);
