// `length` as typed ops in MIR (§7): a proven string's length word, and
// an array's (behind `guard.kind Array` and an int32 guard) where the
// builder has evidence the receiver is an array. Receivers that break the
// evidence (array-likes, strings where arrays were seen, sparse arrays
// whose length is past int32) must read the same values.

function sumArr(a) { var t = 0; for (var i = 0; i < a.length; i++) t += a[i]; return t; }
function lastOf(a) { return a[a.length - 1]; }
function strLen(s) { var n = 0; for (var i = 0; i < 10; i++) n += s.length; return n; }
function grow(a, n) { while (a.length < n) a.push(a.length); return a.length; }

var arr = [];
for (var i = 0; i < 100; i++) arr.push(i);
for (var r = 0; r < 300; r++) {
  assertEq(sumArr(arr), 4950);
  assertEq(lastOf(arr), 99);
  assertEq(strLen("ab" + r), 10 * ("ab" + r).length);
  assertEq(grow([], r % 20), r % 20);
  if (r % 50 == 49) {
    assertEq(sumArr({ length: 2, 0: 5, 1: 6 }), 11);
    assertEq(sumArr("123"), "0123");
    var sparse = [1, 2, 3];
    sparse.length = 4294967295;
    assertEq(lastOf(sparse), undefined);
    assertEq(sparse.length, 4294967295);
    assertEq(sumArr([1, , 3]), NaN);
  }
}
