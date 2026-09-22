// DefineDataProperty over an array whose index is a sparse non-writable
// property must redefine it, not add a dense element beside it.
var a = [1];
a.constructor = {};
a.constructor[Symbol.species] = function(len) {
  var q = new Array(0);
  Object.defineProperty(q, 0, {value: 0, writable: false, configurable: true, enumerable: false});
  return q;
};
var r = a.map(function() { return 2; });
assertEq(r[0], 2);
assertEq(Object.getOwnPropertyNames(r).join(","), "0,length");
assertEq(delete r[0], true);
assertEq(r.hasOwnProperty(0), false);
