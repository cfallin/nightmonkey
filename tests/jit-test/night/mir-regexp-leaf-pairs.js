// A successful exec() the compiled call's leaf decides hands its match pairs
// to the generic path that builds the result (the context's NightLeafMatch),
// which must use them only for the same regexp and input: every result here
// is checked against a match run with the leaf out of the way (a global
// regexp's exec, reset each time). Atoms (patterns with no metacharacters)
// take the same leaf and the collapsed matcher/searcher paths.

var res = [/b(a+)(c?)/, /a/, /(x)(y)?z/, /na/, /[0-9]+/, /hello/,
           /(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)(k)(l)(m)(n)(o)(p)(q)(r)/];
var refs = res.map(r => new RegExp(r.source, "g"));
var inputs = ["xbaaac", "banana", "xyz", "xz", "abc123def", "say hello", "nope",
              "abcdefghijklmnopqrstuvwxyz", "a", "bac", "2026"];
function ex(re, s) { return re.exec(s); }
function same(m, r, what) {
  if (r === null) { assertEq(m, null, what); return; }
  assertEq(m.length, r.length, what);
  assertEq(m.index, r.index, what);
  assertEq(m.input, r.input, what);
  for (var k = 0; k < r.length; k++) assertEq(m[k], r[k], what + " [" + k + "]");
}
for (var i = 0; i < 3000; i++) {
  if (i % 500 == 0) gc();
  if (i % 97 == 0) minorgc();
  var j = i % res.length, s = inputs[(i * 7) % inputs.length];
  // A rope, flattened by the leaf's linearity test or not at all.
  if (i % 5 == 0) s = s.slice(0, 2) + s.slice(2);
  var m = ex(res[j], s);
  refs[j].lastIndex = 0;
  same(m, refs[j].exec(s), res[j] + " on " + s);
  // Interleave a second, different exec between a leaf match and the next.
  var k = (j + 3) % res.length, t = inputs[(i * 3 + 1) % inputs.length];
  var m2 = ex(res[k], t);
  refs[k].lastIndex = 0;
  same(m2, refs[k].exec(t), res[k] + " on " + t);
}

// Atoms through replace / split / match / search (the searcher and
// matcher paths) and as the leaf's exec.
for (var i = 0; i < 500; i++) {
  assertEq("banana".replace(/na/g, "NA"), "baNANA");
  assertEq("a,b,,c".split(/,/).join("|"), "a|b||c");
  assertEq("banana".match(/an/g).length, 2);
  assertEq("banana".search(/nan/), 2);
  assertEq(/nan/.exec("banana").index, 2);
  assertEq(RegExp.lastMatch, "nan");
  assertEq(/zzz/.exec("banana"), null);
}
