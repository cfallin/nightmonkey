// Object literals are allocated with a fixed slot for each field of their
// layout row (up to the engine's 16), so a literal of more fields than the
// default object kind holds keeps its layout's slot predictions. Values,
// property order and later changes stay right, including literals wider
// than 16 fields and ones with accessors.

function assertEq(a, b, msg) {
  if (a !== b) {
    throw new Error((msg || "") + ": got " + String(a) + ", expected " + String(b));
  }
}

function five(i, s) {
  return { a: i, b: s, c: i * 2, d: (i & 1) === 0, e: i & 3 ? s : null };
}
function six(i) {
  return { $$typeof: 1, type: "div", key: i, ref: null, props: { i: i }, _owner: null };
}
function wide(i) {
  return {
    f0: i, f1: i + 1, f2: i + 2, f3: i + 3, f4: i + 4, f5: i + 5, f6: i + 6,
    f7: i + 7, f8: i + 8, f9: i + 9, f10: i + 10, f11: i + 11, f12: i + 12,
    f13: i + 13, f14: i + 14, f15: i + 15, f16: i + 16, f17: i + 17,
    f18: i + 18, f19: i + 19,
  };
}
function acc(i) {
  return { x: i, y: i + 1, z: i + 2, w: i + 3, get sum() { return this.x + this.y + this.z + this.w; }, v: i + 4 };
}

function run() {
  var total = 0;
  for (var i = 0; i < 3000; i++) {
    var o = five(i, "s");
    total += o.a + o.c + (o.d ? 1 : 0) + (o.e === null ? 0 : o.e.length);
    assertEq(Object.keys(o).join(","), "a,b,c,d,e", "five keys");
    var p = six(i);
    total += p.key + p.props.i + p.$$typeof;
    assertEq(Object.keys(p).join(","), "$$typeof,type,key,ref,props,_owner", "six keys");
    var w = wide(i);
    var ws = 0;
    for (var k = 0; k < 20; k++) ws += w["f" + k];
    assertEq(ws, 20 * i + 190, "wide sum " + i);
    assertEq(w.f19 - w.f0, 19, "wide ends");
    var q = acc(i);
    assertEq(q.sum, 4 * i + 6, "getter");
    assertEq(q.v, i + 4, "after getter");
    if (i % 7 === 0) {
      // Later adds and a delete on the wide literals.
      o.f = "late";
      p.extra = i;
      delete w.f3;
      assertEq(o.f + p.extra, "late" + i, "late adds");
      assertEq("f3" in w, false, "delete");
      assertEq(w.f4, i + 4, "after delete");
      assertEq(JSON.stringify(o), JSON.stringify({ a: i, b: "s", c: i * 2, d: (i & 1) === 0, e: i & 3 ? "s" : null, f: "late" }), "json");
    }
  }
  var want = 0;
  for (var i = 0; i < 3000; i++) {
    want += i + 2 * i + ((i & 1) === 0 ? 1 : 0) + (i & 3 ? 1 : 0) + i + i + 1;
  }
  assertEq(total, want, "total");
}
run();
gc();
run();
