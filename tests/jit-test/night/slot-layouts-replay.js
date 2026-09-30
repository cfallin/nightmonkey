// Add transitions under analysis-chosen slot layouts, replayed from the
// runtime's caches: splay's insert adds `left` then `right` on one branch
// and `right` then `left` on the other, so half the nodes take a transition
// that skips a slot (a hole the replay must initialize, since the GC traces
// the whole span) and then one that fills it. Values, property order and GC
// safety must hold for every node, in every order.

function assertEq(a, b, msg) {
  if (a !== b) {
    throw new Error((msg || "") + ": got " + String(a) + ", expected " + String(b));
  }
}

function Node(key, value) {
  this.key = key;
  this.value = value;
}
Node.prototype.left = null;
Node.prototype.right = null;

// As splay's insert: the adds follow the construction, on a local.
function make(i, a, b) {
  var node = new Node(i, "v" + i);
  if (i & 1) {
    node.left = a;
    node.right = b;
  } else {
    node.right = b;
    // A GC while the skipped slot is a hole: it must hold a valid value.
    if (i % 50 === 0) {
      minorgc();
    }
    node.left = a;
  }
  return node;
}

function run(n) {
  var nodes = [];
  var junk = [];
  for (var i = 0; i < n; i++) {
    // Garbage between allocations, so a skipped slot left uninitialized
    // would hold a stale pointer.
    junk.push({ i: i, s: "junk" + i, o: { p: junk } });
    var node = make(i, { l: i }, { r: i });
    nodes.push(node);
    if (i % 1000 === 0) {
      junk = [];
      minorgc();
    }
  }
  gc();
  var sum = 0;
  for (var i = 0; i < n; i++) {
    var node = nodes[i];
    assertEq(node.key, i, "key");
    assertEq(node.value, "v" + i, "value");
    sum += node.left.l + node.right.r;
    assertEq(Object.keys(node).join(","), i & 1 ? "key,value,left,right" : "key,value,right,left", "order " + i);
  }
  assertEq(sum, n * (n - 1), "sum");
}
run(5000);
run(5000);
