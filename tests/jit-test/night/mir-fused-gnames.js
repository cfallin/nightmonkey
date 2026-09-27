// MIR's fused global reads (`--pipeline mir`): a top-level constant that
// nothing else writes reads as its literal while its fuse is armed, and a
// blown fuse sends the read back through baseline to the new value.
var K = 5;
var D = 1.5;
var B = true;
var N = null;
function useK(n) { let s = 0; for (let i = 0; i < n; i++) s += K; return s; }
function useD() { return D * 2; }
function useB() { return B ? 1 : 2; }
function useN() { return N === null; }
for (let i = 0; i < 50; i++) {
  assertEq(useK(10), 50);
  assertEq(useD(), 3);
  assertEq(useB(), 1);
  assertEq(useN(), true);
}
// A computed-key write the analysis cannot see blows the fuse.
globalThis["K"] = 7;
globalThis["D"] = "x";
globalThis["B"] = 0;
globalThis["N"] = 3;
for (let i = 0; i < 5; i++) {
  assertEq(useK(10), 70);
  assertEq(useD(), NaN);
  assertEq(useB(), 2);
  assertEq(useN(), false);
}
