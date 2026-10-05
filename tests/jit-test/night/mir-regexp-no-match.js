// An exec/test that does not match, decided in MIR: the regexp arm runs the
// AOT matcher itself where the leaf armed the regexp's shape and its shared's
// row, the prototype's fuse is intact, `lastIndex` is a number and the
// subject is linear. A failed match changes nothing, so its answer is final;
// everything else is the leaf's or the engine's. Each case below is one the
// arm must hand back.

var re = /["'&<>]/;
function find(s) { return re.exec(s); }
function has(s) { return re.test(s); }

var long = "plain text without any special characters, long enough to be out of line";
var two = "中文 text with no specials";
function rope(i) { return long.slice(0, 20 + (i & 1)) + long.slice(20 + (i & 1)); }

for (var i = 0; i < 200; i++) {
  assertEq(find("abc"), null);
  assertEq(has("abc"), false);
  assertEq(find(long), null);
  assertEq(has(two), false);
  assertEq(has(rope(i)), false);
  assertEq(has(rope(i) + "<"), true);
  assertEq(has(long.slice(0, 30) + "&" + long.slice(30)), true);
  var m = find("a<b");
  assertEq(m.index, 1);
  assertEq(m[0], "<");
  assertEq(has("x&y"), true);
  assertEq(has("中<"), true);
  if (i % 50 == 0) gc();
}

// A failed match leaves the statics as the last match set them.
assertEq(has("q'r"), true);
assertEq(RegExp.lastMatch, "'");
assertEq(has("nothing here"), false);
assertEq(RegExp.lastMatch, "'");

// lastIndex an object: reading it runs valueOf (the arm hands it back).
var calls = 0;
re.lastIndex = { valueOf() { calls++; return 0; } };
for (var i = 0; i < 10; i++) assertEq(has("abc"), false);
assertEq(calls, 10);
re.lastIndex = 0;

// An own property: another shape, not the optimizable one.
var re2 = /z+z/;
re2.extra = 1;
function has2(s) { return re2.test(s); }
for (var i = 0; i < 50; i++) { assertEq(has2("abc"), false); assertEq(has2("azzb"), true); }

// An own `exec` on a regexp armed while it had none: test() calls it (the
// object's shape is no longer the optimizable one).
var re4 = /q[0-9]/;
function has4(s) { return re4.test(s); }
for (var i = 0; i < 50; i++) assertEq(has4("abc"), false);
var ownCalls = 0;
re4.exec = function (s) { ownCalls++; return null; };
for (var i = 0; i < 10; i++) assertEq(has4("abc"), false);
assertEq(ownCalls, 10);

// compile() gives the object another shared (and pattern).
var re3 = /a+b/;
function find3(s) { return re3.exec(s); }
for (var i = 0; i < 50; i++) assertEq(find3("xyz"), null);
re3.compile("x");
for (var i = 0; i < 50; i++) assertEq(find3("xyz")[0], "x");

// Global: lastIndex moves, so never decided by the arm.
var rg = /[0-9]/g;
function nextDigit(s) { return rg.exec(s); }
var s = "a1b2";
assertEq(nextDigit(s)[0], "1");
assertEq(rg.lastIndex, 2);
assertEq(nextDigit(s)[0], "2");
assertEq(nextDigit(s), null);
assertEq(rg.lastIndex, 0);

// More armed regexps than the arm has rows: shareds collide, and each must
// run its own matcher (a row names its shared), not its neighbour's.
function t0(s) { return /^w0$/.test(s); }
function t1(s) { return /^w1$/.test(s); }
function t2(s) { return /^w2$/.test(s); }
function t3(s) { return /^w3$/.test(s); }
function t4(s) { return /^w4$/.test(s); }
function t5(s) { return /^w5$/.test(s); }
function t6(s) { return /^w6$/.test(s); }
function t7(s) { return /^w7$/.test(s); }
function t8(s) { return /^w8$/.test(s); }
function t9(s) { return /^w9$/.test(s); }
function t10(s) { return /^w10$/.test(s); }
function t11(s) { return /^w11$/.test(s); }
function t12(s) { return /^w12$/.test(s); }
function t13(s) { return /^w13$/.test(s); }
function t14(s) { return /^w14$/.test(s); }
function t15(s) { return /^w15$/.test(s); }
function t16(s) { return /^w16$/.test(s); }
function t17(s) { return /^w17$/.test(s); }
function t18(s) { return /^w18$/.test(s); }
function t19(s) { return /^w19$/.test(s); }
function t20(s) { return /^w20$/.test(s); }
function t21(s) { return /^w21$/.test(s); }
function t22(s) { return /^w22$/.test(s); }
function t23(s) { return /^w23$/.test(s); }
function t24(s) { return /^w24$/.test(s); }
function t25(s) { return /^w25$/.test(s); }
function t26(s) { return /^w26$/.test(s); }
function t27(s) { return /^w27$/.test(s); }
function t28(s) { return /^w28$/.test(s); }
function t29(s) { return /^w29$/.test(s); }
function t30(s) { return /^w30$/.test(s); }
function t31(s) { return /^w31$/.test(s); }
function t32(s) { return /^w32$/.test(s); }
function t33(s) { return /^w33$/.test(s); }
function t34(s) { return /^w34$/.test(s); }
function t35(s) { return /^w35$/.test(s); }
function t36(s) { return /^w36$/.test(s); }
function t37(s) { return /^w37$/.test(s); }
function t38(s) { return /^w38$/.test(s); }
function t39(s) { return /^w39$/.test(s); }
function t40(s) { return /^w40$/.test(s); }
function t41(s) { return /^w41$/.test(s); }
function t42(s) { return /^w42$/.test(s); }
function t43(s) { return /^w43$/.test(s); }
function t44(s) { return /^w44$/.test(s); }
function t45(s) { return /^w45$/.test(s); }
function t46(s) { return /^w46$/.test(s); }
function t47(s) { return /^w47$/.test(s); }
function t48(s) { return /^w48$/.test(s); }
function t49(s) { return /^w49$/.test(s); }
function t50(s) { return /^w50$/.test(s); }
function t51(s) { return /^w51$/.test(s); }
function t52(s) { return /^w52$/.test(s); }
function t53(s) { return /^w53$/.test(s); }
function t54(s) { return /^w54$/.test(s); }
function t55(s) { return /^w55$/.test(s); }
function t56(s) { return /^w56$/.test(s); }
function t57(s) { return /^w57$/.test(s); }
function t58(s) { return /^w58$/.test(s); }
function t59(s) { return /^w59$/.test(s); }
function t60(s) { return /^w60$/.test(s); }
function t61(s) { return /^w61$/.test(s); }
function t62(s) { return /^w62$/.test(s); }
function t63(s) { return /^w63$/.test(s); }
function t64(s) { return /^w64$/.test(s); }
function t65(s) { return /^w65$/.test(s); }
function t66(s) { return /^w66$/.test(s); }
function t67(s) { return /^w67$/.test(s); }
function t68(s) { return /^w68$/.test(s); }
function t69(s) { return /^w69$/.test(s); }
function t70(s) { return /^w70$/.test(s); }
function t71(s) { return /^w71$/.test(s); }
function t72(s) { return /^w72$/.test(s); }
function t73(s) { return /^w73$/.test(s); }
function t74(s) { return /^w74$/.test(s); }
function t75(s) { return /^w75$/.test(s); }
function t76(s) { return /^w76$/.test(s); }
function t77(s) { return /^w77$/.test(s); }
function t78(s) { return /^w78$/.test(s); }
function t79(s) { return /^w79$/.test(s); }
var ts = [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, t76, t77, t78, t79];
for (var r = 0; r < 3; r++) {
  for (var k = 0; k < ts.length; k++) {
    for (var j = 0; j < ts.length; j++) assertEq(ts[k]("w" + j), j == k);
  }
}

// Last: RegExp.prototype.exec replaced (the fuse pops): test() calls it.
var seen = 0;
var origExec = RegExp.prototype.exec;
RegExp.prototype.exec = function (s) { seen++; return origExec.call(this, s); };
for (var i = 0; i < 20; i++) assertEq(has("abc"), false);
assertEq(seen, 20);
