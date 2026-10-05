// MIR's closure-variable loads and stores (`env.load`/`env.store`) in
// environments wider than an object's fixed slots: an environment holds
// its first MAX_FIXED_SLOTS (16) slots inline and the rest in its dynamic
// slots, and MIR addresses each statically by its slot number. Each
// function below closes over n bindings (a CallObject's bindings start at
// slot 2), so they straddle the boundary; inner closures write and read
// every one, through one and two hops, across GCs, and a block scope in a
// loop does the same with `let`s. A direct eval in the scope reads and
// writes the same bindings through the engine's own lookup, so a slot MIR
// misplaces shows even where MIR's reads and writes agree with each other.

function wide13() {
  var v0 = 0;
  var v1 = 1;
  var v2 = 2;
  var v3 = 3;
  var v4 = 4;
  var v5 = 5;
  var v6 = 6;
  var v7 = 7;
  var v8 = 8;
  var v9 = 9;
  var v10 = 10;
  var v11 = 11;
  var v12 = 12;
  function write(k) {
    for (var r = 0; r < 2; r++) {
      v0 = v0 * 3 + k + 0;
      v1 = v1 * 3 + k + 1;
      v2 = v2 * 3 + k + 2;
      v3 = v3 * 3 + k + 3;
      v4 = v4 * 3 + k + 4;
      v5 = v5 * 3 + k + 5;
      v6 = v6 * 3 + k + 6;
      v7 = v7 * 3 + k + 7;
      v8 = v8 * 3 + k + 8;
      v9 = v9 * 3 + k + 9;
      v10 = v10 * 3 + k + 10;
      v11 = v11 * 3 + k + 11;
      v12 = v12 * 3 + k + 12;
    }
  }
  function read() { return v0 * 1 + v1 * 2 + v2 * 3 + v3 * 4 + v4 * 5 + v5 * 6 + v6 * 7 + v7 * 8 + v8 * 9 + v9 * 10 + v10 * 11 + v11 * 12 + v12 * 13; }
  function twoHops() { return function () { v12 = v12 + 1; return read(); }; }
  function peek(i) { return eval("v" + i); }
  function poke(i, x) { eval("v" + i + " = " + x); }
  return { write, read, bump: twoHops(), peek, poke };
}
function check13() {
  var o = wide13();
  var expect = [];
  for (var i = 0; i < 13; i++) expect.push(i);
  for (var round = 0; round < 30; round++) {
    o.write(round);
    for (var i = 0; i < 13; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 + round + i;
    if (round % 10 == 0) gc();
    var want = 0;
    for (var i = 0; i < 13; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 13; i++) assertEq(o.peek(i), expect[i]);
    for (var i = 0; i < 13; i++) { o.poke(i, 7 * i + 1); expect[i] = 7 * i + 1; }
    want = 0;
    for (var i = 0; i < 13; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 13; i++) expect[i] = expect[i] % 1000;
    o.write(-1);
    for (var i = 0; i < 13; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 - 1 + i;
    // Keep the numbers small: reset through the closures.
    o = wide13();
    expect = [];
    for (var i = 0; i < 13; i++) expect.push(i);
    var b = o.bump();
    want = 0;
    for (var i = 0; i < 13; i++) want += (i == 12 ? i + 1 : i) * (i + 1);
    assertEq(b, want);
    o = wide13();
  }
}
for (var t = 0; t < 3; t++) check13();

function wide14() {
  var v0 = 0;
  var v1 = 1;
  var v2 = 2;
  var v3 = 3;
  var v4 = 4;
  var v5 = 5;
  var v6 = 6;
  var v7 = 7;
  var v8 = 8;
  var v9 = 9;
  var v10 = 10;
  var v11 = 11;
  var v12 = 12;
  var v13 = 13;
  function write(k) {
    for (var r = 0; r < 2; r++) {
      v0 = v0 * 3 + k + 0;
      v1 = v1 * 3 + k + 1;
      v2 = v2 * 3 + k + 2;
      v3 = v3 * 3 + k + 3;
      v4 = v4 * 3 + k + 4;
      v5 = v5 * 3 + k + 5;
      v6 = v6 * 3 + k + 6;
      v7 = v7 * 3 + k + 7;
      v8 = v8 * 3 + k + 8;
      v9 = v9 * 3 + k + 9;
      v10 = v10 * 3 + k + 10;
      v11 = v11 * 3 + k + 11;
      v12 = v12 * 3 + k + 12;
      v13 = v13 * 3 + k + 13;
    }
  }
  function read() { return v0 * 1 + v1 * 2 + v2 * 3 + v3 * 4 + v4 * 5 + v5 * 6 + v6 * 7 + v7 * 8 + v8 * 9 + v9 * 10 + v10 * 11 + v11 * 12 + v12 * 13 + v13 * 14; }
  function twoHops() { return function () { v13 = v13 + 1; return read(); }; }
  function peek(i) { return eval("v" + i); }
  function poke(i, x) { eval("v" + i + " = " + x); }
  return { write, read, bump: twoHops(), peek, poke };
}
function check14() {
  var o = wide14();
  var expect = [];
  for (var i = 0; i < 14; i++) expect.push(i);
  for (var round = 0; round < 30; round++) {
    o.write(round);
    for (var i = 0; i < 14; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 + round + i;
    if (round % 10 == 0) gc();
    var want = 0;
    for (var i = 0; i < 14; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 14; i++) assertEq(o.peek(i), expect[i]);
    for (var i = 0; i < 14; i++) { o.poke(i, 7 * i + 1); expect[i] = 7 * i + 1; }
    want = 0;
    for (var i = 0; i < 14; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 14; i++) expect[i] = expect[i] % 1000;
    o.write(-1);
    for (var i = 0; i < 14; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 - 1 + i;
    // Keep the numbers small: reset through the closures.
    o = wide14();
    expect = [];
    for (var i = 0; i < 14; i++) expect.push(i);
    var b = o.bump();
    want = 0;
    for (var i = 0; i < 14; i++) want += (i == 13 ? i + 1 : i) * (i + 1);
    assertEq(b, want);
    o = wide14();
  }
}
for (var t = 0; t < 3; t++) check14();

function wide15() {
  var v0 = 0;
  var v1 = 1;
  var v2 = 2;
  var v3 = 3;
  var v4 = 4;
  var v5 = 5;
  var v6 = 6;
  var v7 = 7;
  var v8 = 8;
  var v9 = 9;
  var v10 = 10;
  var v11 = 11;
  var v12 = 12;
  var v13 = 13;
  var v14 = 14;
  function write(k) {
    for (var r = 0; r < 2; r++) {
      v0 = v0 * 3 + k + 0;
      v1 = v1 * 3 + k + 1;
      v2 = v2 * 3 + k + 2;
      v3 = v3 * 3 + k + 3;
      v4 = v4 * 3 + k + 4;
      v5 = v5 * 3 + k + 5;
      v6 = v6 * 3 + k + 6;
      v7 = v7 * 3 + k + 7;
      v8 = v8 * 3 + k + 8;
      v9 = v9 * 3 + k + 9;
      v10 = v10 * 3 + k + 10;
      v11 = v11 * 3 + k + 11;
      v12 = v12 * 3 + k + 12;
      v13 = v13 * 3 + k + 13;
      v14 = v14 * 3 + k + 14;
    }
  }
  function read() { return v0 * 1 + v1 * 2 + v2 * 3 + v3 * 4 + v4 * 5 + v5 * 6 + v6 * 7 + v7 * 8 + v8 * 9 + v9 * 10 + v10 * 11 + v11 * 12 + v12 * 13 + v13 * 14 + v14 * 15; }
  function twoHops() { return function () { v14 = v14 + 1; return read(); }; }
  function peek(i) { return eval("v" + i); }
  function poke(i, x) { eval("v" + i + " = " + x); }
  return { write, read, bump: twoHops(), peek, poke };
}
function check15() {
  var o = wide15();
  var expect = [];
  for (var i = 0; i < 15; i++) expect.push(i);
  for (var round = 0; round < 30; round++) {
    o.write(round);
    for (var i = 0; i < 15; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 + round + i;
    if (round % 10 == 0) gc();
    var want = 0;
    for (var i = 0; i < 15; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 15; i++) assertEq(o.peek(i), expect[i]);
    for (var i = 0; i < 15; i++) { o.poke(i, 7 * i + 1); expect[i] = 7 * i + 1; }
    want = 0;
    for (var i = 0; i < 15; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 15; i++) expect[i] = expect[i] % 1000;
    o.write(-1);
    for (var i = 0; i < 15; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 - 1 + i;
    // Keep the numbers small: reset through the closures.
    o = wide15();
    expect = [];
    for (var i = 0; i < 15; i++) expect.push(i);
    var b = o.bump();
    want = 0;
    for (var i = 0; i < 15; i++) want += (i == 14 ? i + 1 : i) * (i + 1);
    assertEq(b, want);
    o = wide15();
  }
}
for (var t = 0; t < 3; t++) check15();

function wide16() {
  var v0 = 0;
  var v1 = 1;
  var v2 = 2;
  var v3 = 3;
  var v4 = 4;
  var v5 = 5;
  var v6 = 6;
  var v7 = 7;
  var v8 = 8;
  var v9 = 9;
  var v10 = 10;
  var v11 = 11;
  var v12 = 12;
  var v13 = 13;
  var v14 = 14;
  var v15 = 15;
  function write(k) {
    for (var r = 0; r < 2; r++) {
      v0 = v0 * 3 + k + 0;
      v1 = v1 * 3 + k + 1;
      v2 = v2 * 3 + k + 2;
      v3 = v3 * 3 + k + 3;
      v4 = v4 * 3 + k + 4;
      v5 = v5 * 3 + k + 5;
      v6 = v6 * 3 + k + 6;
      v7 = v7 * 3 + k + 7;
      v8 = v8 * 3 + k + 8;
      v9 = v9 * 3 + k + 9;
      v10 = v10 * 3 + k + 10;
      v11 = v11 * 3 + k + 11;
      v12 = v12 * 3 + k + 12;
      v13 = v13 * 3 + k + 13;
      v14 = v14 * 3 + k + 14;
      v15 = v15 * 3 + k + 15;
    }
  }
  function read() { return v0 * 1 + v1 * 2 + v2 * 3 + v3 * 4 + v4 * 5 + v5 * 6 + v6 * 7 + v7 * 8 + v8 * 9 + v9 * 10 + v10 * 11 + v11 * 12 + v12 * 13 + v13 * 14 + v14 * 15 + v15 * 16; }
  function twoHops() { return function () { v15 = v15 + 1; return read(); }; }
  function peek(i) { return eval("v" + i); }
  function poke(i, x) { eval("v" + i + " = " + x); }
  return { write, read, bump: twoHops(), peek, poke };
}
function check16() {
  var o = wide16();
  var expect = [];
  for (var i = 0; i < 16; i++) expect.push(i);
  for (var round = 0; round < 30; round++) {
    o.write(round);
    for (var i = 0; i < 16; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 + round + i;
    if (round % 10 == 0) gc();
    var want = 0;
    for (var i = 0; i < 16; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 16; i++) assertEq(o.peek(i), expect[i]);
    for (var i = 0; i < 16; i++) { o.poke(i, 7 * i + 1); expect[i] = 7 * i + 1; }
    want = 0;
    for (var i = 0; i < 16; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 16; i++) expect[i] = expect[i] % 1000;
    o.write(-1);
    for (var i = 0; i < 16; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 - 1 + i;
    // Keep the numbers small: reset through the closures.
    o = wide16();
    expect = [];
    for (var i = 0; i < 16; i++) expect.push(i);
    var b = o.bump();
    want = 0;
    for (var i = 0; i < 16; i++) want += (i == 15 ? i + 1 : i) * (i + 1);
    assertEq(b, want);
    o = wide16();
  }
}
for (var t = 0; t < 3; t++) check16();

function wide40() {
  var v0 = 0;
  var v1 = 1;
  var v2 = 2;
  var v3 = 3;
  var v4 = 4;
  var v5 = 5;
  var v6 = 6;
  var v7 = 7;
  var v8 = 8;
  var v9 = 9;
  var v10 = 10;
  var v11 = 11;
  var v12 = 12;
  var v13 = 13;
  var v14 = 14;
  var v15 = 15;
  var v16 = 16;
  var v17 = 17;
  var v18 = 18;
  var v19 = 19;
  var v20 = 20;
  var v21 = 21;
  var v22 = 22;
  var v23 = 23;
  var v24 = 24;
  var v25 = 25;
  var v26 = 26;
  var v27 = 27;
  var v28 = 28;
  var v29 = 29;
  var v30 = 30;
  var v31 = 31;
  var v32 = 32;
  var v33 = 33;
  var v34 = 34;
  var v35 = 35;
  var v36 = 36;
  var v37 = 37;
  var v38 = 38;
  var v39 = 39;
  function write(k) {
    for (var r = 0; r < 2; r++) {
      v0 = v0 * 3 + k + 0;
      v1 = v1 * 3 + k + 1;
      v2 = v2 * 3 + k + 2;
      v3 = v3 * 3 + k + 3;
      v4 = v4 * 3 + k + 4;
      v5 = v5 * 3 + k + 5;
      v6 = v6 * 3 + k + 6;
      v7 = v7 * 3 + k + 7;
      v8 = v8 * 3 + k + 8;
      v9 = v9 * 3 + k + 9;
      v10 = v10 * 3 + k + 10;
      v11 = v11 * 3 + k + 11;
      v12 = v12 * 3 + k + 12;
      v13 = v13 * 3 + k + 13;
      v14 = v14 * 3 + k + 14;
      v15 = v15 * 3 + k + 15;
      v16 = v16 * 3 + k + 16;
      v17 = v17 * 3 + k + 17;
      v18 = v18 * 3 + k + 18;
      v19 = v19 * 3 + k + 19;
      v20 = v20 * 3 + k + 20;
      v21 = v21 * 3 + k + 21;
      v22 = v22 * 3 + k + 22;
      v23 = v23 * 3 + k + 23;
      v24 = v24 * 3 + k + 24;
      v25 = v25 * 3 + k + 25;
      v26 = v26 * 3 + k + 26;
      v27 = v27 * 3 + k + 27;
      v28 = v28 * 3 + k + 28;
      v29 = v29 * 3 + k + 29;
      v30 = v30 * 3 + k + 30;
      v31 = v31 * 3 + k + 31;
      v32 = v32 * 3 + k + 32;
      v33 = v33 * 3 + k + 33;
      v34 = v34 * 3 + k + 34;
      v35 = v35 * 3 + k + 35;
      v36 = v36 * 3 + k + 36;
      v37 = v37 * 3 + k + 37;
      v38 = v38 * 3 + k + 38;
      v39 = v39 * 3 + k + 39;
    }
  }
  function read() { return v0 * 1 + v1 * 2 + v2 * 3 + v3 * 4 + v4 * 5 + v5 * 6 + v6 * 7 + v7 * 8 + v8 * 9 + v9 * 10 + v10 * 11 + v11 * 12 + v12 * 13 + v13 * 14 + v14 * 15 + v15 * 16 + v16 * 17 + v17 * 18 + v18 * 19 + v19 * 20 + v20 * 21 + v21 * 22 + v22 * 23 + v23 * 24 + v24 * 25 + v25 * 26 + v26 * 27 + v27 * 28 + v28 * 29 + v29 * 30 + v30 * 31 + v31 * 32 + v32 * 33 + v33 * 34 + v34 * 35 + v35 * 36 + v36 * 37 + v37 * 38 + v38 * 39 + v39 * 40; }
  function twoHops() { return function () { v39 = v39 + 1; return read(); }; }
  function peek(i) { return eval("v" + i); }
  function poke(i, x) { eval("v" + i + " = " + x); }
  return { write, read, bump: twoHops(), peek, poke };
}
function check40() {
  var o = wide40();
  var expect = [];
  for (var i = 0; i < 40; i++) expect.push(i);
  for (var round = 0; round < 30; round++) {
    o.write(round);
    for (var i = 0; i < 40; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 + round + i;
    if (round % 10 == 0) gc();
    var want = 0;
    for (var i = 0; i < 40; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 40; i++) assertEq(o.peek(i), expect[i]);
    for (var i = 0; i < 40; i++) { o.poke(i, 7 * i + 1); expect[i] = 7 * i + 1; }
    want = 0;
    for (var i = 0; i < 40; i++) want += expect[i] * (i + 1);
    assertEq(o.read(), want);
    for (var i = 0; i < 40; i++) expect[i] = expect[i] % 1000;
    o.write(-1);
    for (var i = 0; i < 40; i++) for (var r = 0; r < 2; r++) expect[i] = expect[i] * 3 - 1 + i;
    // Keep the numbers small: reset through the closures.
    o = wide40();
    expect = [];
    for (var i = 0; i < 40; i++) expect.push(i);
    var b = o.bump();
    want = 0;
    for (var i = 0; i < 40; i++) want += (i == 39 ? i + 1 : i) * (i + 1);
    assertEq(b, want);
    o = wide40();
  }
}
for (var t = 0; t < 3; t++) check40();

function blocks() {
  var fs = [];
  for (var i = 0; i < 10; i++) {
    let b0 = i * 1 + 0;
    let b1 = i * 2 + 1;
    let b2 = i * 3 + 2;
    let b3 = i * 4 + 3;
    let b4 = i * 5 + 4;
    let b5 = i * 6 + 5;
    let b6 = i * 7 + 6;
    let b7 = i * 8 + 7;
    let b8 = i * 9 + 8;
    let b9 = i * 10 + 9;
    let b10 = i * 11 + 10;
    let b11 = i * 12 + 11;
    let b12 = i * 13 + 12;
    let b13 = i * 14 + 13;
    let b14 = i * 15 + 14;
    let b15 = i * 16 + 15;
    let b16 = i * 17 + 16;
    let b17 = i * 18 + 17;
    let b18 = i * 19 + 18;
    let b19 = i * 20 + 19;
    fs.push(function () {
      b0 += 1;
      b1 += 1;
      b2 += 1;
      b3 += 1;
      b4 += 1;
      b5 += 1;
      b6 += 1;
      b7 += 1;
      b8 += 1;
      b9 += 1;
      b10 += 1;
      b11 += 1;
      b12 += 1;
      b13 += 1;
      b14 += 1;
      b15 += 1;
      b16 += 1;
      b17 += 1;
      b18 += 1;
      b19 += 1;
      return b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14 + b15 + b16 + b17 + b18 + b19;
    });
  }
  var t = 0;
  for (var j = 0; j < 10; j++) t += fs[j]() + fs[j]();
  return t;
}
function blocksWant() {
  var t = 0;
  for (var i = 0; i < 10; i++) {
    var s = 0;
    for (var k = 0; k < 20; k++) s += i * (k + 1) + k;
    t += (s + 20) + (s + 40);
  }
  return t;
}
for (var t = 0; t < 40; t++) {
  assertEq(blocks(), blocksWant());
  if (t % 10 == 0) gc();
}
