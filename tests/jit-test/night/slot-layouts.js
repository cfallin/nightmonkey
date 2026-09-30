// Analysis-chosen slot layouts: a constructor whose paths write its fields
// in different orders, or skip some (pdfjs's Font), puts each field in its
// layout row's slot whatever the order. Values, the visible property order,
// methods reading the fields, later adds, deletes and generic consumers stay
// right on every path.

function assertEq(a, b, msg) {
  if (a !== b) {
    throw new Error((msg || "") + ": got " + String(a) + ", expected " + String(b));
  }
}

function Font(kind, n) {
  this.name = "f" + n;
  this.type = kind;
  if (kind === 0) {
    // Early return: the row's later fields stay holes.
    this.loadedName = "early" + n;
    this.loading = false;
    return;
  }
  this.widths = [n, n + 1];
  this.defaultWidth = n * 2;
  if (kind === 1) {
    this.encoding = "enc" + n;
    return;
  }
  this.loadedName = "main" + n;
  this.loading = true;
}
Font.prototype.width = function (i) {
  return this.widths === undefined ? -1 : this.widths[i] + this.defaultWidth;
};
Font.prototype.label = function () {
  return this.name + ":" + this.type + ":" + this.loadedName + ":" + this.loading;
};
Font.prototype.describe = function () {
  return Object.keys(this).join(",");
};

var expectKeys = [
  "name,type,loadedName,loading",
  "name,type,widths,defaultWidth,encoding",
  "name,type,widths,defaultWidth,loadedName,loading",
];

function run() {
  var fonts = [];
  for (var i = 0; i < 300; i++) {
    fonts.push(new Font(i % 3, i));
  }
  var sum = 0;
  for (var r = 0; r < 20; r++) {
    for (var i = 0; i < fonts.length; i++) {
      var f = fonts[i];
      var k = i % 3;
      sum += f.width(1);
      var label = f.label();
      if (k === 0) {
        assertEq(label, "f" + i + ":0:early" + i + ":false", "label0");
      } else if (k === 1) {
        assertEq(label, "f" + i + ":1:undefined:undefined", "label1");
        assertEq(f.encoding, "enc" + i, "encoding");
      } else {
        assertEq(label, "f" + i + ":2:main" + i + ":true", "label2");
      }
      assertEq(f.describe(), expectKeys[k], "keys");
      assertEq("loadedName" in f, k !== 1, "in");
    }
  }
  var want = 0;
  for (var i = 0; i < fonts.length; i++) {
    want += i % 3 === 0 ? -1 : (i + 1) + i * 2;
  }
  assertEq(sum, want * 20, "widths");

  // A hole filled after construction, then read by the methods.
  for (var i = 1; i < fonts.length; i += 3) {
    fonts[i].loadedName = "late" + i;
    fonts[i].loading = 7;
  }
  for (var i = 1; i < fonts.length; i += 3) {
    assertEq(fonts[i].label(), "f" + i + ":1:late" + i + ":7", "late");
    assertEq(fonts[i].describe(), "name,type,widths,defaultWidth,encoding,loadedName,loading", "late keys");
  }

  // Generic consumers.
  var j = JSON.parse(JSON.stringify(fonts[2]));
  assertEq(Object.keys(j).join(","), expectKeys[2], "json keys");
  assertEq(j.loadedName, "main2", "json value");
  var copy = Object.assign({}, fonts[4]);
  assertEq(copy.encoding + copy.loadedName, "enc4late4", "assign");
  var spread = { ...fonts[0] };
  assertEq(spread.loadedName, "early0", "spread");
  var seen = [];
  for (var p in fonts[5]) {
    if (fonts[5].hasOwnProperty(p)) seen.push(p);
  }
  assertEq(seen.join(","), expectKeys[2], "for-in");

  // Deletes and re-adds.
  var d = new Font(1, 99);
  delete d.encoding;
  d.loadedName = "x";
  assertEq(d.label(), "f99:1:x:undefined", "delete");
  assertEq(d.width(0), 99 + 198, "delete width");
  gc();
  for (var i = 0; i < fonts.length; i++) {
    assertEq(fonts[i].name, "f" + i, "after gc");
  }
}
run();
run();
