// RegExpBuiltinExec reads lastIndex for every regexp, so a valueOf on it is
// observable even when the regexp is neither global nor sticky.
var gets = 0;
var counter = { valueOf: function() { gets++; return 0; } };
var r = /a/;
r.lastIndex = counter;
assertEq(r.exec("nbc"), null);
assertEq(r.lastIndex, counter);
assertEq(gets, 1);
var called = 0;
var re = /./;
re.lastIndex = { toString: function() { called++; return "0"; } };
re.exec(".");
assertEq(called, 1);
