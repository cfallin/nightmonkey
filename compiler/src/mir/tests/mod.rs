//! Text-format fixtures.
//!
//! Fixtures (`*.mir` next to this file) must round-trip through the
//! printer and parser.

use crate::mir::parse::parse;
use crate::mir::print::print_module;
use crate::mir::Module;

const FIXTURES: &[(&str, &str)] = &[
    ("basic.mir", include_str!("basic.mir")),
    ("fence_rejoin.mir", include_str!("fence_rejoin.mir")),
    ("ops.mir", include_str!("ops.mir")),
];

fn assert_roundtrip(m: &Module) {
    let text = print_module(m);
    let m2 = parse(&text).unwrap_or_else(|e| panic!("reparse error: {e}\n{text}"));
    assert_eq!(*m, m2, "parse(print(m)) != m\n{text}");
    assert_eq!(text, print_module(&m2), "printing is not deterministic");
}

#[test]
fn fixtures_roundtrip() {
    for (name, src) in FIXTURES {
        let m = parse(src).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_roundtrip(&m);
    }
}

#[test]
fn printing_is_canonical() {
    // Hand-written text may omit inferable result types and atom
    // declarations; the printer's output is a fixed point.
    for (name, src) in FIXTURES {
        let once = print_module(&parse(src).unwrap());
        let twice = print_module(&parse(&once).unwrap());
        assert_eq!(once, twice, "{name}");
    }
}

#[test]
fn parse_errors() {
    let cases = [
        ("func @s1 () {\n  root entry b0\nb0:\n  bogus.op\n}", "unknown opcode"),
        ("func @s1 () {\n  root entry b0\nb0:\n  return v9\n}", "v9 is used but never defined"),
        ("func @s1 () {\n  root entry b0\nb0(v0: val):\n  v0 = const.i32 1\n  return v0\n}", "defined twice"),
        ("func @s1 () {\n  root entry b0\nb0:\n  jump b7\n}", "undefined block"),
        (
            "func @s1 () {\n  root entry b0\nb0(v0: val):\n  guard.unbox.i32 v0 -> fail b1, ok b2(v1: i32)\nb1:\n  unreachable\nb2(v1: i32):\n  unreachable\n}",
            "expected successors [ok, fail]",
        ),
        (
            "func @s1 () {\n  root entry b0\nb0(v0: val):\n  guard.unbox.i32 v0 -> ok b2(v1: i32[0,1]), fail b1\nb1:\n  unreachable\nb2(v1: i32):\n  unreachable\n}",
            "disagrees with b2's header",
        ),
        ("func @s1 () {\n  root entry b0\nb0:\n  v1 = unbox.i32 v2\n  v2 = const.val null\n  unreachable\n}", "cannot infer"),
    ];
    for (src, needle) in cases {
        let e = parse(src).expect_err(src);
        assert!(e.msg.contains(needle), "{needle:?} not in {e}");
    }
}

#[test]
#[ignore]
fn dump_fixtures() {
    for (name, src) in FIXTURES {
        println!("==== {name}\n{}", print_module(&parse(src).unwrap()));
    }
}
