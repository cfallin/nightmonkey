//! Text-format fixtures and validator tests.
//!
//! Fixtures (`*.mir` next to this file) must round-trip through the
//! printer and parser and validate. Every validator check family has a
//! positive test and at least one negative test naming the family and a
//! fragment of the expected message.

use crate::mir::parse::parse;
use crate::mir::print::print_module;
use crate::mir::verify::{verify_module, Check};
use crate::mir::Module;

pub(crate) const FIXTURES: &[(&str, &str)] = &[
    ("basic.mir", include_str!("basic.mir")),
    ("fence_rejoin.mir", include_str!("fence_rejoin.mir")),
    ("ops.mir", include_str!("ops.mir")),
    ("lower.mir", include_str!("lower.mir")),
];

fn parse_ok(src: &str) -> Module {
    parse(src).unwrap_or_else(|e| panic!("parse error: {e}\n{src}"))
}

fn assert_roundtrip(m: &Module) {
    let text = print_module(m);
    let m2 = parse(&text).unwrap_or_else(|e| panic!("reparse error: {e}\n{text}"));
    assert_eq!(*m, m2, "parse(print(m)) != m\n{text}");
    assert_eq!(text, print_module(&m2), "printing is not deterministic");
}

fn verify_ok(src: &str) {
    let m = parse_ok(src);
    if let Err(es) = verify_module(&m) {
        let msgs: Vec<String> = es.iter().map(|e| e.to_string()).collect();
        panic!(
            "unexpected validator errors:\n{}\n{}",
            msgs.join("\n"),
            print_module(&m)
        );
    }
    assert_roundtrip(&m);
}

fn verify_err(src: &str, check: Check, needle: &str) {
    let m = parse_ok(src);
    let es = verify_module(&m).expect_err("expected a validator error");
    assert!(
        es.iter()
            .any(|e| e.check == check && e.msg.contains(needle)),
        "expected a {check:?} error containing {needle:?}; got:\n{}",
        es.iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert_roundtrip(&m);
}

#[test]
fn fixtures_roundtrip_and_validate() {
    for (name, src) in FIXTURES {
        let m = parse(src).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_roundtrip(&m);
        if let Err(es) = verify_module(&m) {
            let msgs: Vec<String> = es.iter().map(|e| e.to_string()).collect();
            panic!("{name}: validator errors:\n{}", msgs.join("\n"));
        }
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

// A minimal function frame for the validator tests: no formals, no
// locals, stack depth 0 at pc 0 and 1 at pc 4.
const HEAD: &str = "func @s1 (formals=0, locals=0, depths={0:0, 4:1}) {\n  root entry b0\n";

fn func(body: &str) -> String {
    format!("{HEAD}{body}}}\n")
}

fn with_module(module: &str, body: &str) -> String {
    format!("module {{\n{module}\n}}\n{}", func(body))
}

const EXIT0: &str = "b99:\n  exit pc=0 this=v1 args=[] locals=[] rval=v1 stack=[]\n";

// --- 1. structure -------------------------------------------------------

#[test]
fn structure() {
    verify_ok(&func("b0(v0: obj{Function(s1)}, v1: val):\n  return v1\n"));
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.i32 1\n"),
        Check::Structure,
        "no terminator",
    );
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  return v1\n  v2 = const.i32 1\n"),
        Check::Structure,
        "no terminator",
    );
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  return v1\n  return v1\n"),
        Check::Structure,
        "is not the last instruction",
    );
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  jump b1(v1)\nb1:\n  return v1\n"),
        Check::Structure,
        "passes 1 arg(s), but it has 0",
    );
    verify_err(
        "func @s1 (formals=0, locals=0, depths={0:0}) {\n  root entry b0\n  root entry b1\n\
             b0(v0: obj{Function(s1)}, v1: val):\n  return v1\n\
             b1(v2: obj{Function(s1)}, v3: val):\n  return v3\n}\n",
        Check::Structure,
        "expected one entry root",
    );
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  jump b0(v0, v1)\n"),
        Check::Structure,
        "root has predecessors",
    );
    // Failure outputs are not a thing: a `fail` edge cannot carry one.
    verify_err(
        &func(
            "b0(v0: obj{Function(s1)}, v1: val):\n  guard.unbox.i32 v1 -> ok b1(v2: i32), fail b1(v2: i32)\n\
             b1(v2: i32):\n  unreachable\n",
        ),
        Check::Structure,
        "the fail edge cannot carry outputs",
    );
}

#[test]
fn irreducible() {
    // b1 and b2 each enter the other's cycle. MIR has no reducibility
    // invariant (§5.4): with no dominating header, there is no natural
    // loop to declare, and the function is valid.
    verify_ok(&func(
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.bool true\n  br v2 -> then b1, else b2\n\
         b1:\n  jump b2\nb2:\n  br v2 -> then b1, else b3\nb3:\n  return v1\n",
    ));
    // A natural loop must be declared.
    verify_err(
        &func(
            "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.bool true\n  jump b3\n\
             b3:\n  br v2 -> then b3, else b4\nb4:\n  return v1\n",
        ),
        Check::Structure,
        "b3 is not a declared loop header",
    );
}

/// An onramp into an inner loop side-enters the outer one: the outer
/// header no longer dominates its latch, and the function is irreducible,
/// but both loops are declared and each has its preheader.
#[test]
fn onramp_side_entry() {
    verify_ok(
        "func @s1 (formals=0, locals=0, depths={0:0, 8:0}) {\n  root entry b0\n  root onramp(pc=8) b9\n\
           loop b2 preheader=b1\n  loop b4 preheader=b3\n\
         b0(v0: obj{Function(s1)}, v1: val):\n  jump b1(v1)\n\
         b1(v2: val):\n  jump b2(v2)\n\
         b2(v3: val):\n  v4 = const.bool true\n  br v4 -> then b3(v3), else b6(v3)\n\
         b3(v5: val):\n  jump b4(v5)\n\
         b4(v6: val):\n  v7 = const.bool true\n  br v7 -> then b4(v6), else b5(v6)\n\
         b5(v8: val):\n  jump b2(v8)\n\
         b6(v9: val):\n  return v9\n\
         b9(v10: val, v11: val):\n  v12 = const.bool true\n  br v12 -> then b3(v10), else b10\n\
         b10:\n  exit pc=8 this=v10 args=[] locals=[] rval=v11 stack=[]\n}\n",
    );
}

// --- 2. dominance -------------------------------------------------------

#[test]
fn dominance() {
    verify_ok(&func(
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.bool true\n  br v2 -> then b1, else b2\n\
         b1:\n  jump b3(v1)\nb2:\n  jump b3(v1)\nb3(v3: val):\n  return v3\n",
    ));
    // A value from one arm used after the merge.
    verify_err(
        &func(
            "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.bool true\n  br v2 -> then b1, else b2\n\
             b1:\n  v4 = const.val null\n  jump b3\nb2:\n  jump b3\nb3:\n  return v4\n",
        ),
        Check::Dominance,
        "use of v4",
    );
    // Use before def in one block.
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  v2: val = weaken v3\n  v3 = const.val null\n  return v2\n"),
        Check::Dominance,
        "use of v3",
    );
    // Values do not flow between roots: an onramp root sees none of
    // the entry root's values.
    verify_err(
        "func @s1 (formals=0, locals=0, depths={0:0, 8:0}) {\n  root entry b0\n  root onramp(pc=8) b5\n\
             b0(v0: obj{Function(s1)}, v1: val):\n  return v1\n\
             b5(v5: val):\n  return v1\n}\n",
        Check::Dominance,
        "use of v1",
    );
}

// --- 3. edge subtyping --------------------------------------------------

#[test]
fn edge_subtyping() {
    // Narrower into wider: fine (an implicit weakening).
    verify_ok(&func(
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.val int32 3\n  jump b1(v2)\nb1(v3: val{int32,double}):\n  return v3\n",
    ));
    verify_err(
        &func(
            "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.val int32 3\n  jump b1(v1)\nb1(v3: val{int32}):\n  return v3\n",
        ),
        Check::EdgeType,
        "is not a subtype of param v3",
    );
    // Across representations, never.
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.i32 3\n  jump b1(v2)\nb1(v3: val):\n  return v3\n"),
        Check::EdgeType,
        "different representations",
    );
    // An output must fit its param, too.
    verify_err(
        &func(&format!(
            "b0(v0: obj{{Function(s1)}}, v1: val):\n  guard.unbox.i32 v1 -> ok b1(v2: i32[0,9]), fail b99\n\
             b1(v2: i32[0,9]):\n  unreachable\n{EXIT0}"
        )),
        Check::EdgeType,
        "output %0 (i32) is not a subtype of param v2",
    );
}

// --- 4. operand types ---------------------------------------------------

#[test]
fn operand_types() {
    verify_ok(&func(
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.val int32 3\n  v3 = unbox.i32 v2\n  v4 = box v3\n  return v4\n",
    ));
    // `unbox.i32` needs a proof of the tag.
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  v2: i32 = unbox.i32 v1\n  unreachable\n"),
        Check::OperandType,
        "is not proven to have tags {int32}",
    );
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.i32 1\n  br v2 -> then b1, else b1\nb1:\n  return v1\n"),
        Check::OperandType,
        "br: expected a bool",
    );
    // A declared result may be weaker than the rule, never stronger.
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  v2: val{int32} = weaken v1\n  return v2\n"),
        Check::OperandType,
        "is not a supertype of the rule's val",
    );
    // Without `types` on the layout claim, a field load is only a val: a
    // successor expecting the field's claim is ill-typed.
    let m = "  layout L3 = { x: val{int32} }";
    verify_err(
        &with_module(
            m,
            &format!(
                "b0(v0: obj{{Function(s1)}}, v1: val):\n  guard.unbox.obj v1 -> ok b1(v2: obj), fail b99\n\
                 b1(v2: obj):\n  guard.layout v2 L3 -> ok b2(v3: obj{{L3}}), fail b99\n\
                 b2(v3: obj{{L3}}):\n  load_field v3 x -> ok_clean b3(v4: val{{int32}}), ok_dirty b99, err b99\n\
                 b3(v4: val{{int32}}):\n  return v4\n{EXIT0}"
            ),
        ),
        Check::EdgeType,
        "is not a subtype of param",
    );
}

// --- 5, 6. fences and predictions ---------------------------------------

/// The §10.3 fixture with the second `a.x` guard folded across the
/// `ok_dirty` edge: `a` keeps its layout claim through the call's dirty
/// edge, which kills it.
#[test]
fn fence_rejoin_wrong_fold() {
    let good = include_str!("fence_rejoin.mir");
    let bad = good.replace("ok_dirty b8(v27: val, v12)", "ok_dirty b9(v12)");
    assert_ne!(good, bad);
    verify_err(
        &bad,
        Check::Fence,
        "v12 flows across the ok_dirty edge of call into param v30",
    );
    // The other way to get it wrong: use `a` directly after the join.
    let bad2 = good.replace("load_field v30 x", "load_field v12 x");
    assert_ne!(good, bad2);
    verify_err(
        &bad2,
        Check::Fence,
        "v12 (obj{L3 types}) is live into b8 across the ok_dirty edge of call",
    );
}

#[test]
fn fences() {
    let m = "  layout L3 = { x: val{int32} }\n  binding G0 = g : val\n  fuse F0 = f";
    let guarded =
        "b0(v0: obj{Function(s1)}, v1: val):\n  guard.unbox.obj v1 -> ok b1(v2: obj), fail b99\n\
         b1(v2: obj):\n  guard.layout v2 L3 types -> ok b2(v3: obj{L3 types}), fail b99\n";
    // Weakening through the dirty edge's param, then using the weak
    // value: fine.
    verify_ok(&with_module(
        m,
        &format!(
            "{guarded}b2(v3: obj{{L3 types}}):\n  v4 = const.val undefined\n  \
             call v1, v4 -> ok_clean b3(v3), ok_dirty b3(v3), err b98\n\
             b3(v5: obj):\n  v6 = box v5\n  return v6\n{EXIT0}\
             b98:\n  exit.throw pc=0 this=v1 args=[] locals=[] rval=v1 stack=[]\n"
        ),
    ));
    // A throw block may box a value whose claim the op killed; any
    // other `err` target is a fence edge like `ok_dirty`.
    let err_into = |target: &str| {
        with_module(
            m,
            &format!(
                "{guarded}b2(v3: obj{{L3 types}}):\n  v4 = const.val undefined\n  \
                 call v1, v4 -> ok_clean b3(v3), ok_dirty b3(v3), err {target}\n\
                 b3(v5: obj):\n  v6 = box v5\n  return v6\n{EXIT0}\
                 b98:\n  v7 = box v3\n  v8: val = weaken v7\n  exit.throw pc=4 this=v1 args=[] locals=[] rval=v1 stack=[v8]\n\
                 b97:\n  guard.layout v3 L3 -> ok b98, fail b98\n"
            ),
        )
    };
    verify_ok(&err_into("b98"));
    verify_err(
        &err_into("b97"),
        Check::Fence,
        "is live into b97 across the err edge of call",
    );
    // A single-successor fence: the fuse fact may not live across a store
    // to a global.
    verify_err(
        &with_module(
            m,
            &format!(
                "b0(v0: obj{{Function(s1)}}, v1: val):\n  check.fuse F0 -> ok b1(v2: fact.fuse(F0)), fail b99\n\
                 b1(v2: fact.fuse(F0)):\n  check.binding G0 -> ok b2(v3: fact.binding(G0)), fail b99\n\
                 b2(v3: fact.binding(G0)):\n  store_gname v3, v1 G0 !pred{{fuse}}\n  jump b3(v2)\n\
                 b3(v4: fact.fuse(F0)):\n  return v1\n{EXIT0}"
            ),
        ),
        Check::Fence,
        "v2 (fact.fuse(F0)) is live across store_gname",
    );
}

#[test]
fn dead_params_leave_throw_blocks() {
    // A throw block that boxes `v3` (whose TYPES the calls kill) and has a
    // param nothing reads, fed different values by its two `err` edges
    // (`pea` puts its object on every block of its real part): with the
    // param it is not a throw block, so `v3` is live across both fences.
    // `optimize` drops the param, and the block is a throw block again.
    let src = with_module(
        "  layout L3 = { x: val{int32} }",
        &format!(
            "b0(v0: obj{{Function(s1)}}, v1: val):\n  guard.unbox.obj v1 -> ok b1(v2: obj), fail b99\n\
             b1(v2: obj):\n  guard.layout v2 L3 types -> ok b2(v3: obj{{L3 types}}), fail b99\n\
             b2(v3: obj{{L3 types}}):\n  v4 = const.val undefined\n  \
             call v1, v4 -> ok_clean b3(v3), ok_dirty b3(v3), err b98(v2)\n\
             b3(v5: obj):\n  call v1, v4 -> ok_clean b4, ok_dirty b4, err b98(v5)\n\
             b4:\n  v6 = box v5\n  return v6\n{EXIT0}\
             b98(v9: obj):\n  v7 = box v3\n  v8: val = weaken v7\n  exit.throw pc=4 this=v1 args=[] locals=[] rval=v1 stack=[v8]\n"
        ),
    );
    verify_err(&src, Check::Fence, "v3 (obj{L3 types}) is live into b98 across the err edge of call");
    let mut m = parse_ok(&src);
    let mut f = m.funcs.pop().unwrap();
    crate::mir::opt::optimize(&m, &mut f);
    m.funcs.push(f);
    let text = print_module(&m);
    if let Err(es) = verify_module(&m) {
        panic!("invalid after optimizing: {:?}\n{text}", es);
    }
    assert!(text.contains("\nb98:\n"), "{text}");
}

#[test]
fn predictions() {
    let m = "  layout L6 = { a: val }";
    let ctor = |witness: &str| {
        with_module(
            m,
            &format!(
                "b0(v0: obj{{Function(s1)}}, v1: val):\n  v2 = new_object L6\n  \
                 init_field v2, v1 a -> ok b1(v3: obj{{Plain, L6 types constructing(1)}}), fail b99\n\
                 b1(v3: obj{{Plain, L6 types constructing(1)}}):\n  v4 = publish_layout v3{witness}\n  \
                 v5 = box v4\n  return v5\n{EXIT0}"
            ),
        )
    };
    verify_ok(&ctor(" !pred{constructing}"));
    verify_err(&ctor(""), Check::Prediction, "(no witness)");
    verify_err(&ctor(" !pred{fuse}"), Check::Prediction, "does not cover");
    // A kill on an `ok_dirty` edge (the §10.3 call, and since facts are
    // fixed every op that runs JS) needs no witness: its clean edge kills
    // nothing.
}

// --- 7. raw pointers across GC ------------------------------------------

#[test]
fn raw_across_gc() {
    let m = "  layout L6 = { a: val }";
    let body = |use_after: bool| {
        let (before, after) = if use_after {
            ("", "  v4 = elements_ptr v2\n  v5 = new_object L6\n  v6 = new_array v3\n  jump b1(v4)\n")
        } else {
            (
                "  v4 = elements_ptr v2\n",
                "  v5 = new_object L6\n  jump b1(v4)\n",
            )
        };
        with_module(
            m,
            &format!(
                "b0(v0: obj{{Function(s1)}}, v1: val):\n  v3 = const.i32 4\n  v2 = new_array v3\n{before}{after}\
                 b1(v7: raw.elements):\n  return v1\n"
            ),
        )
    };
    // Recomputed after the last may-GC op: fine.
    verify_ok(&with_module(
        m,
        "b0(v0: obj{Function(s1)}, v1: val):\n  v3 = const.i32 4\n  v2 = new_array v3\n  \
         v5 = new_object L6\n  v4 = elements_ptr v2\n  jump b1(v4)\nb1(v7: raw.elements):\n  return v1\n",
    ));
    verify_err(
        &body(false),
        Check::RawGc,
        "raw pointer v4 (raw.elements) is live across may-GC new_object",
    );
    verify_err(&body(true), Check::RawGc, "live across may-GC new_array");
}

// --- 8. boundary --------------------------------------------------------

#[test]
fn boundary_exits() {
    let exit = |this: &str, stack: &str| {
        func(&format!(
            "b0(v0: obj{{Function(s1)}}, v1: val):\n  v2 = const.val int32 1\n  v3: val = weaken v2\n  \
             exit pc=4 this={this} args=[] locals=[] rval={this} stack=[{stack}]\n"
        ))
    };
    verify_ok(&exit("v1", "v3"));
    // Narrower values and raw representations cross too: the lowering
    // boxes them at the exit hub.
    verify_ok(&exit("v1", "v2"));
    verify_ok(&func(
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.i32 7\n  v3 = const.f64 1.5\n  \
         exit pc=4 this=v1 args=[] locals=[] rval=v3 stack=[v2]\n",
    ));
    verify_err(
        &exit("v1", ""),
        Check::Boundary,
        "the frame needs 3 (stack depth 1)",
    );
    verify_err(
        &func(
            "b0(v0: obj{Function(s1)}, v1: val):\n  exit pc=9 this=v1 args=[] locals=[] rval=v1 stack=[]\n",
        ),
        Check::Boundary,
        "no stack depth is recorded for pc 9",
    );
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val):\n  exit pc=0 this=v1 args=[v1] locals=[] rval=v1 stack=[]\n"),
        Check::Boundary,
        "carries 1 arg(s)",
    );
}

#[test]
fn boundary_roots() {
    verify_err(
        &func("b0(v0: obj{Function(s1)}, v1: val{int32}):\n  return v1\n"),
        Check::Boundary,
        "entry param v1 (val{int32}) must be val",
    );
    verify_err(
        &func("b0(v0: obj{Function(s2)}, v1: val):\n  return v1\n"),
        Check::Boundary,
        "claims more than the callee's identity",
    );
    verify_err(
        &func("b0(v1: val):\n  return v1\n"),
        Check::Boundary,
        "entry root takes 1 param(s)",
    );
    let onramp = |params: &str| {
        format!(
            "func @s1 (formals=0, locals=1, depths={{0:0, 8:0}}) {{\n  root entry b0\n  root onramp(pc=8) b5\n\
             b0(v0: obj{{Function(s1)}}, v1: val):\n  return v1\n\
             b5({params}):\n  unreachable\n}}\n"
        )
    };
    // this, the local, rval.
    verify_ok(&onramp("v5: val, v6: val, v7: val"));
    verify_err(
        &onramp("v5: val, v6: val{int32}, v7: val"),
        Check::Boundary,
        "onramp param v6 (val{int32}) must be val",
    );
    verify_err(
        &onramp("v5: val, v6: val"),
        Check::Boundary,
        "takes 2 param(s); the frame needs 3",
    );
}

#[test]
fn boundary_preheaders() {
    let with_loop = |decl: &str, body: &str| format!("{HEAD}  {decl}\n{body}}}\n");
    // Two entries into the loop header: b2 is not its preheader.
    let two_entries = with_loop(
        "loop b3 preheader=b1",
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.bool true\n  br v2 -> then b1, else b2\n\
         b1:\n  jump b3\nb2:\n  jump b3\nb3:\n  br v2 -> then b3, else b4\nb4:\n  return v1\n",
    );
    verify_err(
        &two_entries,
        Check::Boundary,
        "entered from outside the loop by [b2], not only by its preheader b1",
    );
    // A preheader that also branches elsewhere is not one.
    let branchy = with_loop(
        "loop b3 preheader=b0",
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.bool true\n  br v2 -> then b3, else b4\n\
         b3:\n  br v2 -> then b3, else b4\nb4:\n  return v1\n",
    );
    verify_err(
        &branchy,
        Check::Boundary,
        "preheader b0 must jump only to its header b3",
    );
    // A latch declared as the preheader: the real entry is then outside.
    let latch = with_loop(
        "loop b3 preheader=b5",
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.bool true\n  jump b3\n\
         b3:\n  br v2 -> then b5, else b4\nb5:\n  jump b3\nb4:\n  return v1\n",
    );
    verify_err(
        &latch,
        Check::Boundary,
        "entered from outside the loop by [b0]",
    );
    verify_ok(&with_loop(
        "loop b3 preheader=b0",
        "b0(v0: obj{Function(s1)}, v1: val):\n  v2 = const.bool true\n  jump b3\n\
         b3:\n  br v2 -> then b3, else b4\nb4:\n  return v1\n",
    ));
}

#[test]
#[ignore]
fn dump_fixtures() {
    for (name, src) in FIXTURES {
        println!("==== {name}\n{}", print_module(&parse(src).unwrap()));
    }
}

// --- passes -------------------------------------------------------------

/// Guard folding (§10.1): the second receiver guard pair folds against the
/// first; after a call, object-ness still folds (it is invariant), but the
/// layout claim died on the call's dirty edge, so that guard stays.
#[test]
fn fold_guards_across_a_fence() {
    let src = "module {\n  layout L3 = { x: val{int32,double} }\n}\n\
func @s1 (formals=1, locals=0, depths={0:0}) {\n  root entry b0\n\
b0(v0: obj{Function(s1)}, v1: val, v2: val):\n  guard.unbox.obj v2 -> ok b1(v3: obj), fail b9\n\
b1(v3: obj):\n  guard.layout v3 L3 types -> ok b2(v4: obj{L3 types}), fail b9\n\
b2(v4: obj{L3 types}):\n  guard.unbox.obj v2 -> ok b3(v5: obj), fail b9\n\
b3(v5: obj):\n  guard.layout v5 L3 types -> ok b4(v6: obj{L3 types}), fail b9\n\
b4(v6: obj{L3 types}):\n  v7 = const.val undefined\n  call v1, v7 -> ok_clean b5(v8: val), ok_dirty b11(v11: val), err b10\n\
b11(v11: val):\n  jump b5(v11)\n\
b5(v8: val):\n  guard.unbox.obj v2 -> ok b6(v9: obj), fail b9\n\
b6(v9: obj):\n  guard.layout v9 L3 types -> ok b7(v10: obj{L3 types}), fail b9\n\
b7(v10: obj{L3 types}):\n  return v8\n\
b9:\n  exit pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n\
b10:\n  exit.throw pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n}\n";
    let mut m = parse_ok(src);
    verify_module(&m).expect("valid before");
    let mut f = m.funcs.pop().unwrap();
    let n = crate::mir::opt::optimize(&m, &mut f);
    m.funcs.push(f);
    if let Err(es) = verify_module(&m) {
        panic!("invalid after folding: {:?}\n{}", es, print_module(&m));
    }
    assert_eq!(n, 3, "{}", print_module(&m));
    let text = print_module(&m);
    assert_eq!(text.matches("guard.layout").count(), 2, "{text}");
    assert_eq!(text.matches("guard.unbox.obj").count(), 1, "{text}");
}

#[test]
fn slot_loads_number_and_hoist() {
    // Two loads of `v4.x` in a loop, through a receiver proven before it
    // with SLOTS: both become `load_slot`, the second is the first, and
    // the one left hoists into the preheader (nothing in the loop writes
    // `x`).
    let src = "module {\n  layout L3 = { x: val{int32} }\n}\n\
func @s1 (formals=1, locals=0, depths={0:0}) {\n  root entry b0\n  loop b2 preheader=b1\n\
b0(v0: obj{Function(s1)}, v1: val, v2: val):\n  guard.unbox.obj v2 -> ok b5(v3: obj), fail b9\n\
b5(v3: obj):\n  guard.layout v3 L3 types slots -> ok b6(v4: obj{L3 types slots}), fail b9\n\
b6(v4: obj{L3 types slots}):\n  v5 = const.i32 0\n  jump b1(v5)\n\
b1(v6: i32):\n  jump b2(v6)\n\
b2(v7: i32):\n  load_field v4 x -> ok_clean b3(v8: val{int32}), ok_dirty b9, err b10\n\
b3(v8: val{int32}):\n  load_field v4 x -> ok_clean b4(v9: val{int32}), ok_dirty b9, err b10\n\
b4(v9: val{int32}):\n  v10 = unbox.i32 v8\n  v14 = unbox.i32 v9\n  i32.add.ovf v10, v14 -> ok b7(v11: i32), fail b9\n\
b7(v11: i32):\n  v12 = const.i32 100\n  v13 = i32.cmp.lt v11, v12\n  br v13 -> then b2(v11), else b8\n\
b8:\n  return v1\n\
b9:\n  exit pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n\
b10:\n  exit.throw pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n}\n";
    let mut m = parse_ok(src);
    verify_module(&m).expect("valid before");
    let mut f = m.funcs.pop().unwrap();
    crate::mir::opt::optimize(&m, &mut f);
    m.funcs.push(f);
    let text = print_module(&m);
    if let Err(es) = verify_module(&m) {
        panic!("invalid after optimizing: {:?}\n{text}", es);
    }
    assert_eq!(text.matches("load_field").count(), 0, "{text}");
    assert_eq!(text.matches("load_slot").count(), 1, "{text}");
    let pre = text
        .split("\n\n")
        .find(|blk| blk.starts_with("b1:") || blk.starts_with("b1("))
        .unwrap_or("");
    assert!(pre.contains("load_slot"), "not hoisted into the preheader:\n{text}");
}

/// Run `optimize` on the module's one function, check it still
/// validates, and return its text.
fn optimized(src: &str) -> String {
    let mut m = parse_ok(src);
    verify_module(&m).expect("valid before");
    let mut f = m.funcs.pop().unwrap();
    crate::mir::opt::optimize(&m, &mut f);
    m.funcs.push(f);
    let text = print_module(&m);
    if let Err(es) = verify_module(&m) {
        panic!("invalid after optimizing: {:?}\n{text}", es);
    }
    text
}

/// A function over two receivers `v4: obj{L3 types slots}` and
/// `v6: obj{L4 types slots}` (both with a field `x`), with `body` in b2
/// (which ends by returning or branching to b9/b10).
fn two_receivers(body: &str) -> String {
    format!(
        "module {{\n  layout L3 = {{ x: val{{int32}} }}\n  layout L4 = {{ x: val{{int32}} }}\n}}\n\
func @s1 (formals=2, locals=0, depths={{0:0}}) {{\n  root entry b0\n\
b0(v0: obj{{Function(s1)}}, v1: val, v2: val, v3: val):\n  guard.unbox.obj v2 -> ok b5(v20: obj), fail b9\n\
b5(v20: obj):\n  guard.layout v20 L3 types slots -> ok b6(v4: obj{{L3 types slots}}), fail b9\n\
b6(v4: obj{{L3 types slots}}):\n  guard.unbox.obj v3 -> ok b7(v21: obj), fail b9\n\
b7(v21: obj):\n  guard.layout v21 L4 types slots -> ok b2(v6: obj{{L4 types slots}}), fail b9\n\
b2(v6: obj{{L4 types slots}}):\n{body}\
b9:\n  exit pc=0 this=v1 args=[v2, v3] locals=[] rval=v1 stack=[]\n\
b10:\n  exit.throw pc=0 this=v1 args=[v2, v3] locals=[] rval=v1 stack=[]\n}}\n"
    )
}

#[test]
fn store_forwards_to_load() {
    // `v4.x = 7; return v4.x`: the load is the stored value.
    let text = optimized(&two_receivers(
        "  v30 = const.i32 7\n  v31 = box v30\n  v32: val{int32} = weaken v31\n\
  store_field v4, v32 x -> ok_clean b11, ok_dirty b9, err b10\n\
b11:\n  load_field v4 x -> ok_clean b12(v33: val{int32}), ok_dirty b9, err b10\n\
b12(v33: val{int32}):\n  return v33\n",
    ));
    assert_eq!(text.matches("load_").count(), 0, "{text}");
    assert!(text.contains("return v32"), "{text}");
}

#[test]
fn loads_number_across_another_class_store() {
    // `a = v4.x; v6.x = 7; b = v4.x`: L4's `x` is not L3's, so the second
    // load of `v4.x` is the first.
    let text = optimized(&two_receivers(
        "  load_field v4 x -> ok_clean b11(v33: val{int32}), ok_dirty b9, err b10\n\
b11(v33: val{int32}):\n  v30 = const.i32 7\n  v31 = box v30\n  v32: val{int32} = weaken v31\n\
  store_field v6, v32 x -> ok_clean b12, ok_dirty b9, err b10\n\
b12:\n  load_field v4 x -> ok_clean b13(v34: val{int32}), ok_dirty b9, err b10\n\
b13(v34: val{int32}):\n  v35 = unbox.i32 v33\n  v36 = unbox.i32 v34\n  i32.add.ovf v35, v36 -> ok b14(v37: i32), fail b9\n\
b14(v37: i32):\n  v38 = box v37\n  return v38\n",
    ));
    assert_eq!(text.matches("load_slot").count(), 1, "{text}");
}

#[test]
fn loads_do_not_number_across_a_call() {
    let text = optimized(&two_receivers(
        "  load_field v4 x -> ok_clean b11(v33: val{int32}), ok_dirty b9, err b10\n\
b11(v33: val{int32}):\n  v39 = const.val undefined\n  call v1, v39 -> ok_clean b12(v40: val), ok_dirty b9, err b10\n\
b12(v40: val):\n  load_field v4 x -> ok_clean b13(v34: val{int32}), ok_dirty b9, err b10\n\
b13(v34: val{int32}):\n  v35 = unbox.i32 v33\n  v36 = unbox.i32 v34\n  i32.add.ovf v35, v36 -> ok b14(v37: i32), fail b9\n\
b14(v37: i32):\n  v38 = box v37\n  return v38\n",
    ));
    assert_eq!(text.matches("load_slot").count(), 2, "{text}");
}

#[test]
fn length_of_a_field_hoists() {
    // `for (i = 0; i < this.arr.length; i++)`, with `this` proven before
    // the loop: the field load (an object: a managed result), its unbox
    // and kind guards, the length and its int32 guard all leave the loop.
    let src = "module {\n  layout L3 = { arr: val{object} }\n}\n\
func @s1 (formals=1, locals=0, depths={0:0}) {\n  root entry b0\n  loop b2 preheader=b1\n\
b0(v0: obj{Function(s1)}, v1: val, v2: val):\n  guard.unbox.obj v1 -> ok b12(v3: obj), fail b9\n\
b12(v3: obj):\n  guard.layout v3 L3 types slots -> ok b13(v4: obj{L3 types slots}), fail b9\n\
b13(v4: obj{L3 types slots}):\n  v5 = const.val undefined\n  jump b1(v1, v2, v5)\n\
b1(v10: val, v11: val, v12: val):\n  v13 = const.i32 0\n  jump b2(v13)\n\
b2(v14: i32):\n  load_field v4 arr -> ok_clean b3(v15: val{object}), ok_dirty b9, err b10\n\
b3(v15: val{object}):\n  guard.unbox.obj v15 -> ok b4(v16: obj), fail b9\n\
b4(v16: obj):\n  guard.kind v16 Array -> ok b5(v17: obj{Array}), fail b9\n\
b5(v17: obj{Array}):\n  v18 = length.array v17\n  int.to_i32 v18 -> ok b6(v19: i32), fail b9\n\
b6(v19: i32):\n  v20 = i32.cmp.lt v14, v19\n  br v20 -> then b7, else b8\n\
b7:\n  v21 = const.i32 1\n  i32.add.ovf v14, v21 -> ok b11(v22: i32), fail b9\n\
b11(v22: i32):\n  jump b2(v22)\n\
b8:\n  return v5\n\
b9:\n  exit pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n\
b10:\n  exit.throw pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n}\n";
    let mut m = parse_ok(src);
    verify_module(&m).expect("valid before");
    let mut f = m.funcs.pop().unwrap();
    f.loops[0].entry = Some(crate::mir::func::LoopEntry {
        pc: crate::ids::Pc::new(0),
        slots: vec![true, true, true],
        state: vec![],
    });
    crate::mir::opt::optimize(&m, &mut f);
    // The loop: the blocks that reach its latch from its header.
    let h = f.loops[0].header;
    let mut preds: std::collections::BTreeMap<crate::mir::entity::Block, Vec<crate::mir::entity::Block>> =
        Default::default();
    for &b in &f.layout {
        for s in f.succs(b) {
            preds.entry(s).or_default().push(b);
        }
    }
    let mut reach = std::collections::BTreeSet::new();
    let mut work = vec![h];
    while let Some(b) = work.pop() {
        if reach.insert(b) {
            work.extend(f.succs(b));
        }
    }
    let mut body = std::collections::BTreeSet::from([h]);
    let mut work: Vec<_> = preds[&h].iter().copied().filter(|b| reach.contains(b)).collect();
    while let Some(b) = work.pop() {
        if b != h && reach.contains(&b) && body.insert(b) {
            work.extend(preds.get(&b).into_iter().flatten().copied());
        }
    }
    let ops: Vec<String> = body
        .iter()
        .flat_map(|&b| f.blocks[b].insts.iter().map(|&i| crate::mir::print::mnemonic(&f.insts[i].op)).collect::<Vec<_>>())
        .collect();
    m.funcs.push(f);
    let text = print_module(&m);
    if let Err(es) = verify_module(&m) {
        panic!("invalid after optimizing: {:?}\n{text}", es);
    }
    for op in ["load_slot", "guard.unbox.obj", "guard.kind", "length.array", "int.to_i32"] {
        assert!(!ops.iter().any(|o| o == op), "{op} left in the loop ({ops:?}):\n{text}");
    }
    assert!(ops.iter().any(|o| o == "i32.cmp.lt"), "{ops:?}\n{text}");
}

#[test]
fn literal_is_scalar_replaced() {
    // `o = {x: 7}; <guard that may exit with o on the stack>; return o.x`:
    // the load is the init's value, and the object exists only on the
    // exit's path, rebuilt there.
    let text = optimized(
        "module {\n  layout L3 = { x: val{int32} }\n}\n\
func @s1 (formals=1, locals=0, depths={0:0, 5:1}) {\n  root entry b0\n\
b0(v0: obj{Function(s1)}, v1: val, v2: val):\n  lit.new 2 -> ok b1(v5: val{object}), err b10\n\
b1(v5: val{object}):\n  stamp.fresh v5 0x20004\n  v6 = const.i32 7\n  v7 = box v6\n  v8: val{int32} = weaken v7\n\
  lit.init v5, v8 x, L3 -> ok b2, err b10\n\
b2:\n  guard.unbox.i32 v2 -> ok b3(v9: i32), fail b11\n\
b3(v9: i32):\n  guard.unbox.obj v5 -> ok b4(v10: obj), fail b9\n\
b4(v10: obj):\n  guard.layout v10 L3 slots -> ok b5(v11: obj{L3 slots}), fail b9\n\
b5(v11: obj{L3 slots}):\n  v12 = load_slot v11 x\n  return v12\n\
b9:\n  exit pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n\
b10:\n  exit.throw pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n\
b11:\n  exit pc=5 this=v1 args=[v2] locals=[] rval=v1 stack=[v5]\n}\n",
    );
    assert_eq!(text.matches("lit.new").count(), 1, "{text}");
    assert_eq!(text.matches("load_slot").count(), 0, "{text}");
    assert_eq!(text.matches("guard.layout").count(), 0, "{text}");
    // The one allocation left is on the exit's path, before the exit.
    let exit_path = text.split("\n\n").filter(|b| b.contains("lit.new") || b.contains("lit.init") || b.contains("pc=5")).count();
    assert!(exit_path >= 2, "{text}");
    assert!(text.contains("return v8") || text.contains("return v7"), "{text}");
}

#[test]
fn owners_example_folds_to_a_constant() {
    // `let o = {x: 123}; return o.x + 2;` (the owner's example, with the
    // field in the literal: MIR-MEMORY.md §3.4): no object, no guard, no
    // unboxing, and the sum a constant.
    let text = optimized(
        "module {\n  layout L3 = { x: val{int32} }\n}\n\
func @s1 (formals=0, locals=0, depths={0:0}) {\n  root entry b0\n\
b0(v0: obj{Function(s1)}, v1: val):\n  lit.new 1 -> ok b1(v5: val{object}), err b10\n\
b1(v5: val{object}):\n  stamp.fresh v5 0x20004\n  v6 = const.i32 123\n  v7 = box v6\n  v8: val{int32} = weaken v7\n\
  lit.init v5, v8 x, L3 -> ok b2, err b10\n\
b2:\n  guard.unbox.obj v5 -> ok b4(v10: obj), fail b9\n\
b4(v10: obj):\n  guard.layout v10 L3 slots -> ok b5(v11: obj{L3 slots}), fail b9\n\
b5(v11: obj{L3 slots}):\n  v12 = load_slot v11 x\n  guard.unbox.i32 v12 -> ok b6(v13: i32), fail b9\n\
b6(v13: i32):\n  v14 = const.i32 2\n  i32.add.ovf v13, v14 -> ok b7(v15: i32), fail b9\n\
b7(v15: i32):\n  v16 = box v15\n  return v16\n\
b9:\n  exit pc=0 this=v1 args=[] locals=[] rval=v1 stack=[]\n\
b10:\n  exit.throw pc=0 this=v1 args=[] locals=[] rval=v1 stack=[]\n}\n",
    );
    for op in ["lit.new", "load_slot", "guard.", "unbox", "i32.add"] {
        assert!(!text.contains(op), "{op} left:\n{text}");
    }
    assert!(text.contains("const.i32 125"), "{text}");
}

#[test]
fn unbox_of_box_keeps_fences() {
    // `v4` (a layout claim) is boxed before a call that may change its
    // class; the unbox after the call is not `v4` (which the validator
    // would reject past the fence), only `unbox`es with no such claim fold.
    let text = optimized(&two_receivers(
        "  v30 = box v4\n  v34: val{object} = weaken v30\n  v39 = const.val undefined\n\
  call v1, v39 -> ok_clean b11(v40: val), ok_dirty b11(v40: val), err b10\n\
b11(v40: val):\n  v31 = unbox.obj v34\n\
  guard.layout v31 L3 types slots -> ok b12(v32: obj{L3 types slots}), fail b9\n\
b12(v32: obj{L3 types slots}):\n  v33 = load_slot v32 x\n  return v33\n",
    ));
    assert!(text.contains("guard.layout"), "{text}");
}

/// A loop reading `v4.x` by name (`getprop.data`) through a receiver from
/// before it, with `body` after the read (b3 has the value as `v7`; it
/// ends by jumping to b4 with the counter). The loop's entry state is set
/// as the builder sets it (the text format has none).
fn data_read_loop(body: &str) -> Module {
    let src = format!(
        "module {{\n  layout L3 = {{ x: val{{int32}} }}\n}}\n\
func @s1 (formals=1, locals=0, depths={{0:0}}) {{\n  root entry b0\n  loop b2 preheader=b1\n\
b0(v0: obj{{Function(s1)}}, v1: val, v2: val):\n  jump b1(v1, v2)\n\
b1(v3: val, v4: val):\n  v5 = const.i32 0\n  jump b2(v5)\n\
b2(v6: i32):\n  getprop.data v4 x -> ok b3(v7: val), fail b9\n\
b3(v7: val):\n{body}\
b4(v11: i32):\n  v12 = const.i32 100\n  v13 = i32.cmp.lt v11, v12\n  br v13 -> then b2(v11), else b8\n\
b8:\n  return v7\n\
b9:\n  exit pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n}}\n"
    );
    let mut m = parse_ok(&src);
    m.funcs[0].loops[0].entry = Some(crate::mir::func::LoopEntry {
        pc: crate::ids::Pc::new(0),
        slots: vec![true, true, false],
        state: vec![],
    });
    verify_module(&m).expect("valid before");
    m
}

fn optimize_module(mut m: Module) -> String {
    let mut f = m.funcs.pop().unwrap();
    crate::mir::opt::optimize(&m, &mut f);
    m.funcs.push(f);
    let text = print_module(&m);
    if let Err(es) = verify_module(&m) {
        panic!("invalid after optimizing: {:?}\n{text}", es);
    }
    text
}

/// The block (`bN:` or `bN(`) holding `needle`.
fn block_of<'a>(text: &'a str, needle: &str) -> &'a str {
    let blk = text.split("\n\n").find(|b| b.contains(needle)).unwrap_or("");
    blk.split([':', '(']).next().unwrap_or("")
}

#[test]
fn data_read_hoists_with_its_exit() {
    // Nothing in the loop writes `x`: the read leaves it, its fail edge
    // becoming the loop's entry exit (pc 0, the entry state).
    let text = optimize_module(data_read_loop(
        "  v10 = const.i32 1\n  i32.add.ovf v6, v10 -> ok b4(v11: i32), fail b9\n",
    ));
    assert_eq!(text.matches("getprop.data").count(), 1, "{text}");
    let at = block_of(&text, "getprop.data");
    assert!(at == "b1" || !text.contains(&format!("loop b2 preheader={at}")), "{text}");
    let loop_blocks = ["b2:", "b2(", "b3(", "b4("];
    let inside = text
        .split("\n\n")
        .filter(|b| loop_blocks.iter().any(|p| b.starts_with(p)))
        .any(|b| b.contains("getprop.data"));
    assert!(!inside, "still in the loop:\n{text}");
}

#[test]
fn data_read_stays_under_a_store_of_its_name() {
    // `v4.x = i` in the loop (a by-name store): the read stays.
    let text = optimize_module(data_read_loop(
        "  v10 = const.i32 1\n  v14 = box v6\n\
  setprop.data v4, v14 x -> ok_clean b5, ok_dirty b9, fail b9, err b9\n\
b5:\n  i32.add.ovf v6, v10 -> ok b4(v11: i32), fail b9\n",
    ));
    let inside = text
        .split("\n\n")
        .filter(|b| b.starts_with("b2(") || b.starts_with("b2:"))
        .any(|b| b.contains("getprop.data"));
    assert!(inside, "hoisted past a store of `x`:\n{text}");
}

#[test]
fn data_reads_number() {
    // Two reads of `v4.x` with no write between: the second is the first.
    let text = optimize_module(data_read_loop(
        "  getprop.data v4 x -> ok b5(v15: val), fail b9\n\
b5(v15: val):\n  v10 = const.i32 1\n  i32.add.ovf v6, v10 -> ok b4(v11: i32), fail b9\n",
    ));
    assert_eq!(text.matches("getprop.data").count(), 1, "{text}");
}

/// `a[i]` twice through an array `v4` and an index `v5`, with `between`
/// in b11 (which ends by jumping to b12).
fn elem_twice(between: &str) -> String {
    format!(
        "module {{}}\n\
func @s1 (formals=2, locals=0, depths={{0:0}}) {{\n  root entry b0\n\
b0(v0: obj{{Function(s1)}}, v1: val, v2: val, v3: val):\n  guard.unbox.obj v2 -> ok b5(v20: obj), fail b9\n\
b5(v20: obj):\n  guard.kind v20 Array -> ok b6(v4: obj{{Array}}), fail b9\n\
b6(v4: obj{{Array}}):\n  guard.unbox.i32 v3 -> ok b7(v5: i32), fail b9\n\
b7(v5: i32):\n  load_elem v4, v5 -> ok b10(v30: val), fail b9\n\
b10(v30: val):\n  jump b11\n\
b11:\n{between}\
b12:\n  load_elem v4, v5 -> ok b13(v31: val), fail b9\n\
b13(v31: val):\n  return v31\n\
b9:\n  exit pc=0 this=v1 args=[v2, v3] locals=[] rval=v1 stack=[]\n}}\n"
    )
}

#[test]
fn element_loads_number() {
    let text = optimized(&elem_twice("  jump b12\n"));
    assert_eq!(text.matches("load_elem").count(), 1, "{text}");
    assert!(text.contains("return v30"), "{text}");
}

#[test]
fn element_loads_do_not_number_across_a_store() {
    let text = optimized(&elem_twice(
        "  v40 = const.val null\n  store_elem v4, v5, v40 -> ok b12, fail b9\n",
    ));
    assert_eq!(text.matches("load_elem").count(), 2, "{text}");
}

/// A loop that reads and writes slot 4 of the frame's environment, with
/// `body` after the write (which ends by jumping to b4 with the counter).
fn env_loop(body: &str) -> String {
    format!(
        "module {{}}\n\
func @s1 (formals=1, locals=0, depths={{0:0}}) {{\n  root entry b0\n  loop b2 preheader=b1\n\
b0(v0: obj{{Function(s1)}}, v1: val, v2: val):\n  v3 = env.current\n  jump b1\n\
b1:\n  v5 = const.i32 0\n  jump b2(v5)\n\
b2(v6: i32):\n  v7 = env.load v3 4\n  v8 = box v6\n  env.store v3, v8 4\n  jump b3\n\
b3:\n{body}\
b4(v11: i32):\n  v12 = const.i32 100\n  v13 = i32.cmp.lt v11, v12\n  br v13 -> then b2(v11), else b8\n\
b8:\n  return v1\n\
b9:\n  exit pc=0 this=v1 args=[v2] locals=[] rval=v1 stack=[]\n}}\n"
    )
}

/// The blocks of `text` whose label is one of `labels`, joined.
fn blocks_named(text: &str, labels: &[&str]) -> String {
    text.split("\n\n")
        .filter(|b| labels.iter().any(|l| b.starts_with(&format!("{l}:")) || b.starts_with(&format!("{l}("))))
        .collect::<Vec<_>>()
        .join("\n\n")
}

#[test]
fn env_slot_is_carried_around_the_loop() {
    let text = optimized(&env_loop(
        "  v10 = const.i32 1\n  i32.add.ovf v6, v10 -> ok b4(v11: i32), fail b9\n",
    ));
    let lp = blocks_named(&text, &["b2", "b3", "b4"]);
    assert!(!lp.contains("env.load") && !lp.contains("env.store"), "memory traffic left in the loop:\n{text}");
    assert!(blocks_named(&text, &["b1"]).contains("env.load"), "no load in the preheader:\n{text}");
    // Written back on the way out: to the return, and to the exit.
    assert_eq!(text.matches("env.store").count(), 2, "{text}");
}

#[test]
fn env_slot_is_written_back_around_a_call() {
    let text = optimized(&env_loop(
        "  v20 = const.val undefined\n  call v1, v20 -> ok_clean b5(v21: val), ok_dirty b9, err b9\n\
b5(v21: val):\n  v10 = const.i32 1\n  i32.add.ovf v6, v10 -> ok b4(v11: i32), fail b9\n",
    ));
    // Before the call (it may read the slot) and a reload after it (it
    // may write it).
    let call_blk = text.split("\n\n").find(|b| b.contains("call v1")).unwrap_or("");
    assert!(call_blk.contains("env.store"), "no write-back before the call:\n{text}");
    let preheader = blocks_named(&text, &["b1"]);
    assert!(
        text.split("\n\n").any(|b| b.contains("env.load") && b != preheader),
        "no reload after the call:\n{text}"
    );
}
