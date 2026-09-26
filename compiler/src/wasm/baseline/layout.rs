//! The baseline frame format: the contract between the baseline tier and
//! MIR (`docs/BASELINE.md` §2).
//!
//! Baseline keeps the whole JS frame in NightStack memory, so the state of
//! an activation at a bytecode boundary is exactly *the frame plus the
//! static operand depth at that pc*. A MIR exit writes this format and
//! resumes baseline; a MIR onramp reads it. Everything here is a function
//! of the script alone -- no slot depends on what a code generator decided
//! -- which is what lets independently compiled tiers agree on it.
//!
//! ```text
//! sp+0            callee
//! sp+8            this
//! sp+16+8i        actuals, i < max(argc, nargs)   (formals padded with undefined)
//! vp              = sp + 8*max(0, argc-nargs) if the script reads actuals past
//!                   its formals (arguments, rest, GetActualArg, mapped args), else sp
//! vp+L+8j         locals, j < nlocals             L = 16 + 8*nargs
//! vp+E            env chain
//! vp+E+8          arguments object
//! vp+E+16         new.target
//! vp+E+24         rval
//! vp+E+32         resume word                     (int32 Value, see `ResumeWord`)
//! vp+O+8k         operand stack, k < depth(pc)    O = E + 40
//! ```

use std::collections::BTreeMap;

use crate::bytecode::{OpcodeVisitor, Script, TryNoteKind};
use crate::ids::Pc;
use crate::opcodes::JSOp;

/// `argc` flag: enter the baseline body at the pc in the frame's resume
/// word instead of at its start. The frame is already complete.
/// (`0x8000_0000` is BBV's typed-entry selector, `ctx.rs` `ARGC_SEL_BIT`.)
pub const ARGC_RESUME_BIT: u32 = 0x4000_0000;
/// `argc` flag: enter a MIR body at the onramp root of the loop header
/// named by the resume word, from a baseline frame.
pub const ARGC_ONRAMP_BIT: u32 = 0x2000_0000;
/// Every `argc` flag bit; the actual count is `argc & !ARGC_FLAGS`.
pub const ARGC_FLAGS: u32 = 0x8000_0000 | ARGC_RESUME_BIT | ARGC_ONRAMP_BIT;

/// The body result that says "deopted: resume baseline at the resume
/// word", returned only by a MIR body entered through an onramp (0 is
/// ok and 1 an exception, as for every body).
pub const ERR_DEOPT: u32 = 2;

/// What a resume does once it reaches its pc.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ResumeMode {
    /// Continue executing at `pc`.
    Continue,
    /// An exception is pending: take `pc`'s exception landing.
    Throw,
}

/// The frame's resume word: a pc and a mode, stored as the payload of an
/// int32 Value so the slot is always a valid GC root.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ResumeWord {
    pub pc: Pc,
    pub mode: ResumeMode,
}

impl ResumeWord {
    /// The largest encodable pc (one bit goes to the mode).
    pub const MAX_PC: u32 = (1 << 30) - 1;

    pub fn encode(self) -> i32 {
        assert!(self.pc.get() <= Self::MAX_PC, "resume pc out of range");
        let mode = match self.mode {
            ResumeMode::Continue => 0,
            ResumeMode::Throw => 1,
        };
        ((self.pc.get() << 1) | mode) as i32
    }

    pub fn decode(w: i32) -> ResumeWord {
        let w = w as u32;
        ResumeWord {
            pc: Pc::new(w >> 1),
            mode: if w & 1 == 0 {
                ResumeMode::Continue
            } else {
                ResumeMode::Throw
            },
        }
    }
}

/// Byte offsets of a script's baseline frame. `sp`-relative offsets are
/// for callee, `this` and the actuals; everything else is `vp`-relative.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FrameLayout {
    pub nargs: u32,
    pub nlocals: u32,
    /// Whether `vp` is rebased past the actuals beyond the formals.
    pub rebase_vp: bool,
}

impl FrameLayout {
    pub const CALLEE: u32 = 0;
    pub const THIS: u32 = 8;
    pub const ARGS: u32 = 16;
    /// Fixed slots after the locals: env, arguments object, new.target,
    /// rval, resume word.
    const FIXED_SLOTS: u32 = 5;

    pub fn of(script: &Script) -> FrameLayout {
        FrameLayout {
            nargs: u32::from(script.nargs),
            nlocals: nlocals(script),
            rebase_vp: reads_actuals(script),
        }
    }

    /// `sp`-relative offset of actual `i`.
    pub fn arg(&self, i: u32) -> u32 {
        Self::ARGS + 8 * i
    }

    /// `vp`-relative offset of the first local.
    pub fn local_base(&self) -> u32 {
        Self::ARGS + 8 * self.nargs
    }

    pub fn local(&self, j: u32) -> u32 {
        debug_assert!(j < self.nlocals);
        self.local_base() + 8 * j
    }

    pub fn env(&self) -> u32 {
        self.local_base() + 8 * self.nlocals
    }

    pub fn args_obj(&self) -> u32 {
        self.env() + 8
    }

    pub fn new_target(&self) -> u32 {
        self.env() + 16
    }

    pub fn rval(&self) -> u32 {
        self.env() + 24
    }

    pub fn resume(&self) -> u32 {
        self.env() + 32
    }

    pub fn operand_base(&self) -> u32 {
        self.env() + 8 * Self::FIXED_SLOTS
    }

    /// `vp`-relative offset of operand-stack slot `k`.
    pub fn operand(&self, k: u32) -> u32 {
        self.operand_base() + 8 * k
    }

    /// Bytes from `vp` to the top of the frame at operand depth `depth`:
    /// what the published `top` is at a helper call.
    pub fn top(&self, depth: u32) -> u32 {
        self.operand(depth)
    }
}

/// Whether the script reads actuals beyond its formals, so the variable
/// region must start above them (`vp` rebase). The same predicate as BBV's
/// (`translate::uses_arguments`, `uses_actual_args`, mapped args), stated
/// once here for the frame contract.
pub fn reads_actuals(script: &Script) -> bool {
    script.has_mapped_args
        || script
            .parser()
            .opcodes()
            .any(|op| matches!(op, JSOp::Arguments | JSOp::Rest | JSOp::GetActualArg))
}

/// The number of local slots: one past the highest local any op names.
pub fn nlocals(script: &Script) -> u32 {
    struct Scan(u32);
    impl Scan {
        fn note(&mut self, n: u32) {
            self.0 = self.0.max(n + 1);
        }
    }
    impl OpcodeVisitor for Scan {
        fn get_local(&mut self, n: u32) {
            self.note(n);
        }
        fn set_local(&mut self, n: u32) {
            self.note(n);
        }
        fn init_lexical(&mut self, n: u32) {
            self.note(n);
        }
        fn check_lexical(&mut self, n: u32) {
            self.note(n);
        }
    }
    script.parser().visit(Scan(0)).0
}

/// One op as the depth pass sees it.
struct OpInfo {
    pc: Pc,
    op: JSOp,
    len: u32,
    nuses: u32,
    ndefs: u32,
    /// Branch targets (not the fall-through).
    targets: Vec<Pc>,
}

struct Collect {
    ops: Vec<OpInfo>,
}

impl Collect {
    fn cur(&mut self) -> &mut OpInfo {
        self.ops.last_mut().unwrap()
    }

    fn jump(&mut self, off: i32) {
        let t = self.cur().pc.branch(off);
        self.cur().targets.push(t);
    }
}

impl OpcodeVisitor for Collect {
    fn before_op(&mut self, pc: Pc, op: JSOp, nuses: usize, ndefs: usize) {
        self.ops.push(OpInfo {
            pc,
            op,
            len: op.len(),
            nuses: u32::try_from(nuses).unwrap(),
            ndefs: u32::try_from(ndefs).unwrap(),
            targets: vec![],
        });
    }
    fn goto_(&mut self, off: i32) {
        self.jump(off);
    }
    fn jump_if_false(&mut self, off: i32) {
        self.jump(off);
    }
    fn jump_if_true(&mut self, off: i32) {
        self.jump(off);
    }
    fn and_(&mut self, off: i32) {
        self.jump(off);
    }
    fn or_(&mut self, off: i32) {
        self.jump(off);
    }
    fn coalesce(&mut self, off: i32) {
        self.jump(off);
    }
    fn case_(&mut self, off: i32) {
        self.jump(off);
    }
    fn default_(&mut self, off: i32) {
        self.jump(off);
    }
    fn table_switch(&mut self, default_off: i32, _low: i32, _high: i32, offsets: &[Pc]) {
        self.jump(default_off);
        self.cur().targets.extend_from_slice(offsets);
    }
}

/// Whether control can continue to the next op (SpiderMonkey's
/// `BytecodeFallsThrough`; `Yield`/`Await` fall through, like a call).
fn falls_through(op: JSOp) -> bool {
    !matches!(
        op,
        JSOp::Goto
            | JSOp::Default
            | JSOp::Return
            | JSOp::RetRval
            | JSOp::FinalYieldRval
            | JSOp::Throw
            | JSOp::ThrowWithStack
            | JSOp::ThrowMsg
            | JSOp::ThrowSetConst
            | JSOp::TableSwitch
    )
}

/// The static operand-stack depth at every reachable pc, computed the way
/// SpiderMonkey's own `BytecodeParser::parse` does (`vm/BytecodeUtil.cpp`):
/// forward from pc 0, with the depth *before* each op.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackDepths {
    at: BTreeMap<Pc, u32>,
    /// The deepest the operand stack gets, including mid-op (after an op's
    /// inputs are popped and its outputs pushed).
    pub max: u32,
}

impl StackDepths {
    pub fn compute(script: &Script) -> Result<StackDepths, String> {
        let ops = script.parser().visit(Collect { ops: vec![] }).ops;
        let index: BTreeMap<Pc, usize> = ops.iter().enumerate().map(|(i, o)| (o.pc, i)).collect();
        let mut at: BTreeMap<Pc, u32> = BTreeMap::new();
        let mut max = 0u32;
        let mut work = vec![(Pc::new(0), 0u32)];
        let record =
            |at: &mut BTreeMap<Pc, u32>, work: &mut Vec<(Pc, u32)>, pc: Pc, d: u32| match at
                .get(&pc)
            {
                Some(&old) if old != d => Err(format!("stack depth at {pc} is both {old} and {d}")),
                Some(_) => Ok(()),
                None => {
                    at.insert(pc, d);
                    work.push((pc, d));
                    Ok(())
                }
            };
        at.insert(Pc::new(0), 0);
        while let Some((pc, d)) = work.pop() {
            let Some(&i) = index.get(&pc) else {
                return Err(format!("control reaches {pc}, which is not an op boundary"));
            };
            let o = &ops[i];
            if o.nuses > d {
                return Err(format!(
                    "{:?} at {pc} pops {} with depth {d}",
                    o.op, o.nuses
                ));
            }
            let after = d - o.nuses + o.ndefs;
            max = max.max(d).max(after);
            if o.op == JSOp::Try {
                // The handler of a try note starting just past this `Try`
                // is reached at the try's depth; a finally's with three more
                // values (exception or resume index, exception stack,
                // throwing flag).
                for n in &script.try_notes {
                    if n.start == o.pc + o.len {
                        let handler = n.start + n.length;
                        match n.kind {
                            TryNoteKind::Catch => record(&mut at, &mut work, handler, after)?,
                            TryNoteKind::Finally => {
                                max = max.max(after + 3);
                                record(&mut at, &mut work, handler, after + 3)?
                            }
                            _ => {}
                        }
                    }
                }
            }
            for &t in &o.targets {
                // `Case` does not push the switch value back when it
                // branches.
                let td = if o.op == JSOp::Case { after - 1 } else { after };
                record(&mut at, &mut work, t, td)?;
            }
            if falls_through(o.op) {
                let next = o.pc + o.len;
                if index.contains_key(&next) {
                    record(&mut at, &mut work, next, after)?;
                }
            }
        }
        Ok(StackDepths { at, max })
    }

    /// Cross-check against the try notes: SpiderMonkey records each
    /// note's operand depth, and a catch handler is entered at exactly
    /// that depth, a finally handler three deeper. A mismatch means this
    /// pass and the engine disagree about the frame, which would make
    /// every resume at or past the handler wrong.
    pub fn check_try_notes(&self, script: &Script) -> Result<(), String> {
        for n in &script.try_notes {
            let extra = match n.kind {
                TryNoteKind::Catch => 0,
                TryNoteKind::Finally => 3,
                _ => continue,
            };
            let handler = n.start + n.length;
            if let Some(d) = self.at(handler) {
                if d != n.stack_depth + extra {
                    return Err(format!(
                        "handler {handler} of a {:?} note is at depth {d}, the note says {}",
                        n.kind,
                        n.stack_depth + extra
                    ));
                }
            }
        }
        Ok(())
    }

    /// The depth before the op at `pc`, or `None` if `pc` is unreachable.
    pub fn at(&self, pc: Pc) -> Option<u32> {
        self.at.get(&pc).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (Pc, u32)> + '_ {
        self.at.iter().map(|(&p, &d)| (p, d))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::TryNote;

    fn op(o: JSOp) -> u8 {
        o as u16 as u8
    }

    fn script(bytecode: Vec<u8>, nargs: u16) -> Script {
        Script {
            bytecode,
            addr: 0,
            gcthings: Vec::new(),
            resume_offsets: Vec::new(),
            try_notes: Vec::new(),
            scope_notes: Vec::new(),
            body_scope: None,
            nargs,
            is_generator_or_async: false,
            is_class_ctor: false,
            strict: true,
            has_mapped_args: false,
        }
    }

    #[test]
    fn resume_word_roundtrip() {
        for (pc, mode) in [
            (0, ResumeMode::Continue),
            (17, ResumeMode::Throw),
            (ResumeWord::MAX_PC, ResumeMode::Continue),
            (ResumeWord::MAX_PC, ResumeMode::Throw),
        ] {
            let w = ResumeWord {
                pc: Pc::new(pc),
                mode,
            };
            assert_eq!(ResumeWord::decode(w.encode()), w);
        }
        assert_eq!(ARGC_FLAGS & 0xffff, 0);
    }

    #[test]
    fn layout_offsets() {
        // function f(a, b) { let x, y; ... }: locals 0 and 1.
        let code = vec![
            op(JSOp::Zero),
            op(JSOp::SetLocal),
            1,
            0,
            0,
            op(JSOp::Pop),
            op(JSOp::RetRval),
        ];
        let s = script(code, 2);
        let l = FrameLayout::of(&s);
        assert_eq!(l.nlocals, 2);
        assert!(!l.rebase_vp);
        assert_eq!(l.arg(1), 24);
        assert_eq!(l.local_base(), 32);
        assert_eq!(l.local(1), 40);
        assert_eq!(l.env(), 48);
        assert_eq!(l.args_obj(), 56);
        assert_eq!(l.new_target(), 64);
        assert_eq!(l.rval(), 72);
        assert_eq!(l.resume(), 80);
        assert_eq!(l.operand_base(), 88);
        assert_eq!(l.operand(2), 104);
    }

    #[test]
    fn reads_actuals_rebases_vp() {
        let s = script(vec![op(JSOp::Arguments), op(JSOp::Return)], 0);
        assert!(FrameLayout::of(&s).rebase_vp);
    }

    #[test]
    fn depths_straight_line_and_branches() {
        // @0 One; @1 JumpIfFalse +8 (-> @9); @6 Int8 42; @8 Return;
        // @9 Int8 99; @11 Return
        let code = vec![
            op(JSOp::One),
            op(JSOp::JumpIfFalse),
            8,
            0,
            0,
            0,
            op(JSOp::Int8),
            42,
            op(JSOp::Return),
            op(JSOp::Int8),
            99,
            op(JSOp::Return),
        ];
        let d = StackDepths::compute(&script(code, 0)).unwrap();
        let got: Vec<(u32, u32)> = d.iter().map(|(p, d)| (p.get(), d)).collect();
        assert_eq!(got, [(0, 0), (1, 1), (6, 0), (8, 1), (9, 0), (11, 1)]);
        assert_eq!(d.max, 1);
    }

    #[test]
    fn depths_at_catch_and_finally_handlers() {
        // Catch: @0 Try; @1 Zero; @2 Throw; @3 Nop; @4 Exception; @5 Return.
        let code = vec![
            op(JSOp::Try),
            op(JSOp::Zero),
            op(JSOp::Throw),
            op(JSOp::Nop),
            op(JSOp::Exception),
            op(JSOp::Return),
        ];
        let mut s = script(code, 0);
        s.try_notes = vec![TryNote {
            kind: TryNoteKind::Catch,
            stack_depth: 0,
            start: Pc::new(1),
            length: 3,
        }];
        let d = StackDepths::compute(&s).unwrap();
        // The handler's depth is the try note's recorded depth.
        assert_eq!(d.at(Pc::new(4)), Some(s.try_notes[0].stack_depth));
        d.check_try_notes(&s).unwrap();
        let mut wrong = s.try_notes.clone();
        wrong[0].stack_depth = 1;
        let mut s2 = script(s.bytecode.clone(), 0);
        s2.try_notes = wrong;
        assert!(d
            .check_try_notes(&s2)
            .unwrap_err()
            .contains("the note says 1"));
        assert_eq!(
            d.at(Pc::new(3)),
            None,
            "the padding after a throw is unreachable"
        );

        // Finally, entered with [exception, stack, throwing] on top.
        let code = vec![
            op(JSOp::Try),
            op(JSOp::Zero),
            op(JSOp::Throw),
            op(JSOp::Nop),
            op(JSOp::PopN),
            3,
            0,
            op(JSOp::RetRval),
        ];
        let mut s = script(code, 0);
        s.try_notes = vec![TryNote {
            kind: TryNoteKind::Finally,
            stack_depth: 0,
            start: Pc::new(1),
            length: 3,
        }];
        let d = StackDepths::compute(&s).unwrap();
        assert_eq!(d.at(Pc::new(4)), Some(3));
        d.check_try_notes(&s).unwrap();
        assert_eq!(d.max, 3);
    }

    #[test]
    fn depths_case_pops_on_branch() {
        // switch-style: @0 Zero; @1 Zero; @2 Case +6 (-> @8); @7 Pop... the
        // fall-through keeps the switch value, the branch does not.
        // @0 Zero; @1 One; @2 Case +7 (-> @9); @7 Pop; @8 RetRval; @9 RetRval
        let code = vec![
            op(JSOp::Zero),
            op(JSOp::One),
            op(JSOp::Case),
            7,
            0,
            0,
            0,
            op(JSOp::Pop),
            op(JSOp::RetRval),
            op(JSOp::RetRval),
        ];
        let d = StackDepths::compute(&script(code, 0)).unwrap();
        assert_eq!(d.at(Pc::new(7)), Some(1));
        assert_eq!(d.at(Pc::new(9)), Some(0));
    }

    #[test]
    fn depths_reject_inconsistent_merges() {
        // @0 One; @1 JumpIfTrue +6 (-> @7); @6 Zero; @7 RetRval: @7 is
        // reached at depth 0 by the branch and 1 by the fall-through.
        let code = vec![
            op(JSOp::One),
            op(JSOp::JumpIfTrue),
            6,
            0,
            0,
            0,
            op(JSOp::Zero),
            op(JSOp::RetRval),
        ];
        let e = StackDepths::compute(&script(code, 0)).unwrap_err();
        assert!(e.contains("both"), "{e}");
    }
}
