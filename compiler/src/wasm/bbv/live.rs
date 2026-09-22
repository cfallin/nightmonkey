/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Per-pc liveness of one script's frame slots -- its locals and formals.
//!
//! A raw carrier's deferred frame store is owed at an edge only if the
//! target can read the slot before writing it, and a carrier is worth
//! proposing at an edge only on the same condition. Without this every edge
//! that drops a raw local pays a canonical box and a store for it, and the
//! loop back edges of a body full of hoisted `var`s -- each written before
//! it is read on every iteration -- pay for all of them every time round
//! (box2d's kernel: 52 of the 55 IR at its outer back edge).
//!
//! Backward dataflow over the bytecode, one bit per local and per formal.
//! Sound by over-approximation: an op the scan does not model falls through
//! (the majority), a landing pad is reachable from every pc its try note
//! covers, and the ops that hand the whole frame to the runtime (the
//! resumable state machine, `arguments`, direct eval) read every slot.

use super::*;
use crate::bytecode::TryNote;

pub(super) struct ScriptLive {
    nlocals: u32,
    nargs: u32,
    words: usize,
    /// Op start pcs, ascending; `live_in` is indexed by position here.
    pcs: Vec<u32>,
    live_in: Vec<u64>,
    /// The global bindings this script reads (`GetGName`), each one a bit
    /// after the formals: a per-binding value fact (`Ctx::gcells`) is worth
    /// carrying only where a later read of the binding can consume it.
    gbids: Vec<u32>,
}

impl ScriptLive {
    /// The table for `sid`, built once per callee and shared by every
    /// segment that splices it.
    pub(super) fn shared(
        cache: &mut HashMap<ScriptId, std::rc::Rc<ScriptLive>>,
        sid: ScriptId,
        script: &Script,
        bid_of: &dyn Fn(u32) -> Option<u32>,
    ) -> std::rc::Rc<ScriptLive> {
        cache
            .entry(sid)
            .or_insert_with(|| std::rc::Rc::new(ScriptLive::build(script, bid_of)))
            .clone()
    }

    /// `bid_of` maps a `GetGName` name index of this script to its binding
    /// id (None for a name outside the syntactic-global table).
    pub(super) fn build(script: &Script, bid_of: &dyn Fn(u32) -> Option<u32>) -> ScriptLive {
        let nlocals = max_locals(script);
        let nargs = u32::from(script.nargs);
        struct GScan<'b> {
            bid_of: &'b dyn Fn(u32) -> Option<u32>,
            gbids: Vec<u32>,
        }
        impl OpcodeVisitor for GScan<'_> {
            fn get_g_name(&mut self, name_index: u32) {
                if let Some(b) = (self.bid_of)(name_index) {
                    if !self.gbids.contains(&b) {
                        self.gbids.push(b);
                    }
                }
            }
        }
        let gbids = script
            .parser()
            .visit(GScan {
                bid_of,
                gbids: Vec::new(),
            })
            .gbids;
        let nbits = nlocals + nargs + u32::try_from(gbids.len()).unwrap();
        let words = usize::try_from(nbits.div_ceil(64)).unwrap();
        let s = script.parser().visit(LiveScan {
            nlocals,
            nargs,
            words,
            pc: 0,
            ops: Vec::new(),
            flow: HashMap::default(),
            handlers: Vec::new(),
            bid_of,
            gbids: &gbids,
        });
        let n = s.ops.len();
        let pcs: Vec<u32> = s.ops.iter().map(|o| o.pc).collect();
        let index = |pc: u32| -> Option<usize> { pcs.binary_search(&pc).ok() };
        let mut succs: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (i, o) in s.ops.iter().enumerate() {
            let next = pc_index(&pcs, o.pc + o.len);
            match s.flow.get(&o.pc) {
                None => succs[i].extend(next),
                Some(Flow::Br(t)) => succs[i].extend(index(*t)),
                Some(Flow::CondBr(t)) => {
                    succs[i].extend(index(*t));
                    succs[i].extend(next);
                }
                Some(Flow::Switch(ts)) => {
                    for t in ts {
                        succs[i].extend(index(*t));
                    }
                }
                Some(Flow::Ret | Flow::Halt) => {}
            }
        }
        for &(start, end, landing) in &s.handlers {
            let Some(h) = index(landing) else {
                continue;
            };
            let lo = pcs.partition_point(|&p| p < start);
            let hi = pcs.partition_point(|&p| p < end);
            for s in &mut succs[lo..hi] {
                s.push(h);
            }
        }
        let mut live_in = vec![0u64; n * words];
        let mut changed = true;
        let mut out = vec![0u64; words];
        while changed {
            changed = false;
            for i in (0..n).rev() {
                out.iter_mut().for_each(|w| *w = 0);
                for &j in &succs[i] {
                    for w in 0..words {
                        out[w] |= live_in[j * words + w];
                    }
                }
                let o = &s.ops[i];
                for w in 0..words {
                    let v = o.uses[w] | (out[w] & !o.defs[w]);
                    if live_in[i * words + w] != v {
                        live_in[i * words + w] = v;
                        changed = true;
                    }
                }
            }
        }
        ScriptLive {
            nlocals,
            nargs,
            words,
            pcs,
            live_in,
            gbids,
        }
    }

    /// Whether binding `bid` may be read at or after `pc`: false for a
    /// binding this script never reads.
    pub(super) fn gcell_live(&self, pc: u32, bid: u32) -> bool {
        match self.gbids.iter().position(|&b| b == bid) {
            Some(k) => self.bit(pc, self.nlocals + self.nargs + u32::try_from(k).unwrap()),
            None => false,
        }
    }

    fn bit(&self, pc: u32, bit: u32) -> bool {
        let Some(i) = pc_index(&self.pcs, pc) else {
            return true;
        };
        let w = usize::try_from(bit / 64).unwrap();
        w >= self.words || self.live_in[i * self.words + w] & (1u64 << (bit % 64)) != 0
    }

    /// Whether local `l` may be read at or after `pc` before being written.
    /// A pc that is not an op boundary answers yes.
    pub(super) fn local_live(&self, pc: u32, l: u32) -> bool {
        l >= self.nlocals || self.bit(pc, l)
    }

    /// `local_live` for formal `a`.
    pub(super) fn arg_live(&self, pc: u32, a: u32) -> bool {
        self.bit(pc, self.nlocals + a)
    }
}

fn pc_index(pcs: &[u32], pc: u32) -> Option<usize> {
    pcs.binary_search(&pc).ok()
}

enum Flow {
    Br(u32),
    CondBr(u32),
    Switch(Vec<u32>),
    Ret,
    Halt,
}

struct OpRec {
    pc: u32,
    len: u32,
    uses: Vec<u64>,
    defs: Vec<u64>,
}

struct LiveScan<'b> {
    nlocals: u32,
    nargs: u32,
    words: usize,
    pc: u32,
    ops: Vec<OpRec>,
    flow: HashMap<u32, Flow>,
    /// (covered start, covered end, landing pc).
    handlers: Vec<(u32, u32, u32)>,
    bid_of: &'b dyn Fn(u32) -> Option<u32>,
    gbids: &'b [u32],
}

impl LiveScan<'_> {
    fn cur(&mut self) -> &mut OpRec {
        self.ops.last_mut().unwrap()
    }
    fn set_bit(v: &mut [u64], bit: u32) {
        let w = usize::try_from(bit / 64).unwrap();
        if w < v.len() {
            v[w] |= 1u64 << (bit % 64);
        }
    }
    fn use_local(&mut self, l: u32) {
        let o = self.cur();
        Self::set_bit(&mut o.uses, l);
    }
    fn def_local(&mut self, l: u32) {
        let o = self.cur();
        Self::set_bit(&mut o.defs, l);
    }
    fn use_arg(&mut self, a: u32) {
        let bit = self.nlocals + a;
        let o = self.cur();
        Self::set_bit(&mut o.uses, bit);
    }
    fn def_arg(&mut self, a: u32) {
        let bit = self.nlocals + a;
        let o = self.cur();
        Self::set_bit(&mut o.defs, bit);
    }
    fn use_all_args(&mut self) {
        for a in 0..self.nargs {
            self.use_arg(a);
        }
    }
    fn use_all(&mut self) {
        let o = self.cur();
        o.uses.iter_mut().for_each(|w| *w = !0);
    }
    fn set(&mut self, f: Flow) {
        self.flow.insert(self.pc, f);
    }
    fn target(&self, off: i32) -> u32 {
        Pc::new(self.pc).branch(off).get()
    }
}

impl OpcodeVisitor for LiveScan<'_> {
    fn get_g_name(&mut self, name_index: u32) {
        if let Some(b) = (self.bid_of)(name_index) {
            if let Some(k) = self.gbids.iter().position(|&x| x == b) {
                let bit = self.nlocals + self.nargs + u32::try_from(k).unwrap();
                let o = self.cur();
                Self::set_bit(&mut o.uses, bit);
            }
        }
    }
    fn before_op(&mut self, pc: Pc, op: JSOp, _u: usize, _d: usize) {
        self.pc = pc.get();
        self.ops.push(OpRec {
            pc: self.pc,
            len: op.len(),
            uses: vec![0; self.words],
            defs: vec![0; self.words],
        });
    }
    fn try_note(&mut self, _pc: Pc, note: &TryNote) {
        if matches!(note.kind, TryNoteKind::Catch | TryNoteKind::Finally) {
            let end = note.start.get() + note.length;
            self.handlers.push((note.start.get(), end, end));
        }
    }

    fn get_local(&mut self, l: u32) {
        self.use_local(l);
    }
    fn check_lexical(&mut self, l: u32) {
        self.use_local(l);
    }
    fn set_local(&mut self, l: u32) {
        self.def_local(l);
    }
    fn init_lexical(&mut self, l: u32) {
        self.def_local(l);
    }
    fn get_arg(&mut self, a: u16) {
        self.use_arg(u32::from(a));
    }
    fn get_frame_arg(&mut self, a: u16) {
        self.use_arg(u32::from(a));
    }
    fn set_arg(&mut self, a: u16) {
        self.def_arg(u32::from(a));
    }
    fn arguments(&mut self) {
        self.use_all_args();
    }
    fn rest(&mut self) {
        self.use_all_args();
    }
    fn get_actual_arg(&mut self) {
        self.use_all_args();
    }
    fn arguments_length(&mut self) {
        self.use_all_args();
    }
    // The whole frame goes to the runtime.
    fn generator(&mut self) {
        self.use_all();
    }
    fn initial_yield(&mut self, _r: u32) {
        self.use_all();
    }
    fn yield_(&mut self, _r: u32) {
        self.use_all();
    }
    fn await_(&mut self, _r: u32) {
        self.use_all();
    }
    fn resume(&mut self) {
        self.use_all();
    }
    fn after_yield(&mut self, _i: u32) {
        self.use_all();
    }
    fn eval(&mut self, _n: u16) {
        self.use_all();
    }
    fn strict_eval(&mut self, _n: u16) {
        self.use_all();
    }
    fn spread_eval(&mut self) {
        self.use_all();
    }
    fn strict_spread_eval(&mut self) {
        self.use_all();
    }
    fn debugger(&mut self) {
        self.use_all();
    }
    fn force_interpreter(&mut self) {
        self.use_all();
    }
    fn get_aliased_debug_var(&mut self, _h: u16, _s: u32) {
        self.use_all();
    }

    fn goto_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::Br(t));
    }
    fn default_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::Br(t));
    }
    fn jump_if_false(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn jump_if_true(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn and_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn or_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn coalesce(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn case_(&mut self, off: i32) {
        let t = self.target(off);
        self.set(Flow::CondBr(t));
    }
    fn table_switch(&mut self, default_off: i32, _low: i32, _high: i32, offsets: &[Pc]) {
        let mut ts: Vec<u32> = offsets.iter().map(|p| p.get()).collect();
        ts.push(self.target(default_off));
        self.set(Flow::Switch(ts));
    }
    fn return_(&mut self) {
        self.set(Flow::Ret);
    }
    fn ret_rval(&mut self) {
        self.set(Flow::Ret);
    }
    fn throw_(&mut self) {
        self.set(Flow::Halt);
    }
    fn throw_with_stack(&mut self) {
        self.set(Flow::Halt);
    }
    fn throw_msg(&mut self, _n: u8) {
        self.set(Flow::Halt);
    }
    fn throw_set_const(&mut self, _n: u32) {
        self.set(Flow::Halt);
    }
}
