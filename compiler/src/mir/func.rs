//! A MIR function: blocks with typed params, instructions, values, roots,
//! and the side tables (attachments, prediction witnesses).
//!
//! A block's instructions end in exactly one terminator; the validator,
//! not the data structure, enforces that, so a malformed function can be
//! built (and printed) to test the validator on it.
//!
//! **Terminator outputs are the success block's params.** A guard's
//! refined value, a call's result, a check's fact: none is an instruction
//! result. The successor edge names, per target param, either an ordinary
//! value or output `k` of the terminator ([`EdgeArg::Out`]). That keeps
//! "an output exists only where the op succeeded" structural, and makes
//! weakening on a fence edge (§4.2) nothing more than a param of a weaker
//! type.

use std::collections::BTreeMap;

use crate::ids::{Pc, ScriptId, Site, SlotIndex};
use crate::mir::entity::{AttachId, Block, EntityMap, EntityVec, Inst, Value};
use crate::mir::ops::{Opcode, SuccRole};
use crate::mir::types::{KillPattern, Type};

/// The JS frame an exit writes and an onramp reads (§5): its size is the
/// script's, not the MIR's.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct FrameShape {
    pub formals: u32,
    pub locals: u32,
    /// Operand-stack depth at each pc an exit or onramp names.
    pub depths: BTreeMap<Pc, u32>,
}

impl FrameShape {
    /// Operand count of an exit at `pc`: `this`, formals, locals, rval,
    /// stack.
    pub fn exit_arity(&self, pc: Pc) -> Option<usize> {
        let d = *self.depths.get(&pc)?;
        Some(2 + (self.formals + self.locals + d) as usize)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum ValueDef {
    /// Param `n` of a block.
    Param(Block, u32),
    /// Result `n` of a (non-terminator) instruction.
    Result(Inst, u32),
    /// Allocated but not defined: the parser pads gaps in the text's
    /// numbering with these, and passes may leave them behind.
    #[default]
    Unused,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ValueData {
    pub def: ValueDef,
    pub ty: Type,
}

/// One argument on a successor edge.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum EdgeArg {
    Value(Value),
    /// Output `k` of the terminator.
    Out(u32),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Edge {
    pub block: Block,
    pub args: Vec<EdgeArg>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct InstData {
    pub op: Opcode,
    pub args: Vec<Value>,
    pub results: Vec<Value>,
    /// One per `op.roles()`, in order.
    pub succs: Vec<Edge>,
    pub attach: Option<AttachId>,
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct BlockData {
    pub params: Vec<Value>,
    pub insts: Vec<Inst>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum RootKind {
    /// Function entry: `callee`, `this`, formals.
    Entry,
    /// A loop header's onramp entry block `O` (§5.2): the full frame
    /// state at `pc`.
    Onramp(Pc),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Root {
    pub kind: RootKind,
    pub block: Block,
}

/// A declared loop (§5.2): its header and its canonical preheader `P`,
/// the header's only predecessor from outside the loop and the block LICM
/// hoists to. The loop's body is every block that reaches one of its
/// latches without passing through the header; that is well-defined even
/// where onramps make the CFG irreducible (§5.4).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LoopDecl {
    pub header: Block,
    pub preheader: Block,
}

/// What the lowering needs from the analysis and the translator's site
/// tables that is neither an operand nor derivable from operand types.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Attachment {
    /// The originating bytecode op, for diagnostics only.
    pub site: Option<Site>,
    pub ic_cell: Option<u32>,
    pub call_cell: Option<u32>,
    pub slot: Option<SlotIndex>,
    /// The typed-site field mask.
    pub field_mask: Option<u32>,
    /// Candidate call targets, for later inlining.
    pub targets: Vec<ScriptId>,
}

/// A prediction witness (§4.5): what likelier says the op may invalidate.
/// Validator-only: never read by lowering or optimization decisions.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct Witness {
    pub may_kill: KillPattern,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Func {
    pub script: ScriptId,
    pub frame: FrameShape,
    pub blocks: EntityVec<Block, BlockData>,
    /// The blocks that make up the function, in print order. Blocks not in
    /// the layout (parser padding, deleted blocks) are not part of it.
    pub layout: Vec<Block>,
    pub insts: EntityVec<Inst, InstData>,
    pub values: EntityVec<Value, ValueData>,
    pub roots: Vec<Root>,
    pub loops: Vec<LoopDecl>,
    pub attachments: EntityVec<AttachId, Attachment>,
    pub witnesses: EntityMap<Inst, Option<Witness>>,
}

impl Func {
    pub fn new(script: ScriptId, frame: FrameShape) -> Func {
        Func {
            script,
            frame,
            blocks: EntityVec::new(),
            layout: vec![],
            insts: EntityVec::new(),
            values: EntityVec::new(),
            roots: vec![],
            loops: vec![],
            attachments: EntityVec::new(),
            witnesses: EntityMap::new(),
        }
    }

    pub fn add_block(&mut self) -> Block {
        let b = self.blocks.push(BlockData::default());
        self.layout.push(b);
        b
    }

    pub fn add_param(&mut self, b: Block, ty: Type) -> Value {
        let n = u32::try_from(self.blocks[b].params.len()).unwrap();
        let v = self.values.push(ValueData {
            def: ValueDef::Param(b, n),
            ty,
        });
        self.blocks[b].params.push(v);
        v
    }

    /// Append an instruction with results of the given types.
    pub fn add_inst(
        &mut self,
        b: Block,
        op: Opcode,
        args: Vec<Value>,
        result_tys: &[Type],
        succs: Vec<Edge>,
    ) -> (Inst, Vec<Value>) {
        let inst = self.insts.push(InstData {
            op,
            args,
            results: vec![],
            succs,
            attach: None,
        });
        let results: Vec<Value> = result_tys
            .iter()
            .enumerate()
            .map(|(i, &ty)| {
                self.values.push(ValueData {
                    def: ValueDef::Result(inst, i as u32),
                    ty,
                })
            })
            .collect();
        self.insts[inst].results = results.clone();
        self.blocks[b].insts.push(inst);
        (inst, results)
    }

    pub fn ty(&self, v: Value) -> Type {
        self.values[v].ty
    }

    /// The block's terminator, if its last instruction is one.
    pub fn terminator(&self, b: Block) -> Option<Inst> {
        let &last = self.blocks[b].insts.last()?;
        self.insts[last].op.is_terminator().then_some(last)
    }

    /// Successor edges with their roles.
    pub fn succ_edges(&self, inst: Inst) -> impl Iterator<Item = (SuccRole, &Edge)> {
        let data = &self.insts[inst];
        data.op.roles().into_iter().zip(data.succs.iter())
    }

    pub fn succs(&self, b: Block) -> Vec<Block> {
        match self.terminator(b) {
            Some(t) => self.insts[t].succs.iter().map(|e| e.block).collect(),
            None => vec![],
        }
    }

    pub fn witness(&self, inst: Inst) -> Option<Witness> {
        self.witnesses[inst]
    }
}
