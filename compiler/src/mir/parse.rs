//! Parser for the MIR text format (see `print`). `parse(print(m)) == m`
//! for every module the parser itself produced; that is what the fixture
//! tests check.
//!
//! Hand-written text may leave out what the printer leaves out: result
//! types the op's rule infers, and atom declarations (atoms are interned
//! at first use). Value and block numbers are taken literally (`v7` is
//! value 7); gaps are padded, so hand-written numbering need not be dense.
//!
//! The parser checks only what it must to build the function: names
//! resolve, a value is defined once, output annotations on an edge agree
//! with the target block's header, results can be typed. Everything else
//! -- arity, dominance, operand types, fences -- is the validator's, so
//! that negative validator tests can be written as text.

use std::collections::BTreeMap;

use crate::ids::{EnvSlot, JsString, LayoutKey, Pc, RegionRoot, ScriptId, Site, SlotIndex};
use crate::mir::entity::*;
use crate::mir::func::*;
use crate::mir::module::*;
use crate::mir::ops::*;
use crate::mir::print::{mnemonic, type_str_in};
use crate::mir::types::*;
use crate::opsem::{TaKind, ValueRange};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParseError {
    pub line: usize,
    pub msg: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}: {}", self.line, self.msg)
    }
}

type PResult<T> = Result<T, ParseError>;

#[derive(Clone, PartialEq, Debug)]
enum Tok {
    Word(String),
    Str(Vec<u16>),
    Punct(&'static str),
}

struct Lexed {
    tok: Tok,
    line: usize,
}

fn lex(src: &str) -> PResult<Vec<Lexed>> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = vec![];
    let mut i = 0;
    let mut line = 1;
    let is_word = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '$';
    while i < chars.len() {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            i += 1;
        } else if c.is_whitespace() {
            i += 1;
        } else if c == ';' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '-' && chars.get(i + 1) == Some(&'>') {
            out.push(Lexed {
                tok: Tok::Punct("->"),
                line,
            });
            i += 2;
        } else if is_word(c) || (c == '-' && chars.get(i + 1).is_some_and(|&d| is_word(d))) {
            let start = i;
            let numeric = c.is_ascii_digit() || c == '-';
            i += 1;
            while i < chars.len() {
                let d = chars[i];
                let exp_sign = numeric
                    && (d == '-' || d == '+')
                    && matches!(chars[i - 1], 'e' | 'E')
                    && !chars[start..i].contains(&'x');
                if is_word(d) || exp_sign {
                    i += 1;
                } else {
                    break;
                }
            }
            out.push(Lexed {
                tok: Tok::Word(chars[start..i].iter().collect()),
                line,
            });
        } else if c == '"' {
            i += 1;
            let mut s: Vec<u16> = vec![];
            loop {
                let Some(&d) = chars.get(i) else {
                    return Err(ParseError {
                        line,
                        msg: "unterminated string".into(),
                    });
                };
                i += 1;
                match d {
                    '"' => break,
                    '\\' => {
                        let e = chars.get(i).copied().unwrap_or('"');
                        i += 1;
                        match e {
                            'u' => {
                                if chars.get(i) != Some(&'{') {
                                    return Err(ParseError {
                                        line,
                                        msg: "expected `{` after \\u".into(),
                                    });
                                }
                                let end = (i..chars.len()).find(|&j| chars[j] == '}').ok_or(
                                    ParseError {
                                        line,
                                        msg: "unterminated \\u{".into(),
                                    },
                                )?;
                                let hex: String = chars[i + 1..end].iter().collect();
                                let n = u16::from_str_radix(&hex, 16).map_err(|e| ParseError {
                                    line,
                                    msg: format!("bad \\u escape: {e}"),
                                })?;
                                s.push(n);
                                i = end + 1;
                            }
                            other => {
                                let mut buf = [0u16; 2];
                                s.extend_from_slice(other.encode_utf16(&mut buf));
                            }
                        }
                    }
                    '\n' => {
                        return Err(ParseError {
                            line,
                            msg: "newline in string".into(),
                        })
                    }
                    other => {
                        let mut buf = [0u16; 2];
                        s.extend_from_slice(other.encode_utf16(&mut buf));
                    }
                }
            }
            out.push(Lexed {
                tok: Tok::Str(s),
                line,
            });
        } else {
            let p = match c {
                '(' => "(",
                ')' => ")",
                '[' => "[",
                ']' => "]",
                '{' => "{",
                '}' => "}",
                ',' => ",",
                ':' => ":",
                '=' => "=",
                '@' => "@",
                '!' => "!",
                '%' => "%",
                '*' => "*",
                _ => {
                    return Err(ParseError {
                        line,
                        msg: format!("unexpected character `{c}`"),
                    })
                }
            };
            out.push(Lexed {
                tok: Tok::Punct(p),
                line,
            });
            i += 1;
        }
    }
    Ok(out)
}

/// An edge-argument annotation to check once every block header is known.
struct OutNote {
    line: usize,
    block: Block,
    pos: usize,
    param: Value,
    ty: Type,
}

/// Per-function parse state: value ids are the text's numbers.
struct FuncState {
    func: Func,
    /// `None` until defined; `Some(None)` while a result awaits inference.
    defined: Vec<Option<Option<Type>>>,
    block_defined: Vec<bool>,
    notes: Vec<OutNote>,
    /// Values used, with the line of the first use, to report undefined ones.
    uses: BTreeMap<Value, usize>,
}

impl FuncState {
    fn value(&mut self, n: u32, line: usize) -> Value {
        let v = Value::from_u32(n);
        while self.func.values.len() <= n as usize {
            self.func.values.push(ValueData {
                def: ValueDef::Unused,
                ty: Type::VAL_TOP,
            });
            self.defined.push(None);
        }
        self.uses.entry(v).or_insert(line);
        v
    }

    fn block(&mut self, n: u32) -> Block {
        while self.func.blocks.len() <= n as usize {
            self.func.blocks.push(BlockData::default());
            self.block_defined.push(false);
        }
        Block::from_u32(n)
    }

    fn define(&mut self, v: Value, def: ValueDef, ty: Option<Type>, line: usize) -> PResult<()> {
        if self.defined[v.as_u32() as usize].is_some() {
            return Err(ParseError {
                line,
                msg: format!("{v} is defined twice"),
            });
        }
        self.defined[v.as_u32() as usize] = Some(ty);
        self.func.values[v].def = def;
        if let Some(t) = ty {
            self.func.values[v].ty = t;
        }
        Ok(())
    }
}

struct Parser {
    toks: Vec<Lexed>,
    pos: usize,
    m: Module,
}

fn num_word<T: std::str::FromStr>(w: &str) -> Option<T> {
    w.parse().ok()
}

/// `<prefix><digits>`, e.g. `v12` with prefix `v`.
fn prefixed(w: &str, prefix: &str) -> Option<u32> {
    let rest = w.strip_prefix(prefix)?;
    if rest.is_empty() || !rest.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    rest.parse().ok()
}

impl Parser {
    fn line(&self) -> usize {
        self.toks
            .get(self.pos)
            .or(self.toks.last())
            .map_or(1, |t| t.line)
    }

    fn err<T>(&self, msg: impl Into<String>) -> PResult<T> {
        Err(ParseError {
            line: self.line(),
            msg: msg.into(),
        })
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|t| &t.tok)
    }

    fn peek_at(&self, k: usize) -> Option<&Tok> {
        self.toks.get(self.pos + k).map(|t| &t.tok)
    }

    fn at_punct(&self, p: &str) -> bool {
        matches!(self.peek(), Some(Tok::Punct(q)) if *q == p)
    }

    fn at_word(&self, w: &str) -> bool {
        matches!(self.peek(), Some(Tok::Word(x)) if x == w)
    }

    fn eat_punct(&mut self, p: &str) -> bool {
        if self.at_punct(p) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_word(&mut self, w: &str) -> bool {
        if self.at_word(w) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_punct(&mut self, p: &str) -> PResult<()> {
        if self.eat_punct(p) {
            Ok(())
        } else {
            self.err(format!("expected `{p}`, found {}", self.describe()))
        }
    }

    fn expect_word(&mut self, w: &str) -> PResult<()> {
        if self.eat_word(w) {
            Ok(())
        } else {
            self.err(format!("expected `{w}`, found {}", self.describe()))
        }
    }

    fn describe(&self) -> String {
        match self.peek() {
            None => "end of input".into(),
            Some(Tok::Word(w)) => format!("`{w}`"),
            Some(Tok::Str(_)) => "a string".into(),
            Some(Tok::Punct(p)) => format!("`{p}`"),
        }
    }

    fn word(&mut self) -> PResult<String> {
        match self.peek() {
            Some(Tok::Word(w)) => {
                let w = w.clone();
                self.pos += 1;
                Ok(w)
            }
            _ => self.err(format!("expected a word, found {}", self.describe())),
        }
    }

    fn int<T: std::str::FromStr>(&mut self) -> PResult<T> {
        let w = self.word()?;
        let parsed = if let Some(hex) = w.strip_prefix("0x") {
            u64::from_str_radix(hex, 16)
                .ok()
                .and_then(|n| n.to_string().parse().ok())
        } else {
            num_word(&w)
        };
        match parsed {
            Some(n) => Ok(n),
            None => {
                self.pos -= 1;
                self.err(format!("expected an integer, found `{w}`"))
            }
        }
    }

    fn prefixed(&mut self, prefix: &str, what: &str) -> PResult<u32> {
        let w = self.word()?;
        match prefixed(&w, prefix) {
            Some(n) => Ok(n),
            None => {
                self.pos -= 1;
                self.err(format!("expected {what} (`{prefix}N`), found `{w}`"))
            }
        }
    }

    fn at_prefixed(&self, prefix: &str) -> bool {
        matches!(self.peek(), Some(Tok::Word(w)) if prefixed(w, prefix).is_some())
    }

    fn f64_bits(&mut self) -> PResult<u64> {
        let w = self.word()?;
        match w.parse::<f64>() {
            Ok(x) => Ok(x.to_bits()),
            Err(_) => {
                self.pos -= 1;
                self.err(format!("expected a number, found `{w}`"))
            }
        }
    }

    fn atom(&mut self) -> PResult<AtomId> {
        let s: Vec<u16> = match self.peek() {
            Some(Tok::Str(s)) => s.clone(),
            Some(Tok::Word(w)) => w.encode_utf16().collect(),
            _ => return self.err(format!("expected a name, found {}", self.describe())),
        };
        self.pos += 1;
        Ok(self.m.intern_atom(&s))
    }

    /// A descriptive name (fuses, natives): spelled like an atom, not
    /// interned as one.
    fn string(&mut self) -> PResult<String> {
        let s = match self.peek() {
            Some(Tok::Str(s)) => JsString::from_chars(s.clone()).to_string(),
            Some(Tok::Word(w)) => w.clone(),
            _ => return self.err(format!("expected a name, found {}", self.describe())),
        };
        self.pos += 1;
        Ok(s)
    }

    fn layout_key(&mut self) -> PResult<LayoutKey> {
        Ok(LayoutKey::new(self.prefixed("L", "a layout key")?))
    }

    fn keys(&mut self) -> PResult<KeyRange> {
        let w = self.word()?;
        let parse1 = |s: &str| prefixed(s, "L").map(LayoutKey::new);
        let r = match w.split_once("..") {
            Some((a, b)) => parse1(a).zip(parse1(b)).map(|(lo, hi)| KeyRange { lo, hi }),
            None => parse1(&w).map(KeyRange::one),
        };
        match r {
            Some(r) if r.lo <= r.hi => Ok(r),
            _ => {
                self.pos -= 1;
                self.err(format!(
                    "expected a layout key range (`L3` or `L3..L5`), found `{w}`"
                ))
            }
        }
    }

    fn script(&mut self) -> PResult<ScriptId> {
        Ok(ScriptId::new(self.prefixed("s", "a script")?))
    }

    fn tags(&mut self) -> PResult<TagSet> {
        self.expect_punct("{")?;
        let mut t = TagSet::NONE;
        while !self.eat_punct("}") {
            let w = self.word()?;
            match TagSet::NAMES.iter().find(|(n, _)| *n == w) {
                Some((_, bit)) => t = t.union(*bit),
                None => return self.err(format!("unknown tag `{w}`")),
            }
            if !self.eat_punct(",") {
                self.expect_punct("}")?;
                break;
            }
        }
        Ok(t)
    }

    fn ta_kind(&mut self) -> PResult<TaKind> {
        let w = self.word()?;
        match TaKind::ALL.iter().find(|k| format!("{k:?}") == w) {
            Some(k) => Ok(*k),
            None => self.err(format!("unknown typed-array kind `{w}`")),
        }
    }

    fn kind(&mut self) -> PResult<ObjKind> {
        let w = self.word()?;
        Ok(match w.as_str() {
            "Any" => ObjKind::Any,
            "Native" => ObjKind::Native,
            "Plain" => ObjKind::Plain,
            "Array" => ObjKind::Array,
            "Arguments" => ObjKind::Arguments,
            "Env" => ObjKind::Env,
            "Function" => {
                if self.eat_punct("(") {
                    let s = self.script()?;
                    self.expect_punct(")")?;
                    ObjKind::Function(Some(s))
                } else {
                    ObjKind::Function(None)
                }
            }
            "TypedArray" => {
                self.expect_punct("(")?;
                let k = self.ta_kind()?;
                self.expect_punct(")")?;
                ObjKind::TypedArray(k)
            }
            _ => {
                self.pos -= 1;
                return self.err(format!("unknown object kind `{w}`"));
            }
        })
    }

    fn paren_u32(&mut self) -> PResult<u32> {
        self.expect_punct("(")?;
        let n = self.int()?;
        self.expect_punct(")")?;
        Ok(n)
    }

    fn obj_info(&mut self) -> PResult<ObjInfo> {
        let mut o = ObjInfo::TOP;
        if !self.eat_punct("{") {
            return Ok(o);
        }
        if self.eat_punct("}") {
            return Ok(o);
        }
        loop {
            if self.at_prefixed("S") {
                o.singleton = Some(SnapObj::from_u32(self.prefixed("S", "a snapshot object")?));
            } else if matches!(self.peek(), Some(Tok::Word(w)) if w.starts_with('L') && w[1..].starts_with(|c: char| c.is_ascii_digit()))
            {
                let keys = self.keys()?;
                let types = self.eat_word("types");
                let state = if self.eat_word("prefix") {
                    LayoutState::Prefix(self.paren_u32()?)
                } else if self.eat_word("constructing") {
                    LayoutState::Constructing(self.paren_u32()?)
                } else {
                    LayoutState::Published
                };
                o.layout = Some(LayoutClaim { keys, types, state });
            } else {
                o.kind = self.kind()?;
            }
            if !self.eat_punct(",") {
                self.expect_punct("}")?;
                return Ok(o);
            }
        }
    }

    fn str_info(&mut self) -> PResult<StrInfo> {
        if !self.eat_punct("{") {
            return Ok(StrInfo::TOP);
        }
        let atom = self.atom()?;
        self.expect_punct("}")?;
        Ok(StrInfo { atom: Some(atom) })
    }

    fn range_pair(&mut self) -> PResult<(i64, i64)> {
        self.expect_punct("[")?;
        let lo = self.int()?;
        self.expect_punct(",")?;
        let hi = self.int()?;
        self.expect_punct("]")?;
        if lo > hi {
            return self.err(format!("empty range [{lo},{hi}]"));
        }
        Ok((lo, hi))
    }

    /// Numeric qualifiers (and, for `val`, object/string ones).
    fn quals(
        &mut self,
        num: &mut NumInfo,
        mut obj: Option<&mut ObjInfo>,
        mut str: Option<&mut StrInfo>,
    ) -> PResult<()> {
        loop {
            let next_is_brace = matches!(self.peek_at(1), Some(Tok::Punct("{")));
            if self.eat_word("range") {
                let (lo, hi) = self.range_pair()?;
                num.range = Some(ValueRange::new(lo, hi));
            } else if self.eat_word("integral") {
                num.integral = true;
            } else if self.eat_word("nonegz") {
                num.may_neg_zero = false;
            } else if self.eat_word("nonan") {
                num.may_nan = false;
            } else if self.at_word("obj") && next_is_brace && obj.is_some() {
                self.pos += 1;
                let o = self.obj_info()?;
                if let Some(slot) = obj.as_deref_mut() {
                    *slot = o;
                }
            } else if self.at_word("str") && next_is_brace && str.is_some() {
                self.pos += 1;
                let s = self.str_info()?;
                if let Some(slot) = str.as_deref_mut() {
                    *slot = s;
                }
            } else {
                return Ok(());
            }
        }
    }

    fn ty(&mut self) -> PResult<Type> {
        let w = self.word()?;
        Ok(match w.as_str() {
            "val" => {
                let tags = if self.at_punct("{") {
                    self.tags()?
                } else {
                    TagSet::ALL
                };
                let (mut num, mut obj, mut str) = (NumInfo::TOP, ObjInfo::TOP, StrInfo::TOP);
                self.quals(&mut num, Some(&mut obj), Some(&mut str))?;
                Type::Val(VSet::new(tags, num, obj, str))
            }
            "i32" | "int" => {
                let full = if w == "i32" { IRange::I32 } else { IRange::INT };
                let r = if self.at_punct("[") {
                    let (lo, hi) = self.range_pair()?;
                    IRange::new(lo, hi)
                } else {
                    full
                };
                if !full.contains(&r) {
                    return self.err(format!(
                        "{w} range [{},{}] exceeds the representation",
                        r.lo, r.hi
                    ));
                }
                if w == "i32" {
                    Type::I32(r)
                } else {
                    Type::Int(r)
                }
            }
            "f64" => {
                let mut num = NumInfo::TOP;
                self.quals(&mut num, None, None)?;
                Type::F64(num)
            }
            "bool" => Type::Bool,
            "obj" => Type::Obj(self.obj_info()?),
            "str" => Type::Str(self.str_info()?),
            "raw.elements" => Type::Raw(RawKind::Elements),
            "raw.slots" => Type::Raw(RawKind::Slots),
            "raw.tadata" => Type::Raw(RawKind::TaData),
            "w32" => Type::W32,
            "w64" => Type::W64,
            "fact.fuse" | "fact.binding" | "fact.native" => {
                self.expect_punct("(")?;
                let k = match w.as_str() {
                    "fact.fuse" => FactKind::Fuse(FuseId::from_u32(self.prefixed("F", "a fuse")?)),
                    "fact.binding" => {
                        FactKind::Binding(BindingId::from_u32(self.prefixed("G", "a binding")?))
                    }
                    _ => {
                        FactKind::NativeIntact(NativeId::from_u32(self.prefixed("N", "a native")?))
                    }
                };
                self.expect_punct(")")?;
                Type::Fact(k)
            }
            _ => {
                self.pos -= 1;
                return self.err(format!("expected a type, found `{w}`"));
            }
        })
    }

    fn kill_pattern(&mut self) -> PResult<KillPattern> {
        self.expect_punct("{")?;
        let mut p = KillPattern::NONE;
        while !self.at_punct("}") {
            if self.eat_word("in") {
                p.keys = Some(self.keys()?);
                continue;
            }
            let w = self.word()?;
            match KillSet::NAMES.iter().find(|(n, _)| *n == w) {
                Some((_, k)) => p.set = p.set.union(*k),
                None => return self.err(format!("unknown kill class `{w}`")),
            }
            self.eat_punct(",");
        }
        self.expect_punct("}")?;
        Ok(p)
    }

    // --- module ---------------------------------------------------------

    fn root_or_region(&mut self) -> PResult<Option<RegionRoot>> {
        self.expect_punct("(")?;
        let r = if self.eat_punct("*") {
            None
        } else {
            Some(RegionRoot::new(self.prefixed("r", "a region root")?))
        };
        self.expect_punct(")")?;
        Ok(r)
    }

    fn region(&mut self) -> PResult<Region> {
        let w = self.word()?;
        Ok(match w.as_str() {
            "field" => {
                self.expect_punct("(")?;
                let keys = if self.eat_punct("*") {
                    None
                } else {
                    Some(self.keys()?)
                };
                self.expect_punct(",")?;
                let name = self.atom()?;
                self.expect_punct(")")?;
                Region::Field { name, keys }
            }
            "elements" => Region::Elements(self.root_or_region()?),
            "arraylength" => Region::ArrayLength(self.root_or_region()?),
            "tadata" => {
                self.expect_punct("(")?;
                let k = self.ta_kind()?;
                self.expect_punct(")")?;
                Region::TypedArrayData(k)
            }
            "talength" => Region::TypedArrayLength,
            "global" => {
                self.expect_punct("(")?;
                let b = BindingId::from_u32(self.prefixed("G", "a binding")?);
                self.expect_punct(")")?;
                Region::Global(b)
            }
            "env" => Region::Env(EnvSlot::new(self.paren_u32()?)),
            "unknown" => Region::Unknown,
            _ => {
                self.pos -= 1;
                return self.err(format!("unknown region `{w}`"));
            }
        })
    }

    /// `<prefix>N =`, checking that ids are declared densely in order.
    fn decl_id(&mut self, prefix: &str, what: &str, next: usize) -> PResult<()> {
        let n = self.prefixed(prefix, what)?;
        if n as usize != next {
            return self.err(format!(
                "{what} {prefix}{n} declared out of order (expected {prefix}{next})"
            ));
        }
        self.expect_punct("=")
    }

    fn module_decls(&mut self) -> PResult<()> {
        self.expect_punct("{")?;
        while !self.eat_punct("}") {
            let w = self.word()?;
            match w.as_str() {
                "atom" => {
                    self.atom()?;
                }
                "layout" => {
                    let k = self.layout_key()?;
                    self.expect_punct("=")?;
                    self.expect_punct("{")?;
                    let mut fields = vec![];
                    while !self.eat_punct("}") {
                        let name = self.atom()?;
                        self.expect_punct(":")?;
                        let claim = self.ty()?;
                        fields.push(FieldDef { name, claim });
                        if !self.eat_punct(",") {
                            self.expect_punct("}")?;
                            break;
                        }
                    }
                    let elements = if self.eat_word("elements") {
                        Some(RegionRoot::new(self.prefixed("r", "a region root")?))
                    } else {
                        None
                    };
                    if self
                        .m
                        .layouts
                        .insert(k, Layout { fields, elements })
                        .is_some()
                    {
                        return self.err(format!("layout L{k} declared twice"));
                    }
                }
                "snap" => {
                    self.decl_id("S", "snapshot object", self.m.snap_objs.len())?;
                    let kind = self.kind()?;
                    self.m.snap_objs.push(SnapObjDef { kind });
                }
                "fuse" => {
                    self.decl_id("F", "fuse", self.m.fuses.len())?;
                    let name = self.string()?;
                    self.m.fuses.push(FuseDef { name });
                }
                "binding" => {
                    self.decl_id("G", "binding", self.m.bindings.len())?;
                    let name = self.atom()?;
                    self.expect_punct(":")?;
                    let claim = self.ty()?;
                    self.m.bindings.push(BindingDef { name, claim });
                }
                "native" => {
                    self.decl_id("N", "native", self.m.natives.len())?;
                    let name = self.string()?;
                    self.m.natives.push(NativeDef { name });
                }
                "region" => {
                    self.decl_id("R", "region", self.m.regions.len())?;
                    let r = self.region()?;
                    self.m.regions.push(r);
                }
                _ => {
                    self.pos -= 1;
                    return self.err(format!("unknown module declaration `{w}`"));
                }
            }
        }
        Ok(())
    }

    // --- functions --------------------------------------------------------

    fn func(&mut self) -> PResult<Func> {
        let w = self.word().or_else(|_| self.err("expected `@sN`"))?;
        let _ = w;
        // `@` was consumed by the caller; `sN` is this word.
        let script = match prefixed(&w, "s") {
            Some(n) => ScriptId::new(n),
            None => return self.err(format!("expected a script name `sN`, found `{w}`")),
        };
        self.expect_punct("(")?;
        let mut frame = FrameShape::default();
        while !self.eat_punct(")") {
            let key = self.word()?;
            self.expect_punct("=")?;
            match key.as_str() {
                "formals" => frame.formals = self.int()?,
                "locals" => frame.locals = self.int()?,
                "depths" => {
                    self.expect_punct("{")?;
                    while !self.eat_punct("}") {
                        let pc = Pc::new(self.int()?);
                        self.expect_punct(":")?;
                        let d = self.int()?;
                        frame.depths.insert(pc, d);
                        self.eat_punct(",");
                    }
                }
                _ => return self.err(format!("unknown frame property `{key}`")),
            }
            self.eat_punct(",");
        }
        self.expect_punct("{")?;
        let mut st = FuncState {
            func: Func::new(script, frame),
            defined: vec![],
            block_defined: vec![],
            notes: vec![],
            uses: BTreeMap::new(),
        };
        while self.eat_word("root") {
            let kind = if self.eat_word("entry") {
                RootKind::Entry
            } else if self.eat_word("onramp") {
                self.expect_punct("(")?;
                self.expect_word("pc")?;
                self.expect_punct("=")?;
                let pc = Pc::new(self.int()?);
                self.expect_punct(")")?;
                RootKind::Onramp(pc)
            } else {
                return self.err("expected `entry` or `onramp(pc=N)`");
            };
            let b = st.block(self.prefixed("b", "a block")?);
            st.func.roots.push(Root { kind, block: b });
        }
        let mut cur: Option<Block> = None;
        loop {
            if self.eat_punct("}") {
                break;
            }
            // Block header: `bN:` or `bN(params):`.
            if self.at_prefixed("b") && matches!(self.peek_at(1), Some(Tok::Punct(":" | "("))) {
                let line = self.line();
                let b = st.block(self.prefixed("b", "a block")?);
                if st.block_defined[b.as_u32() as usize] {
                    return self.err(format!("{b} is defined twice"));
                }
                st.block_defined[b.as_u32() as usize] = true;
                st.func.layout.push(b);
                if self.eat_punct("(") {
                    while !self.eat_punct(")") {
                        let v = st.value(self.prefixed("v", "a value")?, line);
                        self.expect_punct(":")?;
                        let ty = self.ty()?;
                        let n = st.func.blocks[b].params.len() as u32;
                        st.define(v, ValueDef::Param(b, n), Some(ty), line)?;
                        st.func.blocks[b].params.push(v);
                        if !self.eat_punct(",") {
                            self.expect_punct(")")?;
                            break;
                        }
                    }
                }
                self.expect_punct(":")?;
                cur = Some(b);
                continue;
            }
            let Some(b) = cur else {
                return self.err("instruction outside a block");
            };
            self.inst(&mut st, b)?;
        }
        self.finish(st)
    }

    fn value_list(&mut self, st: &mut FuncState) -> PResult<Vec<Value>> {
        let line = self.line();
        self.expect_punct("[")?;
        let mut vs = vec![];
        while !self.eat_punct("]") {
            vs.push(st.value(self.prefixed("v", "a value")?, line));
            if !self.eat_punct(",") {
                self.expect_punct("]")?;
                break;
            }
        }
        Ok(vs)
    }

    fn edge(&mut self, st: &mut FuncState) -> PResult<Edge> {
        let line = self.line();
        let block = st.block(self.prefixed("b", "a block")?);
        let mut args = vec![];
        if self.eat_punct("(") {
            let mut next_out = 0;
            while !self.eat_punct(")") {
                let v = st.value(self.prefixed("v", "a value")?, line);
                if self.eat_punct(":") {
                    let ty = self.ty()?;
                    let k = if self.eat_punct("=") {
                        self.expect_punct("%")?;
                        self.int()?
                    } else {
                        next_out
                    };
                    next_out = k + 1;
                    st.notes.push(OutNote {
                        line,
                        block,
                        pos: args.len(),
                        param: v,
                        ty,
                    });
                    // The param is defined by its block header, not here.
                    st.uses.remove(&v);
                    args.push(EdgeArg::Out(k));
                } else {
                    args.push(EdgeArg::Value(v));
                }
                if !self.eat_punct(",") {
                    self.expect_punct(")")?;
                    break;
                }
            }
        }
        Ok(Edge { block, args })
    }

    fn inst(&mut self, st: &mut FuncState, b: Block) -> PResult<()> {
        let line = self.line();
        // Results.
        let mut results: Vec<(Value, Option<Type>)> = vec![];
        if self.at_prefixed("v") && matches!(self.peek_at(1), Some(Tok::Punct(":" | "=" | ","))) {
            loop {
                let v = st.value(self.prefixed("v", "a value")?, line);
                let ty = if self.eat_punct(":") {
                    Some(self.ty()?)
                } else {
                    None
                };
                results.push((v, ty));
                if !self.eat_punct(",") {
                    break;
                }
            }
            self.expect_punct("=")?;
        }
        let mn = self.word()?;
        let Some(template) = template(&mn) else {
            self.pos -= 1;
            return self.err(format!("unknown opcode `{mn}`"));
        };
        let mut args = vec![];
        let mut op = template;
        if let Opcode::Exit { .. } | Opcode::ExitThrow { .. } = template {
            self.expect_word("pc")?;
            self.expect_punct("=")?;
            let pc = Pc::new(self.int()?);
            self.expect_word("this")?;
            self.expect_punct("=")?;
            args.push(st.value(self.prefixed("v", "a value")?, line));
            self.expect_word("args")?;
            self.expect_punct("=")?;
            let a = self.value_list(st)?;
            self.expect_word("locals")?;
            self.expect_punct("=")?;
            let l = self.value_list(st)?;
            self.expect_word("stack")?;
            self.expect_punct("=")?;
            let s = self.value_list(st)?;
            let (nargs, nlocals) = (a.len() as u32, l.len() as u32);
            args.extend(a);
            args.extend(l);
            args.extend(s);
            op = if matches!(template, Opcode::Exit { .. }) {
                Opcode::Exit { pc, nargs, nlocals }
            } else {
                Opcode::ExitThrow { pc, nargs, nlocals }
            };
        } else if template != Opcode::Jump {
            // Operands, then immediates. A value followed by `=` or `:`
            // is the next instruction's result, not an operand.
            let starts_def = |p: &Parser| matches!(p.peek_at(1), Some(Tok::Punct("=" | ":")));
            if self.at_prefixed("v") && !starts_def(self) {
                loop {
                    args.push(st.value(self.prefixed("v", "a value")?, line));
                    if !(self.at_punct(",")
                        && matches!(self.peek_at(1), Some(Tok::Word(w)) if prefixed(w, "v").is_some()))
                    {
                        break;
                    }
                    self.pos += 1;
                }
            }
            op = self.immediates(template)?;
        }
        // Trailers may come before or after the successors.
        let mut attach = None;
        let mut witness = None;
        self.trailers(&mut attach, &mut witness)?;
        // Successors.
        let mut succs = vec![];
        if template == Opcode::Jump {
            succs.push(self.edge(st)?);
        } else if self.eat_punct("->") {
            let mut ncases = 0;
            let mut got = vec![];
            loop {
                let role = self.word()?;
                if role.strip_prefix("case") == Some(&ncases.to_string()) {
                    ncases += 1;
                }
                got.push(role);
                succs.push(self.edge(st)?);
                if !self.eat_punct(",") {
                    break;
                }
            }
            if let Opcode::Switch(_) = op {
                op = Opcode::Switch(ncases);
            }
            // Roles are checked here, not by the validator: they are how
            // the text names which edge is which.
            let names: Vec<String> = op.roles().iter().map(|r| r.name()).collect();
            if names != got {
                return Err(ParseError {
                    line,
                    msg: format!(
                        "{mn}: expected successors [{}], found [{}]",
                        names.join(", "),
                        got.join(", ")
                    ),
                });
            }
        }
        let inst = st.func.insts.push(InstData {
            op,
            args,
            results: vec![],
            succs,
            attach: None,
        });
        for (i, (v, ty)) in results.iter().enumerate() {
            st.define(*v, ValueDef::Result(inst, i as u32), *ty, line)?;
            st.uses.remove(v);
        }
        st.func.insts[inst].results = results.iter().map(|r| r.0).collect();
        st.func.blocks[b].insts.push(inst);
        self.trailers(&mut attach, &mut witness)?;
        if let Some(a) = attach {
            st.func.insts[inst].attach = Some(st.func.attachments.push(a));
        }
        st.func.witnesses[inst] = witness;
        Ok(())
    }

    /// `@{attachment}` and `!pred{witness}`, each at most once.
    fn trailers(
        &mut self,
        attach: &mut Option<Attachment>,
        witness: &mut Option<Witness>,
    ) -> PResult<()> {
        loop {
            if self.eat_punct("@") {
                if attach.is_some() {
                    return self.err("two attachments on one instruction");
                }
                *attach = Some(self.attachment()?);
            } else if self.at_punct("!")
                && matches!(self.peek_at(1), Some(Tok::Word(w)) if w == "pred")
            {
                if witness.is_some() {
                    return self.err("two prediction witnesses on one instruction");
                }
                self.pos += 2;
                let may_kill = self.kill_pattern()?;
                *witness = Some(Witness { may_kill });
            } else {
                return Ok(());
            }
        }
    }

    fn immediates(&mut self, t: Opcode) -> PResult<Opcode> {
        use Opcode::*;
        Ok(match t {
            ConstVal(_) => {
                let w = self.word()?;
                ConstVal(match w.as_str() {
                    "undefined" => crate::mir::ops::ConstVal::Undefined,
                    "null" => crate::mir::ops::ConstVal::Null,
                    "true" => crate::mir::ops::ConstVal::Bool(true),
                    "false" => crate::mir::ops::ConstVal::Bool(false),
                    "int32" => crate::mir::ops::ConstVal::Int32(self.int()?),
                    "double" => crate::mir::ops::ConstVal::Double(self.f64_bits()?),
                    _ => return self.err(format!("bad const.val literal `{w}`")),
                })
            }
            ConstI32(_) => ConstI32(self.int()?),
            ConstF64(_) => ConstF64(self.f64_bits()?),
            ConstBool(_) => {
                let w = self.word()?;
                match w.as_str() {
                    "true" => ConstBool(true),
                    "false" => ConstBool(false),
                    _ => return self.err(format!("expected true or false, found `{w}`")),
                }
            }
            ConstObj(_) => ConstObj(SnapObj::from_u32(self.prefixed("S", "a snapshot object")?)),
            GuardSingleton(_) => {
                GuardSingleton(SnapObj::from_u32(self.prefixed("S", "a snapshot object")?))
            }
            ConstStr(_) => ConstStr(self.atom()?),
            JsGetProp(_) => JsGetProp(self.atom()?),
            JsSetProp(_) => JsSetProp(self.atom()?),
            JsGetName(_) => JsGetName(self.atom()?),
            LoadField(_) => LoadField(self.atom()?),
            StoreField(_) => StoreField(self.atom()?),
            InitField(_) => InitField(self.atom()?),
            GuardTags(_) => GuardTags(self.tags()?),
            GuardKind(_) => GuardKind(self.kind()?),
            GuardLayout { .. } => {
                let keys = self.keys()?;
                let types = self.eat_word("types");
                GuardLayout { keys, types }
            }
            GuardScript(_) => GuardScript(self.script()?),
            CheckFuse(_) => CheckFuse(FuseId::from_u32(self.prefixed("F", "a fuse")?)),
            CheckBinding(_) => CheckBinding(BindingId::from_u32(self.prefixed("G", "a binding")?)),
            LoadGName(_) => LoadGName(BindingId::from_u32(self.prefixed("G", "a binding")?)),
            StoreGName(_) => StoreGName(BindingId::from_u32(self.prefixed("G", "a binding")?)),
            CheckNative(_) => CheckNative(NativeId::from_u32(self.prefixed("N", "a native")?)),
            CallNative(_) => CallNative(NativeId::from_u32(self.prefixed("N", "a native")?)),
            NewObject(_) => NewObject(self.layout_key()?),
            EnvLoad(_) => EnvLoad(EnvSlot::new(self.int()?)),
            EnvStore(_) => EnvStore(EnvSlot::new(self.int()?)),
            other => other,
        })
    }

    fn attachment(&mut self) -> PResult<Attachment> {
        self.expect_punct("{")?;
        let mut a = Attachment::default();
        while !self.eat_punct("}") {
            let key = self.word()?;
            self.expect_punct("=")?;
            match key.as_str() {
                "site" => {
                    let s = self.int()?;
                    self.expect_punct(":")?;
                    let pc = self.int()?;
                    a.site = Some(Site::from_raw(s, pc));
                }
                "ic" => a.ic_cell = Some(self.int()?),
                "call" => a.call_cell = Some(self.int()?),
                "slot" => a.slot = Some(SlotIndex::new(self.int()?)),
                "mask" => a.field_mask = Some(self.int()?),
                "targets" => {
                    self.expect_punct("[")?;
                    while !self.eat_punct("]") {
                        a.targets.push(self.script()?);
                        self.eat_punct(",");
                    }
                }
                _ => return self.err(format!("unknown attachment key `{key}`")),
            }
            self.eat_punct(",");
        }
        Ok(a)
    }

    fn finish(&mut self, mut st: FuncState) -> PResult<Func> {
        let line = self.line();
        // Every referenced block is defined.
        for r in &st.func.roots {
            if !st
                .block_defined
                .get(r.block.as_u32() as usize)
                .copied()
                .unwrap_or(false)
            {
                return self.err(format!("root {} is not defined", r.block));
            }
        }
        for &b in &st.func.layout {
            for &i in &st.func.blocks[b].insts {
                for e in &st.func.insts[i].succs {
                    if !st.block_defined[e.block.as_u32() as usize] {
                        return self.err(format!("{b} branches to undefined block {}", e.block));
                    }
                }
            }
        }
        // Every used value is defined.
        for (v, l) in &st.uses {
            if st.defined[v.as_u32() as usize].is_none() {
                return Err(ParseError {
                    line: *l,
                    msg: format!("{v} is used but never defined"),
                });
            }
        }
        // Output annotations agree with the target's header.
        for n in &st.notes {
            let p = st.func.blocks[n.block].params.get(n.pos).copied();
            if p != Some(n.param) {
                return Err(ParseError {
                    line: n.line,
                    msg: format!("{} is not param {} of {}", n.param, n.pos, n.block),
                });
            }
            let t = st.func.values[n.param].ty;
            if t != n.ty {
                return Err(ParseError {
                    line: n.line,
                    msg: format!(
                        "edge annotation {}: {} disagrees with {}'s header ({})",
                        n.param,
                        type_str_in(Some(&self.m), &n.ty),
                        n.block,
                        type_str_in(Some(&self.m), &t)
                    ),
                });
            }
        }
        // Infer omitted result types, to a fixpoint (a result's operands may
        // be results printed later, but never cyclically: cycles go through
        // block params, which are always typed).
        loop {
            let mut progress = false;
            let mut pending = None;
            for (inst, d) in st.func.insts.iter() {
                let unresolved: Vec<usize> = d
                    .results
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| st.defined[v.as_u32() as usize] == Some(None))
                    .map(|(i, _)| i)
                    .collect();
                if unresolved.is_empty() {
                    continue;
                }
                let known = d
                    .args
                    .iter()
                    .all(|v| !matches!(st.defined[v.as_u32() as usize], Some(None)));
                if !known {
                    pending = Some(inst);
                    continue;
                }
                let tys: Vec<Type> = d.args.iter().map(|&v| st.func.values[v].ty).collect();
                let sig = signature(&d.op, &tys, &self.m).map_err(|e| ParseError {
                    line,
                    msg: format!(
                        "cannot infer the result type of {} ({e}); annotate it",
                        mnemonic(&d.op)
                    ),
                })?;
                let results = d.results.clone();
                for i in unresolved {
                    let Some(&t) = sig.results.get(i) else {
                        return self.err(format!("{} has no result {i}", mnemonic(&d.op)));
                    };
                    st.func.values[results[i]].ty = t;
                    st.defined[results[i].as_u32() as usize] = Some(Some(t));
                }
                progress = true;
            }
            match (progress, pending) {
                (_, None) => break,
                (true, Some(_)) => continue,
                (false, Some(i)) => {
                    return self.err(format!(
                        "cannot infer the result types of {i}: operand types are cyclic"
                    ))
                }
            }
        }
        Ok(st.func)
    }

    fn top(&mut self) -> PResult<Module> {
        if self.eat_word("module") {
            self.module_decls()?;
        }
        while self.pos < self.toks.len() {
            self.expect_word("func")?;
            self.expect_punct("@")?;
            let f = self.func()?;
            if self.m.func(f.script).is_some() {
                return self.err(format!("func @s{} defined twice", f.script));
            }
            self.m.funcs.push(f);
        }
        Ok(std::mem::take(&mut self.m))
    }
}

/// The opcode a mnemonic names, with placeholder immediates.
fn template(mn: &str) -> Option<Opcode> {
    use Opcode::*;
    let placeholder_atom = AtomId::from_u32(0);
    let mut all = vec![
        ConstVal(crate::mir::ops::ConstVal::Undefined),
        ConstI32(0),
        ConstF64(0),
        ConstBool(false),
        ConstObj(SnapObj::from_u32(0)),
        ConstStr(placeholder_atom),
        Box,
        I32ToInt,
        I32ToF64,
        IntToF64,
        Weaken,
        GuardTags(TagSet::NONE),
        GuardKind(ObjKind::Any),
        GuardLayout {
            keys: KeyRange::one(LayoutKey::new(0)),
            types: false,
        },
        GuardSingleton(SnapObj::from_u32(0)),
        GuardScript(ScriptId::new(0)),
        F64ToIntExact,
        CheckFuse(FuseId::from_u32(0)),
        CheckBinding(BindingId::from_u32(0)),
        CheckNative(NativeId::from_u32(0)),
        Jump,
        Br,
        Switch(0),
        Return,
        Exit {
            pc: Pc::new(0),
            nargs: 0,
            nlocals: 0,
        },
        ExitThrow {
            pc: Pc::new(0),
            nargs: 0,
            nlocals: 0,
        },
        Unreachable,
        F64Neg,
        I32Ushr,
        ToInt32,
        JsAdd,
        JsTypeof,
        JsToBool,
        JsToNumeric,
        JsGetProp(placeholder_atom),
        JsSetProp(placeholder_atom),
        JsGetElem,
        JsSetElem,
        JsGetName(placeholder_atom),
        LoadField(placeholder_atom),
        StoreField(placeholder_atom),
        InitField(placeholder_atom),
        PublishLayout,
        NewObject(LayoutKey::new(0)),
        NewArray,
        LoadElem,
        StoreElem,
        LoadTa,
        StoreTa,
        LengthArray,
        LengthString,
        LengthTa,
        ElementsPtr,
        StrCharCodeAt,
        LoadGName(BindingId::from_u32(0)),
        StoreGName(BindingId::from_u32(0)),
        EnvCurrent,
        EnvParent,
        EnvLoad(EnvSlot::new(0)),
        EnvStore(EnvSlot::new(0)),
        Call,
        CallDirect,
        Construct,
        CallNative(NativeId::from_u32(0)),
    ];
    for k in UnboxKind::ALL {
        all.push(Unbox(k));
        all.push(GuardUnbox(k));
    }
    for a in [ArithOp::Add, ArithOp::Sub, ArithOp::Mul] {
        all.extend([I32Ovf(a), I32Wrap(a), IntArith(a)]);
    }
    for o in [F64Op::Add, F64Op::Sub, F64Op::Mul, F64Op::Div, F64Op::Mod] {
        all.push(F64Arith(o));
    }
    for o in [BitOp::And, BitOp::Or, BitOp::Xor, BitOp::Shl, BitOp::Shr] {
        all.push(I32Bit(o));
    }
    for r in [NumRepr::I32, NumRepr::Int, NumRepr::F64] {
        for c in [Cc::Eq, Cc::Ne, Cc::Lt, Cc::Le, Cc::Gt, Cc::Ge] {
            all.push(Cmp(r, c));
        }
    }
    for f in MathFn::ALL {
        all.push(Math(f));
    }
    use crate::mir::ops::{JsBinop as B, JsCc as C, JsUnop as U};
    for b in [
        B::Sub,
        B::Mul,
        B::Div,
        B::Mod,
        B::Pow,
        B::BitAnd,
        B::BitOr,
        B::BitXor,
        B::Lsh,
        B::Rsh,
        B::Ursh,
    ] {
        all.push(JsBinop(b));
    }
    for u in [U::Neg, U::Pos, U::BitNot, U::Inc, U::Dec] {
        all.push(JsUnop(u));
    }
    for c in [
        C::Eq,
        C::Ne,
        C::StrictEq,
        C::StrictNe,
        C::Lt,
        C::Le,
        C::Gt,
        C::Ge,
    ] {
        all.push(JsCompare(c));
    }
    all.into_iter().find(|op| mnemonic(op) == mn)
}

/// Parse a module (tables plus functions).
pub fn parse(src: &str) -> Result<Module, ParseError> {
    let toks = lex(src)?;
    let mut p = Parser {
        toks,
        pos: 0,
        m: Module::default(),
    };
    p.top()
}

/// Parse a string that `parse` would accept as an atom, for tests.
pub fn js(s: &str) -> JsString {
    JsString::from(s)
}
