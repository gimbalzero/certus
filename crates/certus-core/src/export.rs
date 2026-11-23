//! Reader for the `lean4export` NDJSON format, version 3.x.
//!
//! Each line is one JSON record. Names, universe levels and expressions get
//! numeric ids (`in`, `il`, `ie`), and records may refer only to ids that
//! were defined earlier, so the file is a topologically ordered DAG. The
//! reader *fails closed*: unknown record kinds, unknown fields, references
//! to ids not yet defined, ids defined twice and duplicate declarations are
//! all errors. Because every reference must point backwards, the graph can
//! never contain a cycle.
//!
//! lean4export numbers each kind densely from 0 (`in` 0 is the anonymous
//! name and `il` 0 is level zero, both implicit), but the format only asks
//! for integer ids, and Lean's own importer accepts sparse or out-of-order
//! ids as long as each is defined before use. The reader therefore maps the
//! file's ids to dense internal ids ([`IdMap`]); for ordinary exports the
//! map is the identity and costs nothing. All ids stored in [`Env`] are the
//! internal ones.
//!
//! Names are canonicalised by content while reading, so two name records with
//! the same text map to one id. That way, dependency analysis can never miss
//! an edge because the exporter happened to emit a name twice.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::io::BufRead;

pub type NameId = u32;
pub type LevelId = u32;
pub type ExprId = u32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Name {
    Anon,
    Str { pre: NameId, s: String },
    Num { pre: NameId, n: u64 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    BVar(u64),
    Sort(LevelId),
    Const { name: NameId, levels: Box<[LevelId]> },
    App { f: ExprId, a: ExprId },
    Lam { name: NameId, ty: ExprId, body: ExprId, bi: BinderInfo },
    Pi { name: NameId, ty: ExprId, body: ExprId, bi: BinderInfo },
    Let { name: NameId, ty: ExprId, val: ExprId, body: ExprId, nondep: bool },
    NatLit(Box<str>),
    StrLit(Box<str>),
    Proj { type_name: NameId, idx: u64, structure: ExprId },
}

// ---- Declarations: stored exactly as exported (ids rewritten to canonical names). ----

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct AxiomVal {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub r#type: ExprId,
    pub is_unsafe: bool,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct DefVal {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub r#type: ExprId,
    pub value: ExprId,
    /// `"opaque"`, `"abbrev"` or `{"regular": n}`; kept verbatim.
    pub hints: serde_json::Value,
    /// `"safe"`, `"unsafe"` or `"partial"`.
    pub safety: String,
    pub all: Vec<NameId>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ThmVal {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub r#type: ExprId,
    pub value: ExprId,
    pub all: Vec<NameId>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct OpaqueVal {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub r#type: ExprId,
    pub value: ExprId,
    pub is_unsafe: bool,
    pub all: Vec<NameId>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct QuotVal {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub r#type: ExprId,
    pub kind: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct InductiveType {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub r#type: ExprId,
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CtorVal {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub r#type: ExprId,
    pub induct: NameId,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
    pub is_unsafe: bool,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RecRule {
    pub ctor: NameId,
    pub nfields: u64,
    pub rhs: ExprId,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RecVal {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub r#type: ExprId,
    pub all: Vec<NameId>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<RecRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

/// A mutual block of inductive types with their constructors and recursors.
/// The kernel checks a block as one unit, so Certus treats it as one declaration.
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct InductiveVal {
    pub types: Vec<InductiveType>,
    pub ctors: Vec<CtorVal>,
    pub recs: Vec<RecVal>,
}

#[derive(Debug, Clone)]
pub enum Decl {
    Axiom(AxiomVal),
    Def(DefVal),
    Thm(ThmVal),
    Opaque(OpaqueVal),
    Quot(QuotVal),
    Inductive(InductiveVal),
}

impl Decl {
    pub fn kind(&self) -> &'static str {
        match self {
            Decl::Axiom(_) => "axiom",
            Decl::Def(_) => "def",
            Decl::Thm(_) => "thm",
            Decl::Opaque(_) => "opaque",
            Decl::Quot(_) => "quot",
            Decl::Inductive(_) => "inductive",
        }
    }

    /// The name used to refer to this declaration in reports.
    pub fn primary_name(&self) -> NameId {
        match self {
            Decl::Axiom(d) => d.name,
            Decl::Def(d) => d.name,
            Decl::Thm(d) => d.name,
            Decl::Opaque(d) => d.name,
            Decl::Quot(d) => d.name,
            Decl::Inductive(d) => d.types.first().map_or(0, |t| t.name),
        }
    }

    /// Every constant name this declaration introduces.
    pub fn defined_names(&self) -> Vec<NameId> {
        match self {
            Decl::Inductive(d) => d
                .types
                .iter()
                .map(|t| t.name)
                .chain(d.ctors.iter().map(|c| c.name))
                .chain(d.recs.iter().map(|r| r.name))
                .collect(),
            _ => vec![self.primary_name()],
        }
    }

    /// Every top-level expression the kernel must check for this declaration.
    pub fn roots(&self) -> Vec<ExprId> {
        match self {
            Decl::Axiom(d) => vec![d.r#type],
            Decl::Def(d) => vec![d.r#type, d.value],
            Decl::Thm(d) => vec![d.r#type, d.value],
            Decl::Opaque(d) => vec![d.r#type, d.value],
            Decl::Quot(d) => vec![d.r#type],
            Decl::Inductive(d) => {
                let mut v: Vec<ExprId> = d.types.iter().map(|t| t.r#type).collect();
                v.extend(d.ctors.iter().map(|c| c.r#type));
                for r in &d.recs {
                    v.push(r.r#type);
                    v.extend(r.rules.iter().map(|x| x.rhs));
                }
                v
            }
        }
    }

    /// Apply `f` to every expression id stored in the declaration.
    pub fn map_exprs(&mut self, f: &mut impl FnMut(ExprId) -> ExprId) {
        match self {
            Decl::Axiom(d) => d.r#type = f(d.r#type),
            Decl::Quot(d) => d.r#type = f(d.r#type),
            Decl::Def(d) => {
                d.r#type = f(d.r#type);
                d.value = f(d.value);
            }
            Decl::Thm(d) => {
                d.r#type = f(d.r#type);
                d.value = f(d.value);
            }
            Decl::Opaque(d) => {
                d.r#type = f(d.r#type);
                d.value = f(d.value);
            }
            Decl::Inductive(d) => {
                for t in &mut d.types {
                    t.r#type = f(t.r#type);
                }
                for c in &mut d.ctors {
                    c.r#type = f(c.r#type);
                }
                for r in &mut d.recs {
                    r.r#type = f(r.r#type);
                    for rule in &mut r.rules {
                        rule.rhs = f(rule.rhs);
                    }
                }
            }
        }
    }

    /// True for anything outside Lean's safe fragment.
    pub fn is_unsafe_or_partial(&self) -> bool {
        match self {
            Decl::Axiom(d) => d.is_unsafe,
            Decl::Def(d) => d.safety != "safe",
            Decl::Opaque(d) => d.is_unsafe,
            Decl::Inductive(d) => {
                d.types.iter().any(|t| t.is_unsafe)
                    || d.ctors.iter().any(|c| c.is_unsafe)
                    || d.recs.iter().any(|r| r.is_unsafe)
            }
            Decl::Thm(_) | Decl::Quot(_) => false,
        }
    }

    /// Apply `f` to every name id stored in the declaration.
    pub fn map_names(&mut self, f: &mut impl FnMut(NameId) -> Result<NameId, String>) -> Result<(), String> {
        fn all(v: &mut [NameId], f: &mut impl FnMut(NameId) -> Result<NameId, String>) -> Result<(), String> {
            for x in v {
                *x = f(*x)?;
            }
            Ok(())
        }
        match self {
            Decl::Axiom(d) => {
                d.name = f(d.name)?;
                all(&mut d.level_params, f)
            }
            Decl::Def(d) => {
                d.name = f(d.name)?;
                all(&mut d.level_params, f)?;
                all(&mut d.all, f)
            }
            Decl::Thm(d) => {
                d.name = f(d.name)?;
                all(&mut d.level_params, f)?;
                all(&mut d.all, f)
            }
            Decl::Opaque(d) => {
                d.name = f(d.name)?;
                all(&mut d.level_params, f)?;
                all(&mut d.all, f)
            }
            Decl::Quot(d) => {
                d.name = f(d.name)?;
                all(&mut d.level_params, f)
            }
            Decl::Inductive(d) => {
                if d.types.is_empty() {
                    return Err("inductive block with no types".into());
                }
                for t in &mut d.types {
                    t.name = f(t.name)?;
                    all(&mut t.level_params, f)?;
                    all(&mut t.all, f)?;
                    all(&mut t.ctors, f)?;
                }
                for c in &mut d.ctors {
                    c.name = f(c.name)?;
                    c.induct = f(c.induct)?;
                    all(&mut c.level_params, f)?;
                }
                for r in &mut d.recs {
                    r.name = f(r.name)?;
                    all(&mut r.level_params, f)?;
                    all(&mut r.all, f)?;
                    for rule in &mut r.rules {
                        rule.ctor = f(rule.ctor)?;
                    }
                }
                Ok(())
            }
        }
    }
}

// ---- Header ----

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Meta {
    pub exporter: Tool,
    pub format: Format,
    pub lean: LeanInfo,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Tool {
    pub name: String,
    pub version: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Format {
    pub version: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LeanInfo {
    pub githash: String,
    pub version: String,
}

// ---- Raw line shape ----

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct StrName {
    pre: NameId,
    str: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NumName {
    pre: NameId,
    i: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ConstE {
    name: NameId,
    us: Vec<LevelId>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AppE {
    #[serde(rename = "fn")]
    f: ExprId,
    arg: ExprId,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BinderE {
    name: NameId,
    r#type: ExprId,
    body: ExprId,
    binder_info: BinderInfo,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LetE {
    name: NameId,
    r#type: ExprId,
    value: ExprId,
    body: ExprId,
    nondep: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProjE {
    type_name: NameId,
    idx: u64,
    #[serde(rename = "struct")]
    structure: ExprId,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Line {
    #[serde(rename = "in")]
    in_id: Option<u32>,
    il: Option<u32>,
    ie: Option<u32>,
    str: Option<StrName>,
    num: Option<NumName>,
    succ: Option<LevelId>,
    max: Option<[LevelId; 2]>,
    imax: Option<[LevelId; 2]>,
    param: Option<NameId>,
    bvar: Option<u64>,
    sort: Option<LevelId>,
    #[serde(rename = "const")]
    cnst: Option<ConstE>,
    app: Option<AppE>,
    lam: Option<BinderE>,
    #[serde(rename = "forallE")]
    forall_e: Option<BinderE>,
    #[serde(rename = "letE")]
    let_e: Option<LetE>,
    proj: Option<ProjE>,
    #[serde(rename = "natVal")]
    nat_val: Option<String>,
    #[serde(rename = "strVal")]
    str_val: Option<String>,
    meta: Option<Meta>,
    axiom: Option<AxiomVal>,
    def: Option<DefVal>,
    thm: Option<ThmVal>,
    opaque: Option<OpaqueVal>,
    quot: Option<QuotVal>,
    inductive: Option<InductiveVal>,
}

// ---- Environment ----

#[derive(Debug)]
pub struct ParseError {
    pub line: u64,
    pub msg: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.msg)
    }
}

impl std::error::Error for ParseError {}

#[derive(Hash, PartialEq, Eq)]
enum NameKey {
    Str(NameId, String),
    Num(NameId, u64),
}

/// Everything read from one export file.
#[derive(Debug)]
pub struct Env {
    pub meta: Meta,
    /// Indexed by name id. Id 0 is the anonymous name.
    pub names: Vec<Name>,
    /// Canonical id for each name id (equal to itself unless it is a duplicate).
    pub name_canon: Vec<NameId>,
    /// Indexed by level id. Id 0 is level zero.
    pub levels: Vec<Level>,
    /// Indexed by expression id.
    pub exprs: Vec<Expr>,
    /// Declarations in file order (which is dependency order).
    pub decls: Vec<Decl>,
    /// Canonical name id -> index into `decls`, for every defined constant.
    pub decl_of_name: HashMap<NameId, usize>,
    pub bytes: u64,
    pub lines: u64,
}

/// Maps the ids a file uses for one kind of record to dense internal ids,
/// in order of definition. While the file's ids are exactly `0, 1, 2, ...`
/// the map is the identity and no table is kept.
#[derive(Default)]
struct IdMap {
    sparse: Option<HashMap<u32, u32>>,
}

impl IdMap {
    /// Define file id `id` as internal id `next` (the number of entries so
    /// far). Fails if `id` was already defined.
    fn define(&mut self, kind: &str, id: u32, next: usize) -> Result<u32, String> {
        let next32 = u32::try_from(next).map_err(|_| format!("too many {kind} records"))?;
        let dup = || format!("{kind} id {id} defined twice");
        match &mut self.sparse {
            None if id as usize == next => Ok(next32),
            None if (id as usize) < next => Err(dup()),
            None => {
                let mut m: HashMap<u32, u32> = (0..next32).map(|i| (i, i)).collect();
                m.insert(id, next32);
                self.sparse = Some(m);
                Ok(next32)
            }
            Some(m) => match m.entry(id) {
                std::collections::hash_map::Entry::Occupied(_) => Err(dup()),
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(next32);
                    Ok(next32)
                }
            },
        }
    }

    /// The internal id of file id `id`, if it has been defined (`len` is the
    /// number of entries so far).
    fn get(&self, id: u32, len: usize) -> Option<u32> {
        match &self.sparse {
            None => ((id as usize) < len).then_some(id),
            Some(m) => m.get(&id).copied(),
        }
    }
}

struct Builder {
    meta: Option<Meta>,
    name_ids: IdMap,
    level_ids: IdMap,
    expr_ids: IdMap,
    names: Vec<Name>,
    name_canon: Vec<NameId>,
    name_index: HashMap<NameKey, NameId>,
    levels: Vec<Level>,
    exprs: Vec<Expr>,
    decls: Vec<Decl>,
    decl_of_name: HashMap<NameId, usize>,
}

/// Parse a whole export. Fails on the first malformed record.
pub fn parse<R: BufRead>(reader: R) -> Result<Env, ParseError> {
    parse_jobs(reader, std::thread::available_parallelism().map_or(1, |n| n.get()))
}

/// Bytes of input each thread decodes per batch. Larger batches are no faster
/// and use more memory (records decoded on one thread and linked on another
/// fragment the heap).
const BATCH_PER_THREAD: usize = 1 << 16;

/// One line of a batch, decoded: its line number within the batch, and the
/// record or why it is not one.
type Decoded = (u64, Result<Rec, String>);

/// [`parse`] with `jobs` threads decoding JSON. Lines are decoded in
/// parallel, a batch at a time, then added to the environment in file order
/// by one thread, so the result, and the first error reported, are the same
/// for every `jobs`.
pub fn parse_jobs<R: BufRead>(reader: R, jobs: usize) -> Result<Env, ParseError> {
    parse_batched(reader, jobs, BATCH_PER_THREAD)
}

/// [`parse_jobs`] with batches of `batch` bytes per thread. Tests use tiny
/// batches, so that lines cross batch boundaries.
#[doc(hidden)]
pub fn parse_batched<R: BufRead>(mut reader: R, jobs: usize, batch: usize) -> Result<Env, ParseError> {
    let jobs = jobs.max(1);
    let batch = batch.max(1);
    let mut b = Builder {
        meta: None,
        name_ids: IdMap::default(),
        level_ids: IdMap::default(),
        expr_ids: IdMap::default(),
        names: vec![Name::Anon],
        name_canon: vec![0],
        name_index: HashMap::new(),
        levels: vec![Level::Zero],
        exprs: Vec::new(),
        decls: Vec::new(),
        decl_of_name: HashMap::new(),
    };
    let (mut lines, mut bytes) = (0u64, 0u64);
    let mut block: Vec<u8> = Vec::new();
    let mut eof = false;
    let mut want = batch * jobs;
    while !eof {
        // Fill a block, then hold back any partial last line for the next one.
        while block.len() < want {
            let avail =
                reader.fill_buf().map_err(|e| ParseError { line: lines + 1, msg: format!("read error: {e}") })?;
            if avail.is_empty() {
                eof = true;
                break;
            }
            let n = avail.len();
            block.extend_from_slice(avail);
            reader.consume(n);
        }
        let cut = if eof { block.len() } else { block.iter().rposition(|&c| c == b'\n').map_or(0, |i| i + 1) };
        if cut == 0 && !eof {
            // A line longer than the whole block: read a bigger block.
            want *= 2;
            continue;
        }
        want = batch * jobs;
        let rest = block.split_off(cut);
        let pieces = split_lines(&block, jobs);
        let decoded: Vec<(Vec<Decoded>, u64)> = if pieces.len() <= 1 {
            pieces.iter().enumerate().map(|(k, p)| decode(p, lines == 0 && k == 0)).collect()
        } else {
            std::thread::scope(|s| {
                let hs: Vec<_> =
                    pieces.iter().enumerate().map(|(k, p)| s.spawn(move || decode(p, lines == 0 && k == 0))).collect();
                hs.into_iter().map(|h| h.join().expect("decoder thread panicked")).collect()
            })
        };
        for (records, n) in decoded {
            for (rel, rec) in records {
                let line = lines + rel;
                let rec = rec.map_err(|msg| ParseError { line, msg })?;
                b.add(rec).map_err(|msg| ParseError { line, msg })?;
            }
            lines += n;
        }
        bytes += block.len() as u64;
        block = rest;
    }
    let meta = b.meta.ok_or(ParseError { line: 0, msg: "empty export: no meta record".into() })?;
    Ok(Env {
        meta,
        names: b.names,
        name_canon: b.name_canon,
        levels: b.levels,
        exprs: b.exprs,
        decls: b.decls,
        decl_of_name: b.decl_of_name,
        bytes,
        lines,
    })
}

/// A strict fast path for the commonest record shapes, exactly as lean4export
/// writes them (keys in its order, no spaces). It returns what `serde_json`
/// followed by `classify` would, or `None` to leave the line to them:
/// any other shape, a leading zero, a number out of range, an escape or a
/// control character in a string all fall back, so the reader stays exactly
/// as strict as before. Most lines of an export are `app` nodes, so this is
/// most of the parsing time.
fn fast(b: &[u8]) -> Option<Rec> {
    let mut c = Cur { b, i: 0 };
    let r = if c.lit(b"{\"app\":{\"arg\":") {
        let a = c.u32()?;
        c.expect(b",\"fn\":")?;
        let f = c.u32()?;
        c.expect(b"},\"ie\":")?;
        let id = c.u32()?;
        c.expect(b"}")?;
        Rec::Expr { id, e: Expr::App { f, a } }
    } else if c.lit(b"{\"ie\":") {
        let id = c.u32()?;
        if c.lit(b",\"lam\":{\"binderInfo\":") {
            let (bi, body, name, ty) = c.binder()?;
            c.expect(b"}}")?;
            Rec::Expr { id, e: Expr::Lam { name, ty, body, bi } }
        } else if c.lit(b",\"letE\":{\"body\":") {
            let body = c.u32()?;
            c.expect(b",\"name\":")?;
            let name = c.u32()?;
            c.expect(b",\"nondep\":")?;
            let nondep = if c.lit(b"true") {
                true
            } else {
                c.expect(b"false")?;
                false
            };
            c.expect(b",\"type\":")?;
            let ty = c.u32()?;
            c.expect(b",\"value\":")?;
            let val = c.u32()?;
            c.expect(b"}}")?;
            Rec::Expr { id, e: Expr::Let { name, ty, val, body, nondep } }
        } else if c.lit(b",\"proj\":{\"idx\":") {
            let idx = c.u64()?;
            c.expect(b",\"struct\":")?;
            let structure = c.u32()?;
            c.expect(b",\"typeName\":")?;
            let type_name = c.u32()?;
            c.expect(b"}}")?;
            Rec::Expr { id, e: Expr::Proj { type_name, idx, structure } }
        } else if c.lit(b",\"sort\":") {
            let l = c.u32()?;
            c.expect(b"}")?;
            Rec::Expr { id, e: Expr::Sort(l) }
        } else {
            return None;
        }
    } else if c.lit(b"{\"forallE\":{\"binderInfo\":") {
        let (bi, body, name, ty) = c.binder()?;
        c.expect(b"},\"ie\":")?;
        let id = c.u32()?;
        c.expect(b"}")?;
        Rec::Expr { id, e: Expr::Pi { name, ty, body, bi } }
    } else if c.lit(b"{\"const\":{\"name\":") {
        let name = c.u32()?;
        c.expect(b",\"us\":[")?;
        let mut us = Vec::new();
        if !c.lit(b"]") {
            loop {
                us.push(c.u32()?);
                if c.lit(b"]") {
                    break;
                }
                c.expect(b",")?;
            }
        }
        c.expect(b"},\"ie\":")?;
        let id = c.u32()?;
        c.expect(b"}")?;
        Rec::Expr { id, e: Expr::Const { name, levels: us.into_boxed_slice() } }
    } else if c.lit(b"{\"bvar\":") {
        let i = c.u64()?;
        c.expect(b",\"ie\":")?;
        let id = c.u32()?;
        c.expect(b"}")?;
        Rec::Expr { id, e: Expr::BVar(i) }
    } else if c.lit(b"{\"in\":") {
        let id = c.u32()?;
        if c.lit(b",\"num\":{\"i\":") {
            let n = c.u64()?;
            c.expect(b",\"pre\":")?;
            let pre = c.u32()?;
            c.expect(b"}}")?;
            Rec::Name { id, name: Name::Num { pre, n } }
        } else if c.lit(b",\"str\":{\"pre\":") {
            let pre = c.u32()?;
            c.expect(b",\"str\":\"")?;
            let start = c.i;
            while c.i < b.len() && b[c.i] != b'"' {
                if b[c.i] == b'\\' || b[c.i] < 0x20 {
                    return None;
                }
                c.i += 1;
            }
            let s = std::str::from_utf8(&b[start..c.i]).ok()?.to_string();
            c.expect(b"\"}}")?;
            Rec::Name { id, name: Name::Str { pre, s } }
        } else {
            return None;
        }
    } else {
        return None;
    };
    (c.i == b.len()).then_some(r)
}

struct Cur<'a> {
    b: &'a [u8],
    i: usize,
}

impl Cur<'_> {
    fn lit(&mut self, s: &[u8]) -> bool {
        if self.b[self.i..].starts_with(s) {
            self.i += s.len();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, s: &[u8]) -> Option<()> {
        self.lit(s).then_some(())
    }

    /// A JSON natural number as `serde_json` reads it into a `u64`: no
    /// sign, no leading zero, no fraction or exponent.
    fn u64(&mut self) -> Option<u64> {
        let start = self.i;
        let mut v: u64 = 0;
        while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
            v = v.checked_mul(10)?.checked_add((self.b[self.i] - b'0') as u64)?;
            self.i += 1;
        }
        let len = self.i - start;
        if len == 0 || (len > 1 && self.b[start] == b'0') {
            return None;
        }
        if self.i < self.b.len() && matches!(self.b[self.i], b'.' | b'e' | b'E') {
            return None;
        }
        Some(v)
    }

    fn u32(&mut self) -> Option<u32> {
        u32::try_from(self.u64()?).ok()
    }

    /// `"<binder info>","body":B,"name":N,"type":T`, after `"binderInfo":`.
    fn binder(&mut self) -> Option<(BinderInfo, u32, u32, u32)> {
        let bi = if self.lit(b"\"default\"") {
            BinderInfo::Default
        } else if self.lit(b"\"implicit\"") {
            BinderInfo::Implicit
        } else if self.lit(b"\"instImplicit\"") {
            BinderInfo::InstImplicit
        } else if self.lit(b"\"strictImplicit\"") {
            BinderInfo::StrictImplicit
        } else {
            return None;
        };
        self.expect(b",\"body\":")?;
        let body = self.u32()?;
        self.expect(b",\"name\":")?;
        let name = self.u32()?;
        self.expect(b",\"type\":")?;
        let ty = self.u32()?;
        Some((bi, body, name, ty))
    }
}

/// Whether to use [`fast`] (tests turn it off to compare).
static FAST: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

#[doc(hidden)]
pub fn set_fast_path_for_tests(on: bool) {
    FAST.store(on, std::sync::atomic::Ordering::Relaxed);
}

/// Split `block` into at most `n` pieces of whole lines.
fn split_lines(block: &[u8], n: usize) -> Vec<&[u8]> {
    let mut out = Vec::with_capacity(n);
    let mut start = 0;
    for k in 1..n {
        let target = (block.len() * k / n).max(start);
        let end = match block[target..].iter().position(|&c| c == b'\n') {
            Some(i) => target + i + 1,
            None => break,
        };
        if end > start {
            out.push(&block[start..end]);
            start = end;
        }
    }
    if start < block.len() {
        out.push(&block[start..]);
    }
    out
}

/// Decode and classify the lines of `piece`, numbered from 1, stopping at the
/// first one that is not a valid record. `file_start`: the piece starts the
/// file, so its line 1 must be the meta record. Also returns how many lines
/// the piece has.
fn decode(piece: &[u8], file_start: bool) -> (Vec<Decoded>, u64) {
    let mut out = Vec::new();
    let mut n = 0u64;
    for raw in piece.split_inclusive(|&c| c == b'\n') {
        n += 1;
        let text = match std::str::from_utf8(raw) {
            Ok(t) => t.trim_end(),
            Err(_) => {
                out.push((n, Err("read error: stream did not contain valid UTF-8".to_string())));
                return (out, n);
            }
        };
        if text.is_empty() {
            continue;
        }
        let first = file_start && n == 1;
        let quick =
            if first || !FAST.load(std::sync::atomic::Ordering::Relaxed) { None } else { fast(text.as_bytes()) };
        let rec = match quick {
            Some(r) => Ok(r),
            None => serde_json::from_str::<Line>(text).map_err(|e| e.to_string()).and_then(|r| classify(r, first)),
        };
        let bad = rec.is_err();
        out.push((n, rec));
        if bad {
            break;
        }
    }
    // Lines after an error are not decoded, but still counted.
    n = piece.split_inclusive(|&c| c == b'\n').count() as u64;
    (out, n)
}

impl Builder {
    fn name(&self, id: NameId) -> Result<NameId, String> {
        match self.name_ids.get(id, self.names.len()) {
            Some(i) => Ok(self.name_canon[i as usize]),
            None => Err(format!("reference to undefined name {id}")),
        }
    }

    fn level(&self, id: LevelId) -> Result<LevelId, String> {
        self.level_ids.get(id, self.levels.len()).ok_or_else(|| format!("reference to undefined level {id}"))
    }

    fn expr(&self, id: ExprId) -> Result<ExprId, String> {
        self.expr_ids.get(id, self.exprs.len()).ok_or_else(|| format!("reference to undefined expression {id}"))
    }

    /// Add one classified record. Only this needs the records before it.
    fn add(&mut self, r: Rec) -> Result<(), String> {
        match r {
            Rec::Meta(m) => {
                self.meta = Some(*m);
                Ok(())
            }
            Rec::Name { id, name } => {
                let (name, key) = match name {
                    Name::Str { pre, s } => {
                        let pre = self.name(pre)?;
                        (Name::Str { pre, s: s.clone() }, NameKey::Str(pre, s))
                    }
                    Name::Num { pre, n } => {
                        let pre = self.name(pre)?;
                        (Name::Num { pre, n }, NameKey::Num(pre, n))
                    }
                    Name::Anon => unreachable!("classify never makes an anonymous name record"),
                };
                let id = self.name_ids.define("name", id, self.names.len())?;
                let canon = *self.name_index.entry(key).or_insert(id);
                self.names.push(name);
                self.name_canon.push(canon);
                Ok(())
            }
            Rec::Level { id, l } => {
                let lvl = match l {
                    Level::Succ(a) => Level::Succ(self.level(a)?),
                    Level::Max(a, b) => Level::Max(self.level(a)?, self.level(b)?),
                    Level::IMax(a, b) => Level::IMax(self.level(a)?, self.level(b)?),
                    Level::Param(n) => Level::Param(self.name(n)?),
                    Level::Zero => unreachable!("classify never makes a zero level record"),
                };
                self.level_ids.define("level", id, self.levels.len())?;
                self.levels.push(lvl);
                Ok(())
            }
            Rec::Expr { id, e } => {
                let e = match e {
                    Expr::BVar(i) => Expr::BVar(i),
                    Expr::Sort(l) => Expr::Sort(self.level(l)?),
                    Expr::Const { name, mut levels } => {
                        // In place: no new allocation per constant.
                        for l in levels.iter_mut() {
                            *l = self.level(*l)?;
                        }
                        Expr::Const { name: self.name(name)?, levels }
                    }
                    Expr::App { f, a } => Expr::App { f: self.expr(f)?, a: self.expr(a)? },
                    Expr::Lam { name, ty, body, bi } => {
                        Expr::Lam { name: self.name(name)?, ty: self.expr(ty)?, body: self.expr(body)?, bi }
                    }
                    Expr::Pi { name, ty, body, bi } => {
                        Expr::Pi { name: self.name(name)?, ty: self.expr(ty)?, body: self.expr(body)?, bi }
                    }
                    Expr::Let { name, ty, val, body, nondep } => Expr::Let {
                        name: self.name(name)?,
                        ty: self.expr(ty)?,
                        val: self.expr(val)?,
                        body: self.expr(body)?,
                        nondep,
                    },
                    Expr::Proj { type_name, idx, structure } => {
                        Expr::Proj { type_name: self.name(type_name)?, idx, structure: self.expr(structure)? }
                    }
                    lit @ (Expr::NatLit(_) | Expr::StrLit(_)) => lit,
                };
                self.expr_ids.define("expression", id, self.exprs.len())?;
                self.exprs.push(e);
                Ok(())
            }
            Rec::Decl(d) => {
                let mut d = *d;
                d.map_names(&mut |n| self.name(n))?;
                for e in d.roots() {
                    self.expr(e)?;
                }
                if self.expr_ids.sparse.is_some() {
                    // Every root resolves (checked just above).
                    d.map_exprs(&mut |e| self.expr_ids.get(e, self.exprs.len()).expect("checked above"));
                }
                let idx = self.decls.len();
                for n in d.defined_names() {
                    if self.decl_of_name.insert(n, idx).is_some() {
                        return Err(format!("constant defined twice (name id {n})"));
                    }
                }
                self.decls.push(d);
                Ok(())
            }
        }
    }
}

/// A record, checked as far as it can be on its own; ids are still the file's.
#[derive(Debug)]
enum Rec {
    Meta(Box<Meta>),
    Name { id: u32, name: Name },
    Level { id: u32, l: Level },
    Expr { id: u32, e: Expr },
    Decl(Box<Decl>),
}

/// Everything about a record that does not depend on the records before it:
/// exactly one payload, the right kind of id, the meta record first, the
/// format version and well-formed literals. Runs on many threads at once.
fn classify(r: Line, first: bool) -> Result<Rec, String> {
    let Line {
        in_id,
        il,
        ie,
        str,
        num,
        succ,
        max,
        imax,
        param,
        bvar,
        sort,
        cnst,
        app,
        lam,
        forall_e,
        let_e,
        proj,
        nat_val,
        str_val,
        meta,
        axiom,
        def,
        thm,
        opaque,
        quot,
        inductive,
    } = r;

    let name_payloads = [str.is_some(), num.is_some()];
    let level_payloads = [succ.is_some(), max.is_some(), imax.is_some(), param.is_some()];
    let expr_payloads = [
        bvar.is_some(),
        sort.is_some(),
        cnst.is_some(),
        app.is_some(),
        lam.is_some(),
        forall_e.is_some(),
        let_e.is_some(),
        proj.is_some(),
        nat_val.is_some(),
        str_val.is_some(),
    ];
    let decl_payloads =
        [axiom.is_some(), def.is_some(), thm.is_some(), opaque.is_some(), quot.is_some(), inductive.is_some()];
    let count = |v: &[bool]| v.iter().filter(|x| **x).count();
    let (np, lp, ep, dp, mp) = (
        count(&name_payloads),
        count(&level_payloads),
        count(&expr_payloads),
        count(&decl_payloads),
        meta.is_some() as usize,
    );
    if np + lp + ep + dp + mp != 1 {
        return Err("record must have exactly one payload".into());
    }
    if first != (mp == 1) {
        return Err("the meta record must be the first line, and only the first".into());
    }
    let ids = (in_id.is_some(), il.is_some(), ie.is_some());
    let ok_ids = match (np, lp, ep) {
        (1, _, _) => ids == (true, false, false),
        (_, 1, _) => ids == (false, true, false),
        (_, _, 1) => ids == (false, false, true),
        _ => ids == (false, false, false),
    };
    if !ok_ids {
        return Err("record has the wrong kind of id for its payload".into());
    }

    if let Some(m) = meta {
        if !m.format.version.starts_with("3.") {
            return Err(format!("unsupported export format {}, expected 3.x", m.format.version));
        }
        return Ok(Rec::Meta(Box::new(m)));
    }
    if let Some(id) = in_id {
        let name = if let Some(s) = str {
            Name::Str { pre: s.pre, s: s.str }
        } else {
            let n = num.expect("checked above");
            Name::Num { pre: n.pre, n: n.i }
        };
        return Ok(Rec::Name { id, name });
    }
    if let Some(id) = il {
        let l = if let Some(a) = succ {
            Level::Succ(a)
        } else if let Some([a, b]) = max {
            Level::Max(a, b)
        } else if let Some([a, b]) = imax {
            Level::IMax(a, b)
        } else {
            Level::Param(param.expect("checked above"))
        };
        return Ok(Rec::Level { id, l });
    }
    if let Some(id) = ie {
        let e = if let Some(i) = bvar {
            Expr::BVar(i)
        } else if let Some(l) = sort {
            Expr::Sort(l)
        } else if let Some(c) = cnst {
            Expr::Const { name: c.name, levels: c.us.into_boxed_slice() }
        } else if let Some(a) = app {
            Expr::App { f: a.f, a: a.arg }
        } else if let Some(x) = lam {
            Expr::Lam { name: x.name, ty: x.r#type, body: x.body, bi: x.binder_info }
        } else if let Some(x) = forall_e {
            Expr::Pi { name: x.name, ty: x.r#type, body: x.body, bi: x.binder_info }
        } else if let Some(x) = let_e {
            Expr::Let { name: x.name, ty: x.r#type, val: x.value, body: x.body, nondep: x.nondep }
        } else if let Some(p) = proj {
            Expr::Proj { type_name: p.type_name, idx: p.idx, structure: p.structure }
        } else if let Some(n) = nat_val {
            let canonical = !n.is_empty() && n.bytes().all(|c| c.is_ascii_digit()) && (n == "0" || !n.starts_with('0'));
            if !canonical {
                return Err(format!("malformed natural-number literal {n:?}"));
            }
            Expr::NatLit(n.into_boxed_str())
        } else {
            Expr::StrLit(str_val.expect("checked above").into_boxed_str())
        };
        return Ok(Rec::Expr { id, e });
    }
    let d = if let Some(x) = axiom {
        Decl::Axiom(x)
    } else if let Some(x) = def {
        Decl::Def(x)
    } else if let Some(x) = thm {
        Decl::Thm(x)
    } else if let Some(x) = opaque {
        Decl::Opaque(x)
    } else if let Some(x) = quot {
        Decl::Quot(x)
    } else {
        Decl::Inductive(inductive.expect("checked above"))
    };
    Ok(Rec::Decl(Box::new(d)))
}

impl Env {
    /// Render a name as Lean would print it, e.g. `Nat.add_comm`.
    pub fn name_str(&self, id: NameId) -> String {
        let mut parts = Vec::new();
        let mut cur = id;
        loop {
            match &self.names[cur as usize] {
                Name::Anon => break,
                Name::Str { pre, s } => {
                    parts.push(s.clone());
                    cur = *pre;
                }
                Name::Num { pre, n } => {
                    parts.push(n.to_string());
                    cur = *pre;
                }
            }
        }
        if parts.is_empty() {
            return "[anonymous]".into();
        }
        parts.reverse();
        parts.join(".")
    }

    /// Find a declaration by its printed name (any constant it defines).
    pub fn find_decl(&self, printed: &str) -> Option<usize> {
        self.decl_of_name.iter().find(|(n, _)| self.name_str(**n) == printed).map(|(_, &i)| i)
    }

    /// `find_decl` for several names at once, in a single pass.
    pub fn find_decls(&self, printed: &[&str]) -> Vec<Option<usize>> {
        let mut found = vec![None; printed.len()];
        for (&n, &i) in &self.decl_of_name {
            let s = self.name_str(n);
            if let Some(k) = printed.iter().position(|p| *p == s) {
                found[k] = Some(i);
            }
        }
        found
    }
}

#[cfg(test)]
mod fast_tests {
    use super::*;

    fn slow(line: &str) -> Result<Rec, String> {
        serde_json::from_str::<Line>(line).map_err(|e| e.to_string()).and_then(|r| classify(r, false))
    }

    /// Whatever the fast path accepts, the strict reader accepts the same way.
    fn agrees(line: &str) -> bool {
        match fast(line.as_bytes()) {
            None => false,
            Some(r) => {
                let s = slow(line).unwrap_or_else(|e| panic!("fast path accepted {line:?}, strict reader says {e}"));
                assert_eq!(format!("{r:?}"), format!("{s:?}"), "{line}");
                true
            }
        }
    }

    #[test]
    fn the_fast_path_reads_every_common_shape_as_the_strict_reader_does() {
        for line in [
            r#"{"app":{"arg":2,"fn":7},"ie":8}"#,
            r#"{"app":{"arg":0,"fn":4294967295},"ie":4294967295}"#,
            r#"{"ie":38,"lam":{"binderInfo":"default","body":1,"name":14,"type":24}}"#,
            r#"{"ie":38,"lam":{"binderInfo":"strictImplicit","body":1,"name":14,"type":24}}"#,
            r#"{"forallE":{"binderInfo":"instImplicit","body":141,"name":38,"type":138},"ie":166}"#,
            r#"{"forallE":{"binderInfo":"implicit","body":5,"name":3,"type":0},"ie":6}"#,
            r#"{"const":{"name":1,"us":[1]},"ie":7}"#,
            r#"{"const":{"name":61,"us":[]},"ie":316}"#,
            r#"{"const":{"name":3090,"us":[12,12,12,12,12]},"ie":16855}"#,
            r#"{"in":8,"num":{"i":18446744073709551615,"pre":7}}"#,
            r#"{"in":7,"str":{"pre":6,"str":"_hyg"}}"#,
            r#"{"in":7,"str":{"pre":6,"str":"α₁ ∀"}}"#,
            r#"{"in":7,"str":{"pre":6,"str":""}}"#,
            r#"{"ie":3312,"letE":{"body":3311,"name":760,"nondep":false,"type":3266,"value":3302}}"#,
            r#"{"ie":3312,"letE":{"body":3311,"name":760,"nondep":true,"type":3266,"value":3302}}"#,
            r#"{"ie":170,"proj":{"idx":0,"struct":1,"typeName":31}}"#,
            r#"{"bvar":0,"ie":1}"#,
            r#"{"ie":0,"sort":1}"#,
        ] {
            assert!(agrees(line), "the fast path should read {line}");
        }
    }

    #[test]
    fn anything_unusual_is_left_to_the_strict_reader() {
        for line in [
            r#"{"app":{"arg":01,"fn":2},"ie":3}"#,
            r#"{"app":{"arg":1,"fn":2},"ie":4294967296}"#,
            r#"{"app":{"arg":1e2,"fn":2},"ie":3}"#,
            r#"{"app":{"arg":1.0,"fn":2},"ie":3}"#,
            r#"{"app":{"arg":-1,"fn":2},"ie":3}"#,
            r#"{"app": {"arg":1,"fn":2},"ie":3}"#,
            r#"{"app":{"fn":2,"arg":1},"ie":3}"#,
            r#"{"app":{"arg":1,"fn":2},"ie":3,"x":1}"#,
            r#"{"app":{"arg":1,"fn":2},"ie":3}x"#,
            r#"{"app":{"arg":1,"fn":2},"ie":3}}"#,
            r#"{"app":{"arg":1,"fn":2}}"#,
            r#"{"ie":1,"lam":{"binderInfo":"auto","body":1,"name":1,"type":1}}"#,
            r#"{"in":7,"str":{"pre":6,"str":"a\"b"}}"#,
            r#"{"in":7,"str":{"pre":6,"str":"a\u0041"}}"#,
            r#"{"in":7,"num":{"i":18446744073709551616,"pre":7}}"#,
            r#"{"const":{"name":1,"us":[1,]},"ie":7}"#,
            r#"{"const":{"name":1,"us":[,1]},"ie":7}"#,
            r#"{"ie":1,"letE":{"body":1,"name":1,"nondep":null,"type":1,"value":1}}"#,
            r#"{"ie":1,"sort":1,"sort":2}"#,
        ] {
            // Either the fast path declines, or (checked inside) it agrees.
            let _ = agrees(line);
            assert!(fast(line.as_bytes()).is_none(), "the fast path must decline {line}");
        }
    }
}
