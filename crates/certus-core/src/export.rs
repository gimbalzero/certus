//! Reader for the `lean4export` NDJSON format, version 3.x.
//!
//! Each line is one JSON record. Names, universe levels and expressions get
//! dense numeric ids (`in`, `il`, `ie`), and records may refer only to ids that
//! were defined earlier, so the file is a topologically ordered DAG. The
//! reader *fails closed*: unknown record kinds, unknown fields, forward
//! references, gaps in ids and duplicate declarations are all errors.
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

struct Builder {
    meta: Option<Meta>,
    names: Vec<Name>,
    name_canon: Vec<NameId>,
    name_index: HashMap<NameKey, NameId>,
    levels: Vec<Level>,
    exprs: Vec<Expr>,
    decls: Vec<Decl>,
    decl_of_name: HashMap<NameId, usize>,
}

/// Parse a whole export. Fails on the first malformed record.
pub fn parse<R: BufRead>(mut reader: R) -> Result<Env, ParseError> {
    let mut b = Builder {
        meta: None,
        names: vec![Name::Anon],
        name_canon: vec![0],
        name_index: HashMap::new(),
        levels: vec![Level::Zero],
        exprs: Vec::new(),
        decls: Vec::new(),
        decl_of_name: HashMap::new(),
    };
    let mut buf = String::new();
    let (mut lines, mut bytes) = (0u64, 0u64);
    loop {
        buf.clear();
        let n =
            reader.read_line(&mut buf).map_err(|e| ParseError { line: lines + 1, msg: format!("read error: {e}") })?;
        if n == 0 {
            break;
        }
        lines += 1;
        bytes += n as u64;
        let text = buf.trim_end();
        if text.is_empty() {
            continue;
        }
        let rec: Line = serde_json::from_str(text).map_err(|e| ParseError { line: lines, msg: e.to_string() })?;
        b.add(rec, lines == 1).map_err(|msg| ParseError { line: lines, msg })?;
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

fn expect_id(kind: &str, got: u32, next: usize) -> Result<(), String> {
    if got as usize == next { Ok(()) } else { Err(format!("{kind} id {got} out of sequence (expected {next})")) }
}

impl Builder {
    fn name(&self, id: NameId) -> Result<NameId, String> {
        self.name_canon.get(id as usize).copied().ok_or_else(|| format!("reference to undefined name {id}"))
    }

    fn level(&self, id: LevelId) -> Result<LevelId, String> {
        if (id as usize) < self.levels.len() { Ok(id) } else { Err(format!("reference to undefined level {id}")) }
    }

    fn expr(&self, id: ExprId) -> Result<ExprId, String> {
        if (id as usize) < self.exprs.len() { Ok(id) } else { Err(format!("reference to undefined expression {id}")) }
    }

    fn add(&mut self, r: Line, first: bool) -> Result<(), String> {
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
            self.meta = Some(m);
            return Ok(());
        }

        if let Some(id) = in_id {
            expect_id("name", id, self.names.len())?;
            let (name, key) = if let Some(s) = str {
                let pre = self.name(s.pre)?;
                (Name::Str { pre, s: s.str.clone() }, NameKey::Str(pre, s.str))
            } else {
                let n = num.expect("checked above");
                let pre = self.name(n.pre)?;
                (Name::Num { pre, n: n.i }, NameKey::Num(pre, n.i))
            };
            let canon = *self.name_index.entry(key).or_insert(id);
            self.names.push(name);
            self.name_canon.push(canon);
            return Ok(());
        }

        if let Some(id) = il {
            expect_id("level", id, self.levels.len())?;
            let lvl = if let Some(a) = succ {
                Level::Succ(self.level(a)?)
            } else if let Some([a, b]) = max {
                Level::Max(self.level(a)?, self.level(b)?)
            } else if let Some([a, b]) = imax {
                Level::IMax(self.level(a)?, self.level(b)?)
            } else {
                Level::Param(self.name(param.expect("checked above"))?)
            };
            self.levels.push(lvl);
            return Ok(());
        }

        if let Some(id) = ie {
            expect_id("expression", id, self.exprs.len())?;
            let e = if let Some(i) = bvar {
                Expr::BVar(i)
            } else if let Some(l) = sort {
                Expr::Sort(self.level(l)?)
            } else if let Some(c) = cnst {
                let levels = c.us.iter().map(|&l| self.level(l)).collect::<Result<Vec<_>, _>>()?;
                Expr::Const { name: self.name(c.name)?, levels: levels.into_boxed_slice() }
            } else if let Some(a) = app {
                Expr::App { f: self.expr(a.f)?, a: self.expr(a.arg)? }
            } else if let Some(x) = lam {
                Expr::Lam {
                    name: self.name(x.name)?,
                    ty: self.expr(x.r#type)?,
                    body: self.expr(x.body)?,
                    bi: x.binder_info,
                }
            } else if let Some(x) = forall_e {
                Expr::Pi {
                    name: self.name(x.name)?,
                    ty: self.expr(x.r#type)?,
                    body: self.expr(x.body)?,
                    bi: x.binder_info,
                }
            } else if let Some(x) = let_e {
                Expr::Let {
                    name: self.name(x.name)?,
                    ty: self.expr(x.r#type)?,
                    val: self.expr(x.value)?,
                    body: self.expr(x.body)?,
                    nondep: x.nondep,
                }
            } else if let Some(p) = proj {
                Expr::Proj { type_name: self.name(p.type_name)?, idx: p.idx, structure: self.expr(p.structure)? }
            } else if let Some(n) = nat_val {
                let canonical =
                    !n.is_empty() && n.bytes().all(|c| c.is_ascii_digit()) && (n == "0" || !n.starts_with('0'));
                if !canonical {
                    return Err(format!("malformed natural-number literal {n:?}"));
                }
                Expr::NatLit(n.into_boxed_str())
            } else {
                Expr::StrLit(str_val.expect("checked above").into_boxed_str())
            };
            self.exprs.push(e);
            return Ok(());
        }

        let mut d = if let Some(x) = axiom {
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
        d.map_names(&mut |n| self.name(n))?;
        for e in d.roots() {
            self.expr(e)?;
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
}
