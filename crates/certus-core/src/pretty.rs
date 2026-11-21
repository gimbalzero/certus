//! A deterministic pretty-printer for export expressions, so that a human can
//! read exactly *what* a checked theorem states.
//!
//! The output is Lean-like text built only from the export itself: binder
//! names come from the export, and nothing is elaborated or looked up outside
//! it. There are two modes:
//!
//! * **raw** (`Options::RAW`): every application is printed exactly as the
//!   kernel sees it, with every argument, instance and universe level shown,
//!   e.g. `HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b`.
//! * **notation** (`Options::NOTATION`): common operators are shown with their
//!   usual syntax (`a + b`, `a = b`, `¬p`, `∃ x, p`, numerals), and implicit or
//!   instance arguments of constants are hidden when an explicit argument
//!   follows them. This is display-only: it never changes what is printed for
//!   the parts it does not recognise, and raw output stays available.
//!
//! A bound variable that is shadowed by a closer binder with the same name is
//! printed with a dagger, `x✝` (or `x✝¹`, `x✝²`, … when that alone would be
//! ambiguous), and
//! a constant whose name is hidden by a binder is printed as `_root_.Name`.

use crate::export::{BinderInfo, Decl, Env, Expr, ExprId, Level, LevelId, Name, NameId};
use std::collections::HashMap;

/// How to print expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Options {
    /// Use operator notation and hide inferable arguments.
    pub notation: bool,
}

impl Options {
    pub const RAW: Options = Options { notation: false };
    pub const NOTATION: Options = Options { notation: true };
}

// Precedences, following Lean 4's built-in notation.
const BINDER: u32 = 0;
const IFF: u32 = 20;
const ARROW: u32 = 25;
const MAX: u32 = 1024;
const ARG: u32 = MAX + 1;

#[derive(Clone, Copy)]
enum Fixity {
    /// `lhs op rhs`, with the required precedences of each side.
    Infix { lhs: u32, rhs: u32 },
    /// `op arg`.
    Prefix { arg: u32 },
}

/// A notation for `head a₁ … aₙ` that shows only the last one or two arguments.
struct Notation {
    head: &'static str,
    arity: usize,
    op: &'static str,
    prec: u32,
    fixity: Fixity,
}

const fn infix(head: &'static str, arity: usize, op: &'static str, prec: u32, lhs: u32, rhs: u32) -> Notation {
    Notation { head, arity, op, prec, fixity: Fixity::Infix { lhs, rhs } }
}

const NOTATIONS: &[Notation] = &[
    infix("HAdd.hAdd", 6, "+", 65, 65, 66),
    infix("HSub.hSub", 6, "-", 65, 65, 66),
    infix("HMul.hMul", 6, "*", 70, 70, 71),
    infix("HDiv.hDiv", 6, "/", 70, 70, 71),
    infix("HMod.hMod", 6, "%", 70, 70, 71),
    infix("HPow.hPow", 6, "^", 75, 76, 75),
    infix("Eq", 3, "=", 50, 51, 51),
    infix("Ne", 3, "≠", 50, 51, 51),
    infix("LE.le", 4, "≤", 50, 51, 51),
    infix("LT.lt", 4, "<", 50, 51, 51),
    infix("GE.ge", 4, "≥", 50, 51, 51),
    infix("GT.gt", 4, ">", 50, 51, 51),
    infix("And", 2, "∧", 35, 36, 35),
    infix("Or", 2, "∨", 30, 31, 30),
    infix("Iff", 2, "↔", IFF, IFF + 1, IFF + 1),
    Notation { head: "Not", arity: 1, op: "¬", prec: 40, fixity: Fixity::Prefix { arg: 40 } },
    Notation { head: "Neg.neg", arity: 3, op: "-", prec: 75, fixity: Fixity::Prefix { arg: 75 } },
];

/// Pretty-prints expressions of one export. Caches results of variable
/// occurrence checks and constant signatures, so reuse it for many terms.
pub struct Printer<'a> {
    env: &'a Env,
    opts: Options,
    has_var_cache: HashMap<(ExprId, u64), bool>,
    binders_cache: HashMap<NameId, Vec<BinderInfo>>,
    notations: HashMap<NameId, &'static Notation>,
    special: HashMap<NameId, &'static str>,
}

impl<'a> Printer<'a> {
    pub fn new(env: &'a Env, opts: Options) -> Self {
        let mut notations = HashMap::new();
        let mut special = HashMap::new();
        if opts.notation {
            // Map notation heads to name ids once, so printing compares ids.
            // Notations that need more than an operator: numerals and `∃`.
            let wanted = ["OfNat.ofNat", "Exists"];
            for (id, _) in env.names.iter().enumerate() {
                let id = id as NameId;
                if env.name_canon[id as usize] != id {
                    continue;
                }
                let s = env.name_str(id);
                if let Some(n) = NOTATIONS.iter().find(|n| n.head == s) {
                    notations.insert(id, n);
                } else if let Some(w) = wanted.iter().find(|w| **w == s) {
                    special.insert(id, *w);
                }
            }
        }
        Printer { env, opts, has_var_cache: HashMap::new(), binders_cache: HashMap::new(), notations, special }
    }

    /// Print a closed expression.
    pub fn expr(&mut self, e: ExprId) -> String {
        let mut ctx = Vec::new();
        self.go(e, &mut ctx, BINDER, true)
    }

    /// Print a universe level.
    pub fn level(&self, l: LevelId) -> String {
        level_to_string(self.env, l)
    }

    fn go(&mut self, e: ExprId, ctx: &mut Vec<String>, req: u32, rightmost: bool) -> String {
        let env = self.env;
        match &env.exprs[e as usize] {
            Expr::BVar(i) => var_name(ctx, *i),
            Expr::Sort(l) => {
                let (s, atomic) = sort_str(env, *l);
                if atomic { s } else { paren(s, MAX < req) }
            }
            Expr::Const { name, levels } => self.const_str(*name, levels, ctx),
            Expr::NatLit(n) => n.to_string(),
            Expr::StrLit(s) => quote(s),
            Expr::App { .. } => self.app(e, ctx, req, rightmost),
            Expr::Pi { .. } => self.pi(e, ctx, req, rightmost),
            Expr::Lam { .. } => self.lam(e, ctx, req, rightmost),
            Expr::Let { name, ty, val, body, nondep } => {
                let wrap = req > BINDER && !rightmost;
                let t = self.go(*ty, ctx, BINDER, true);
                let v = self.go(*val, ctx, BINDER, true);
                let n = binder_name(env, *name);
                ctx.push(n.clone());
                let b = self.go(*body, ctx, BINDER, true);
                ctx.pop();
                let kw = if *nondep { "have" } else { "let" };
                paren(format!("{kw} {n} : {t} := {v}; {b}"), wrap)
            }
            Expr::Proj { idx, structure, .. } => {
                let mut s = self.go(*structure, ctx, ARG, false);
                if matches!(env.exprs[*structure as usize], Expr::NatLit(_)) {
                    s = format!("({s})");
                }
                format!("{s}.{}", idx + 1)
            }
        }
    }

    fn const_str(&self, name: NameId, levels: &[LevelId], ctx: &[String]) -> String {
        let mut s = name_to_string(self.env, name);
        if ctx.contains(&s) {
            s = format!("_root_.{s}");
        }
        if !self.opts.notation && !levels.is_empty() {
            let ls: Vec<String> = levels.iter().map(|&l| level_to_string(self.env, l)).collect();
            s = format!("{s}.{{{}}}", ls.join(", "));
        }
        s
    }

    fn app(&mut self, e: ExprId, ctx: &mut Vec<String>, req: u32, rightmost: bool) -> String {
        let env = self.env;
        let mut args = Vec::new();
        let mut head = e;
        while let Expr::App { f, a } = &env.exprs[head as usize] {
            args.push(*a);
            head = *f;
        }
        args.reverse();

        let mut at = false;
        let mut shown: Vec<ExprId> = args.clone();
        if self.opts.notation {
            if let Expr::Const { name, .. } = &env.exprs[head as usize] {
                if let Some(s) = self.notation(*name, &args, ctx, req, rightmost) {
                    return s;
                }
                // Hide implicit and instance arguments when an explicit one follows them.
                let bis = self.const_binders(*name);
                let explicit = |i: usize| bis.get(i).is_none_or(|b| *b == BinderInfo::Default);
                let last_explicit = (0..args.len()).rev().find(|&i| explicit(i));
                let hidden: Vec<usize> = (0..args.len()).filter(|&i| !explicit(i)).collect();
                if !hidden.is_empty() {
                    if hidden.iter().all(|&i| last_explicit.is_some_and(|l| i < l)) {
                        shown = (0..args.len()).filter(|&i| explicit(i)).map(|i| args[i]).collect();
                    } else {
                        at = true;
                    }
                }
            }
        }

        let mut s = self.go(head, ctx, MAX, false);
        if at {
            s = format!("@{s}");
        }
        for a in shown {
            s.push(' ');
            s.push_str(&self.go(a, ctx, ARG, false));
        }
        paren(s, MAX < req)
    }

    fn notation(
        &mut self,
        head: NameId,
        args: &[ExprId],
        ctx: &mut Vec<String>,
        req: u32,
        rightmost: bool,
    ) -> Option<String> {
        if let Some(n) = self.notations.get(&head).copied() {
            if args.len() != n.arity {
                return None;
            }
            let wrap = n.prec < req;
            let inner_right = wrap || rightmost;
            return Some(match n.fixity {
                Fixity::Infix { lhs, rhs } => {
                    let a = self.go(args[n.arity - 2], ctx, lhs, false);
                    let b = self.go(args[n.arity - 1], ctx, rhs, inner_right);
                    paren(format!("{a} {} {b}", n.op), wrap)
                }
                Fixity::Prefix { arg } => {
                    let a = self.go(args[n.arity - 1], ctx, arg, inner_right);
                    paren(format!("{}{a}", n.op), wrap)
                }
            });
        }
        match self.special.get(&head).copied() {
            Some("OfNat.ofNat") if args.len() == 3 => match &self.env.exprs[args[1] as usize] {
                Expr::NatLit(n) => Some(n.to_string()),
                _ => None,
            },
            Some("Exists") if args.len() == 2 => {
                let Expr::Lam { name, body, .. } = &self.env.exprs[args[1] as usize] else { return None };
                let (name, body) = (*name, *body);
                let wrap = req > BINDER && !rightmost;
                let n = binder_name(self.env, name);
                ctx.push(n.clone());
                let b = self.go(body, ctx, BINDER, true);
                ctx.pop();
                Some(paren(format!("∃ {n}, {b}"), wrap))
            }
            _ => None,
        }
    }

    fn pi(&mut self, e: ExprId, ctx: &mut Vec<String>, req: u32, rightmost: bool) -> String {
        let env = self.env;
        let Expr::Pi { ty, body, bi, .. } = &env.exprs[e as usize] else { unreachable!() };
        let (ty, body, bi) = (*ty, *body, *bi);
        if bi == BinderInfo::Default && !self.has_var(body, 0) {
            // Non-dependent: an arrow. Its binder is never referenced or shown, so it
            // occupies a slot under an empty name that cannot shadow anything.
            let wrap = ARROW < req;
            let a = self.go(ty, ctx, ARROW + 1, false);
            ctx.push(String::new());
            let b = self.go(body, ctx, ARROW, wrap || rightmost);
            ctx.pop();
            return paren(format!("{a} → {b}"), wrap);
        }
        let wrap = req > BINDER && !rightmost;
        let depth = ctx.len();
        let mut groups = Vec::new();
        let mut cur = e;
        while let Expr::Pi { name, ty, body, bi } = &env.exprs[cur as usize] {
            let (name, ty, body, bi) = (*name, *ty, *body, *bi);
            if bi == BinderInfo::Default && !self.has_var(body, 0) {
                break;
            }
            groups.push(self.binder(name, ty, bi, ctx, true));
            cur = body;
        }
        let b = self.go(cur, ctx, BINDER, true);
        ctx.truncate(depth);
        paren(format!("∀ {}, {b}", groups.join(" ")), wrap)
    }

    fn lam(&mut self, e: ExprId, ctx: &mut Vec<String>, req: u32, rightmost: bool) -> String {
        let env = self.env;
        let wrap = req > BINDER && !rightmost;
        let depth = ctx.len();
        let mut groups = Vec::new();
        let mut cur = e;
        while let Expr::Lam { name, ty, body, bi } = &env.exprs[cur as usize] {
            let (name, ty, body, bi) = (*name, *ty, *body, *bi);
            groups.push(self.binder(name, ty, bi, ctx, !self.opts.notation));
            cur = body;
        }
        let b = self.go(cur, ctx, BINDER, true);
        ctx.truncate(depth);
        paren(format!("fun {} => {b}", groups.join(" ")), wrap)
    }

    /// Print one binder (its type in the current context) and push its name.
    fn binder(&mut self, name: NameId, ty: ExprId, bi: BinderInfo, ctx: &mut Vec<String>, typed: bool) -> String {
        let n = binder_name(self.env, name);
        let t = if typed { Some(self.go(ty, ctx, BINDER, true)) } else { None };
        let inaccessible = n.ends_with('✝');
        ctx.push(n.clone());
        let (open, close) = match bi {
            BinderInfo::Default => ("(", ")"),
            BinderInfo::Implicit => ("{", "}"),
            BinderInfo::StrictImplicit => ("⦃", "⦄"),
            BinderInfo::InstImplicit => ("[", "]"),
        };
        match t {
            Some(t) if bi == BinderInfo::InstImplicit && inaccessible => format!("[{t}]"),
            Some(t) => format!("{open}{n} : {t}{close}"),
            None if bi == BinderInfo::Default => n,
            None => format!("{open}{n}{close}"),
        }
    }

    /// Binder infos of the leading Π-binders of a constant's type, if the
    /// constant is defined in this export.
    fn const_binders(&mut self, name: NameId) -> Vec<BinderInfo> {
        if let Some(v) = self.binders_cache.get(&name) {
            return v.clone();
        }
        let mut v = Vec::new();
        if let Some(info) = const_info(self.env, name) {
            let mut cur = info.ty;
            while let Expr::Pi { body, bi, .. } = &self.env.exprs[cur as usize] {
                v.push(*bi);
                cur = *body;
            }
        }
        self.binders_cache.insert(name, v.clone());
        v
    }

    /// Does `e` mention the loose bound variable `k`?
    fn has_var(&mut self, e: ExprId, k: u64) -> bool {
        if let Some(&r) = self.has_var_cache.get(&(e, k)) {
            return r;
        }
        let r = match &self.env.exprs[e as usize] {
            Expr::BVar(i) => *i == k,
            Expr::Sort(_) | Expr::Const { .. } | Expr::NatLit(_) | Expr::StrLit(_) => false,
            Expr::App { f, a } => {
                let (f, a) = (*f, *a);
                self.has_var(f, k) || self.has_var(a, k)
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                let (ty, body) = (*ty, *body);
                self.has_var(ty, k) || self.has_var(body, k + 1)
            }
            Expr::Let { ty, val, body, .. } => {
                let (ty, val, body) = (*ty, *val, *body);
                self.has_var(ty, k) || self.has_var(val, k) || self.has_var(body, k + 1)
            }
            Expr::Proj { structure, .. } => {
                let s = *structure;
                self.has_var(s, k)
            }
        };
        self.has_var_cache.insert((e, k), r);
        r
    }
}

fn paren(s: String, wrap: bool) -> String {
    if wrap { format!("({s})") } else { s }
}

const SUPERSCRIPTS: [char; 10] = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];

fn superscript(n: usize) -> String {
    n.to_string().bytes().map(|b| SUPERSCRIPTS[(b - b'0') as usize]).collect()
}

/// The display name of de Bruijn index `i`.
///
/// A variable that no closer binder shadows keeps its own name. A shadowed one
/// is shown as `x✝ⁿ`, where `n` counts the closer binders of the same family
/// (`x` and the inaccessible `x✝` are one family); a plain `x` hidden by one
/// plain `x` is shown as `x✝`, as Lean does. Every variable in scope thus gets
/// a distinct display name.
fn var_name(ctx: &[String], i: u64) -> String {
    let Some(pos) = (ctx.len() as u64).checked_sub(i + 1) else { return format!("#{i}") };
    let pos = pos as usize;
    let name = &ctx[pos];
    let base = name.trim_end_matches('✝');
    let closer: Vec<&String> = ctx[pos + 1..].iter().filter(|n| n.trim_end_matches('✝') == base).collect();
    match closer.len() {
        0 => name.clone(),
        1 if name == base && closer[0] == name => format!("{base}✝"),
        k => format!("{base}✝{}", superscript(k)),
    }
}

/// The name a binder is shown with. Anonymous and hygienic (macro-scoped)
/// names are inaccessible in Lean, so they get a dagger like Lean prints them.
fn binder_name(env: &Env, id: NameId) -> String {
    let mut parts = Vec::new();
    let mut cur = id;
    loop {
        match &env.names[cur as usize] {
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
    parts.reverse();
    if let Some(p) = parts.iter().position(|s| s == "_@") {
        parts.truncate(p);
        let base = if parts.is_empty() { "a".to_string() } else { join_escaped(&parts) };
        return format!("{base}✝");
    }
    if parts.is_empty() {
        return "a✝".to_string();
    }
    join_escaped(&parts)
}

fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    let Some(c) = cs.next() else { return false };
    (c.is_alphabetic() || c == '_') && cs.all(|c| c.is_alphanumeric() || "_'!?".contains(c) || is_subscript(c))
}

fn is_subscript(c: char) -> bool {
    ('₀'..='₉').contains(&c) || ('ₐ'..='ₜ').contains(&c) || ('ᵢ'..='ᵪ').contains(&c)
}

fn join_escaped(parts: &[String]) -> String {
    let ps: Vec<String> = parts
        .iter()
        .map(|p| if is_ident(p) || p.bytes().all(|b| b.is_ascii_digit()) { p.clone() } else { format!("«{p}»") })
        .collect();
    ps.join(".")
}

/// A constant name as Lean source would write it, with `«»` around
/// components that are not plain identifiers.
pub fn name_to_string(env: &Env, id: NameId) -> String {
    let mut parts = Vec::new();
    let mut cur = id;
    loop {
        match &env.names[cur as usize] {
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
    join_escaped(&parts)
}

/// A string literal with Lean escapes.
fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 || c == '\u{7f}' => out.push_str(&format!("\\x{:02x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Split a level into `base + k` successors.
fn succs(env: &Env, mut l: LevelId) -> (LevelId, u64) {
    let mut k = 0;
    while let Level::Succ(p) = env.levels[l as usize] {
        k += 1;
        l = p;
    }
    (l, k)
}

/// Render a level; the flag says whether it is atomic (needs no parentheses
/// as an argument).
fn level_str(env: &Env, l: LevelId) -> (String, bool) {
    let (base, k) = succs(env, l);
    let arg = |x: LevelId| {
        let (s, atomic) = level_str(env, x);
        paren(s, !atomic)
    };
    let (b, atomic) = match env.levels[base as usize] {
        Level::Zero => return (k.to_string(), true),
        Level::Param(n) => (name_to_string(env, n), true),
        Level::Max(a, b) => (format!("max {} {}", arg(a), arg(b)), false),
        Level::IMax(a, b) => (format!("imax {} {}", arg(a), arg(b)), false),
        Level::Succ(_) => unreachable!("stripped above"),
    };
    if k == 0 { (b, atomic) } else { (format!("{}+{k}", paren(b, !atomic)), false) }
}

/// Render a universe level, e.g. `0`, `u`, `u+1`, `max u v`.
pub fn level_to_string(env: &Env, l: LevelId) -> String {
    level_str(env, l).0
}

fn sort_str(env: &Env, l: LevelId) -> (String, bool) {
    match env.levels[l as usize] {
        Level::Zero => ("Prop".into(), true),
        Level::Succ(p) => match env.levels[p as usize] {
            Level::Zero => ("Type".into(), true),
            _ => {
                let (s, atomic) = level_str(env, p);
                (format!("Type {}", paren(s, !atomic)), false)
            }
        },
        _ => {
            let (s, atomic) = level_str(env, l);
            (format!("Sort {}", paren(s, !atomic)), false)
        }
    }
}

/// Print a closed expression.
pub fn expr_to_string(env: &Env, e: ExprId, opts: Options) -> String {
    Printer::new(env, opts).expr(e)
}

/// One constant: a theorem, definition, axiom, or a type, constructor or
/// recursor of an inductive block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstInfo {
    pub name: NameId,
    /// `axiom`, `def`, `thm`, `opaque`, `quot`, `inductive`, `ctor` or `rec`.
    pub kind: &'static str,
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
}

/// Look up a constant by (canonical) name id.
pub fn const_info(env: &Env, name: NameId) -> Option<ConstInfo> {
    let d = &env.decls[*env.decl_of_name.get(&name)?];
    let mk = |kind, lps: &Vec<NameId>, ty| Some(ConstInfo { name, kind, level_params: lps.clone(), ty });
    match d {
        Decl::Axiom(x) => mk(d.kind(), &x.level_params, x.r#type),
        Decl::Def(x) => mk(d.kind(), &x.level_params, x.r#type),
        Decl::Thm(x) => mk(d.kind(), &x.level_params, x.r#type),
        Decl::Opaque(x) => mk(d.kind(), &x.level_params, x.r#type),
        Decl::Quot(x) => mk(d.kind(), &x.level_params, x.r#type),
        Decl::Inductive(b) => {
            if let Some(t) = b.types.iter().find(|t| t.name == name) {
                return mk("inductive", &t.level_params, t.r#type);
            }
            if let Some(c) = b.ctors.iter().find(|c| c.name == name) {
                return mk("ctor", &c.level_params, c.r#type);
            }
            let r = b.recs.iter().find(|r| r.name == name)?;
            mk("rec", &r.level_params, r.r#type)
        }
    }
}

/// Look up a constant by its printed name, e.g. `Nat.add_comm`.
pub fn find_const(env: &Env, printed: &str) -> Option<ConstInfo> {
    let idx = env.find_decl(printed)?;
    let name = env.decls[idx].defined_names().into_iter().find(|&n| env.name_str(n) == printed)?;
    const_info(env, name)
}

/// The statement of a constant: its type.
pub fn statement(env: &Env, c: &ConstInfo, opts: Options) -> String {
    expr_to_string(env, c.ty, opts)
}
