//! Content hashes for names, levels, expressions and declarations.
//!
//! The encoding is specified in `docs/spec/certificate-v0.md` (faithful mode)
//! and `docs/spec/certificate-v1.md` (alpha-normal mode). In short:
//! `key = BLAKE3-derive_key(CONTEXT, "")`, and every node hash is
//! `BLAKE3-keyed(key, tag || fields)`, where child nodes appear as their
//! 32-byte hashes, integers as 8-byte little-endian, booleans as one byte,
//! and strings and lists are prefixed with their length as an integer.
//!
//! v0 hashes the export *faithfully*: binder names and binder info are
//! included, so alpha-equivalent terms get different hashes.
//!
//! v1 (draft) adds an *alpha-normal* mode with its own key: lambda, pi and
//! let nodes omit the binder name and binder info (for let, the `nondep`
//! flag), so alpha-equivalent terms share a hash. Everything else is encoded
//! exactly as in v0.

use crate::export::*;

pub type Hash = [u8; 32];

/// Derive-key context for the faithful (v0) hash.
pub const CONTEXT: &str = "certus certificate v0 2026-11-20 node hash";

/// Derive-key context for the alpha-normal (v1 draft) hash.
pub const CONTEXT_ALPHA: &str = "certus certificate v1-alpha 2026-11-21 alpha-normal node hash";

/// Which content hash to compute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Spec v0: binder names and binder info are hashed.
    Faithful,
    /// Spec v1 (draft): binder names and binder info are omitted, so
    /// alpha-equivalent terms share a hash.
    AlphaNormal,
}

impl Mode {
    pub fn context(self) -> &'static str {
        match self {
            Mode::Faithful => CONTEXT,
            Mode::AlphaNormal => CONTEXT_ALPHA,
        }
    }
}

pub mod tag {
    pub const NAME_ANON: u8 = 0x00;
    pub const NAME_STR: u8 = 0x01;
    pub const NAME_NUM: u8 = 0x02;
    pub const LEVEL_ZERO: u8 = 0x10;
    pub const LEVEL_SUCC: u8 = 0x11;
    pub const LEVEL_MAX: u8 = 0x12;
    pub const LEVEL_IMAX: u8 = 0x13;
    pub const LEVEL_PARAM: u8 = 0x14;
    pub const EXPR_BVAR: u8 = 0x20;
    pub const EXPR_SORT: u8 = 0x21;
    pub const EXPR_CONST: u8 = 0x22;
    pub const EXPR_APP: u8 = 0x23;
    pub const EXPR_LAM: u8 = 0x24;
    pub const EXPR_PI: u8 = 0x25;
    pub const EXPR_LET: u8 = 0x26;
    pub const EXPR_NAT: u8 = 0x27;
    pub const EXPR_STR: u8 = 0x28;
    pub const EXPR_PROJ: u8 = 0x29;
    pub const DECL_AXIOM: u8 = 0x30;
    pub const DECL_DEF: u8 = 0x31;
    pub const DECL_THM: u8 = 0x32;
    pub const DECL_OPAQUE: u8 = 0x33;
    pub const DECL_QUOT: u8 = 0x34;
    pub const DECL_INDUCTIVE: u8 = 0x35;
    pub const ENV_ROOT: u8 = 0x40;
}

pub struct Hashes {
    pub names: Vec<Hash>,
    pub levels: Vec<Hash>,
    pub exprs: Vec<Hash>,
    pub decls: Vec<Hash>,
    /// Hash over all declaration hashes, in file order.
    pub root: Hash,
}

/// The faithful (v0) key.
pub fn key() -> [u8; 32] {
    key_for(Mode::Faithful)
}

pub fn key_for(mode: Mode) -> [u8; 32] {
    blake3::derive_key(mode.context(), &[])
}

struct Enc(blake3::Hasher);

impl Enc {
    fn new(key: &[u8; 32], tag: u8) -> Self {
        let mut h = blake3::Hasher::new_keyed(key);
        h.update(&[tag]);
        Enc(h)
    }
    fn u64(&mut self, v: u64) -> &mut Self {
        self.0.update(&v.to_le_bytes());
        self
    }
    fn bool(&mut self, b: bool) -> &mut Self {
        self.0.update(&[b as u8]);
        self
    }
    fn bytes(&mut self, b: &[u8]) -> &mut Self {
        self.u64(b.len() as u64);
        self.0.update(b);
        self
    }
    fn h(&mut self, x: &Hash) -> &mut Self {
        self.0.update(x);
        self
    }
    fn list(&mut self, hs: &[Hash], ids: &[u32]) -> &mut Self {
        self.u64(ids.len() as u64);
        for &i in ids {
            self.0.update(&hs[i as usize]);
        }
        self
    }
    fn done(&self) -> Hash {
        *self.0.finalize().as_bytes()
    }
}

fn binder_byte(bi: BinderInfo) -> u64 {
    match bi {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

/// Lambda or pi node. In alpha-normal mode the binder name and info are omitted.
fn binder(k: &[u8; 32], tag: u8, faithful: bool, name: &Hash, bi: BinderInfo, ty: Hash, body: Hash) -> Hash {
    let mut enc = Enc::new(k, tag);
    if faithful {
        enc.h(name).u64(binder_byte(bi));
    }
    enc.h(&ty).h(&body).done()
}

/// Faithful (spec v0) hashes.
pub fn hash_env(env: &Env) -> Hashes {
    hash_env_with(env, Mode::Faithful)
}

/// Alpha-normal (spec v1 draft) hashes.
pub fn hash_env_alpha(env: &Env) -> Hashes {
    hash_env_with(env, Mode::AlphaNormal)
}

pub fn hash_env_with(env: &Env, mode: Mode) -> Hashes {
    use tag::*;
    let k = key_for(mode);
    let faithful = mode == Mode::Faithful;

    let mut names: Vec<Hash> = Vec::with_capacity(env.names.len());
    for n in &env.names {
        let h = match n {
            Name::Anon => Enc::new(&k, NAME_ANON).done(),
            Name::Str { pre, s } => Enc::new(&k, NAME_STR).h(&names[*pre as usize]).bytes(s.as_bytes()).done(),
            Name::Num { pre, n } => Enc::new(&k, NAME_NUM).h(&names[*pre as usize]).u64(*n).done(),
        };
        names.push(h);
    }

    let mut levels: Vec<Hash> = Vec::with_capacity(env.levels.len());
    for l in &env.levels {
        let h = match *l {
            Level::Zero => Enc::new(&k, LEVEL_ZERO).done(),
            Level::Succ(a) => Enc::new(&k, LEVEL_SUCC).h(&levels[a as usize]).done(),
            Level::Max(a, b) => Enc::new(&k, LEVEL_MAX).h(&levels[a as usize]).h(&levels[b as usize]).done(),
            Level::IMax(a, b) => Enc::new(&k, LEVEL_IMAX).h(&levels[a as usize]).h(&levels[b as usize]).done(),
            Level::Param(n) => Enc::new(&k, LEVEL_PARAM).h(&names[n as usize]).done(),
        };
        levels.push(h);
    }

    let mut exprs: Vec<Hash> = Vec::with_capacity(env.exprs.len());
    for e in &env.exprs {
        let x = |i: ExprId| exprs[i as usize];
        let h = match e {
            Expr::BVar(i) => Enc::new(&k, EXPR_BVAR).u64(*i).done(),
            Expr::Sort(l) => Enc::new(&k, EXPR_SORT).h(&levels[*l as usize]).done(),
            Expr::Const { name, levels: ls } => {
                Enc::new(&k, EXPR_CONST).h(&names[*name as usize]).list(&levels, ls).done()
            }
            Expr::App { f, a } => Enc::new(&k, EXPR_APP).h(&x(*f)).h(&x(*a)).done(),
            Expr::Lam { name, ty, body, bi } => {
                binder(&k, EXPR_LAM, faithful, &names[*name as usize], *bi, x(*ty), x(*body))
            }
            Expr::Pi { name, ty, body, bi } => {
                binder(&k, EXPR_PI, faithful, &names[*name as usize], *bi, x(*ty), x(*body))
            }
            Expr::Let { name, ty, val, body, nondep } => {
                let mut enc = Enc::new(&k, EXPR_LET);
                if faithful {
                    enc.h(&names[*name as usize]).bool(*nondep);
                }
                enc.h(&x(*ty)).h(&x(*val)).h(&x(*body)).done()
            }
            Expr::NatLit(s) => Enc::new(&k, EXPR_NAT).bytes(s.as_bytes()).done(),
            Expr::StrLit(s) => Enc::new(&k, EXPR_STR).bytes(s.as_bytes()).done(),
            Expr::Proj { type_name, idx, structure } => {
                Enc::new(&k, EXPR_PROJ).h(&names[*type_name as usize]).u64(*idx).h(&x(*structure)).done()
            }
        };
        exprs.push(h);
    }

    let decls: Vec<Hash> = env.decls.iter().map(|d| hash_decl(&k, d, &names, &exprs)).collect();

    let mut root = Enc::new(&k, ENV_ROOT);
    root.u64(decls.len() as u64);
    for d in &decls {
        root.h(d);
    }
    let root = root.done();

    Hashes { names, levels, exprs, decls, root }
}

fn hash_decl(k: &[u8; 32], d: &Decl, n: &[Hash], e: &[Hash]) -> Hash {
    use tag::*;
    let ex = |i: ExprId| &e[i as usize];
    let nm = |i: NameId| &n[i as usize];
    match d {
        Decl::Axiom(a) => {
            Enc::new(k, DECL_AXIOM).h(nm(a.name)).list(n, &a.level_params).h(ex(a.r#type)).bool(a.is_unsafe).done()
        }
        Decl::Def(a) => {
            // serde_json maps keep keys sorted, so this string is canonical.
            let hints = serde_json::to_string(&a.hints).expect("JSON value serialises");
            Enc::new(k, DECL_DEF)
                .h(nm(a.name))
                .list(n, &a.level_params)
                .h(ex(a.r#type))
                .h(ex(a.value))
                .bytes(hints.as_bytes())
                .bytes(a.safety.as_bytes())
                .list(n, &a.all)
                .done()
        }
        Decl::Thm(a) => Enc::new(k, DECL_THM)
            .h(nm(a.name))
            .list(n, &a.level_params)
            .h(ex(a.r#type))
            .h(ex(a.value))
            .list(n, &a.all)
            .done(),
        Decl::Opaque(a) => Enc::new(k, DECL_OPAQUE)
            .h(nm(a.name))
            .list(n, &a.level_params)
            .h(ex(a.r#type))
            .h(ex(a.value))
            .bool(a.is_unsafe)
            .list(n, &a.all)
            .done(),
        Decl::Quot(a) => Enc::new(k, DECL_QUOT)
            .h(nm(a.name))
            .list(n, &a.level_params)
            .h(ex(a.r#type))
            .bytes(a.kind.as_bytes())
            .done(),
        Decl::Inductive(b) => {
            let mut x = Enc::new(k, DECL_INDUCTIVE);
            x.u64(b.types.len() as u64);
            for t in &b.types {
                x.h(nm(t.name))
                    .list(n, &t.level_params)
                    .h(ex(t.r#type))
                    .u64(t.num_params)
                    .u64(t.num_indices)
                    .list(n, &t.all)
                    .list(n, &t.ctors)
                    .u64(t.num_nested)
                    .bool(t.is_rec)
                    .bool(t.is_unsafe)
                    .bool(t.is_reflexive);
            }
            x.u64(b.ctors.len() as u64);
            for c in &b.ctors {
                x.h(nm(c.name))
                    .list(n, &c.level_params)
                    .h(ex(c.r#type))
                    .h(nm(c.induct))
                    .u64(c.cidx)
                    .u64(c.num_params)
                    .u64(c.num_fields)
                    .bool(c.is_unsafe);
            }
            x.u64(b.recs.len() as u64);
            for r in &b.recs {
                x.h(nm(r.name))
                    .list(n, &r.level_params)
                    .h(ex(r.r#type))
                    .list(n, &r.all)
                    .u64(r.num_params)
                    .u64(r.num_indices)
                    .u64(r.num_motives)
                    .u64(r.num_minors)
                    .u64(r.rules.len() as u64);
                for rule in &r.rules {
                    x.h(nm(rule.ctor)).u64(rule.nfields).h(ex(rule.rhs));
                }
                x.bool(r.k).bool(r.is_unsafe);
            }
            x.done()
        }
    }
}

pub fn hex(h: &Hash) -> String {
    h.iter().map(|b| format!("{b:02x}")).collect()
}
