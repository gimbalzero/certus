//! Type inference, reduction and definitional equality.
//!
//! This follows the design of Lean 4's C++ kernel (and of nanoda and
//! Lean4Lean): weak-head normalisation with beta, zeta, delta, iota and
//! projection reduction; lazy delta reduction guided by definitional heights;
//! proof irrelevance; eta for functions and structures; unit-like types; and
//! GMP-style acceleration of `Nat` operations on literals.

use crate::env::{ConstInfo, Hints, KEnv, Kind, NatOp, QuotKind};
use crate::term::{E, L, Level, Node, Store};
use certus_core::export::NameId;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

pub type R<T> = Result<T, KError>;

/// Why checking stopped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KError {
    /// The input is not a valid proof: it is ill-typed or malformed.
    Invalid(String),
    /// Checking ran out of a resource (work budget or stack) before reaching a
    /// verdict. Nothing is accepted, but nothing is shown to be wrong either.
    Resource(String),
}

impl KError {
    pub fn msg(&self) -> &str {
        match self {
            KError::Invalid(m) | KError::Resource(m) => m,
        }
    }

    pub fn is_resource(&self) -> bool {
        matches!(self, KError::Resource(_))
    }
}

impl std::fmt::Display for KError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.msg())
    }
}

impl From<&str> for KError {
    fn from(m: &str) -> Self {
        KError::Invalid(m.to_string())
    }
}

impl From<String> for KError {
    fn from(m: String) -> Self {
        KError::Invalid(m)
    }
}

/// Default work budget per declaration. Exceeding it is an error, so a
/// hostile proof can make Certus give up, but never make it accept.
pub const DEFAULT_FUEL: u64 = 200_000_000;

/// Stack size of the thread that `check` runs the kernel on. Only the pages
/// actually used are committed, so this is an upper bound, not a cost.
pub const STACK_SIZE: usize = 1 << 30;

/// Stack kept free below the guard for recursion that does not pass through a
/// guarded function (term traversals in `Store`, level normalisation).
const STACK_RESERVE: usize = 64 << 20;

/// Stack budget assumed when `TC` runs on a thread whose stack base was not
/// recorded by `set_stack_base` (any thread has at least this much).
const UNKNOWN_STACK_BUDGET: usize = 512 << 10;

thread_local! {
    /// Lowest stack address the kernel may recurse to on this thread (0: unset).
    static STACK_LIMIT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The current stack position (stacks grow downwards on every supported target).
#[inline(always)]
fn stack_pos() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
}

/// Record that the current thread was started with `STACK_SIZE` bytes of stack.
pub(crate) fn set_stack_base() {
    let limit = stack_pos().saturating_sub(STACK_SIZE - STACK_RESERVE);
    STACK_LIMIT.with(|l| l.set(limit));
}

pub struct TC<'a> {
    pub st: &'a mut Store,
    pub env: &'a KEnv,
    /// Constants added temporarily while checking an inductive block.
    pub local: FxHashMap<NameId, Arc<ConstInfo>>,
    /// Universe parameters of the declaration being checked.
    pub lparams: Vec<NameId>,
    /// Free variables: type and optional let-value.
    pub lctx: Vec<(E, Option<E>)>,
    infer_cache: FxHashMap<E, E>,
    check_cache: FxHashMap<E, E>,
    whnf_core_cache: FxHashMap<E, E>,
    whnf_cache: FxHashMap<E, E>,
    /// Recursion past this stack address is refused as a resource error.
    stack_limit: usize,
    eq_cache: FxHashSet<(E, E)>,
    neq_cache: FxHashSet<(E, E)>,
    fuel: u64,
}

impl<'a> TC<'a> {
    pub fn new(st: &'a mut Store, env: &'a KEnv, lparams: Vec<NameId>) -> Self {
        TC {
            st,
            env,
            local: FxHashMap::default(),
            lparams,
            lctx: Vec::new(),
            infer_cache: FxHashMap::default(),
            check_cache: FxHashMap::default(),
            whnf_core_cache: FxHashMap::default(),
            whnf_cache: FxHashMap::default(),
            stack_limit: match STACK_LIMIT.with(|l| l.get()) {
                0 => stack_pos().saturating_sub(UNKNOWN_STACK_BUDGET),
                l => l,
            },
            eq_cache: FxHashSet::default(),
            neq_cache: FxHashSet::default(),
            fuel: DEFAULT_FUEL,
        }
    }

    pub fn get_const(&self, n: NameId) -> Option<Arc<ConstInfo>> {
        self.local.get(&n).cloned().or_else(|| self.env.get(n))
    }

    /// One unit of work. Every recursive step of inference, reduction and
    /// definitional equality goes through here, so this also guards the stack:
    /// recursion that gets too deep is a resource error, never an overflow.
    fn burn(&mut self) -> R<()> {
        if stack_pos() < self.stack_limit {
            return Err(KError::Resource(
                "out of stack (term or definitional-equality check nested too deeply)".into(),
            ));
        }
        if self.fuel == 0 {
            return Err(KError::Resource(
                "work budget exhausted (proof too expensive to check, or non-terminating)".into(),
            ));
        }
        self.fuel -= 1;
        Ok(())
    }

    /// Strip `optParam T d`, `autoParam T t`, `outParam T` and `semiOutParam T` down to `T`,
    /// as Lean's kernel does when it introduces binders of inductive types.
    pub fn consume_annotations(&self, mut e: E) -> E {
        let b = &self.env.builtins;
        loop {
            let (h, args) = self.st.spine(e);
            let Node::Const(n, _) = self.st.node(h) else { return e };
            let n = Some(n);
            if ((n == b.opt_param || n == b.auto_param) && args.len() == 2)
                || ((n == b.out_param || n == b.semi_out_param) && args.len() == 1)
            {
                e = args[0];
            } else {
                return e;
            }
        }
    }

    pub fn fresh_fvar(&mut self, ty: E, val: Option<E>) -> E {
        let id = self.lctx.len() as u32;
        self.lctx.push((ty, val));
        self.st.mk(Node::FVar(id))
    }

    fn fvar_id(&self, e: E) -> u32 {
        match self.st.node(e) {
            Node::FVar(i) => i,
            _ => unreachable!("not a free variable"),
        }
    }

    /// Build `Π/λ (fvars), body` by abstracting the free variables.
    pub fn bind(&mut self, pi: bool, fvars: &[E], body: E) -> E {
        let ids: Vec<u32> = fvars.iter().map(|&f| self.fvar_id(f)).collect();
        let mut r = self.st.abstract_fvars(body, &ids);
        for k in (0..ids.len()).rev() {
            let ty = self.lctx[ids[k] as usize].0;
            let d = self.st.abstract_fvars(ty, &ids[..k]);
            r = self.st.mk(if pi { Node::Pi(d, r) } else { Node::Lam(d, r) });
        }
        r
    }

    // ------------------------------------------------------------------
    // Type inference
    // ------------------------------------------------------------------

    /// Infer the type of `e`. With `check`, also verify that `e` is well typed.
    pub fn infer(&mut self, e: E, check: bool) -> R<E> {
        if let Some(&t) = self.check_cache.get(&e) {
            return Ok(t);
        }
        if !check && let Some(&t) = self.infer_cache.get(&e) {
            return Ok(t);
        }
        self.burn()?;
        let t = match self.st.node(e) {
            Node::BVar(_) => return Err("unexpected loose bound variable".into()),
            Node::FVar(i) => self.lctx[i as usize].0,
            Node::Sort(l) => {
                self.check_level(l)?;
                let s = self.st.succ(l);
                self.st.sort(s)
            }
            Node::Const(n, ls) => {
                let c = self.get_const(n).ok_or_else(|| format!("unknown constant (name id {n})"))?;
                let ls: Vec<L> = self.st.list_of(ls).to_vec();
                if ls.len() != c.lparams.len() {
                    return Err("wrong number of universe arguments".into());
                }
                for &l in &ls {
                    self.check_level(l)?;
                }
                self.st.instantiate_lparams(c.ty, &c.lparams, &ls)
            }
            Node::App(..) => self.infer_app(e, check)?,
            Node::Lam(..) => self.infer_lambda(e, check)?,
            Node::Pi(..) => self.infer_pi(e, check)?,
            Node::Let(t, v, b) => {
                if check {
                    let s = self.infer(t, true)?;
                    self.ensure_sort(s)?;
                    let vt = self.infer(v, true)?;
                    if !self.is_def_eq(vt, t)? {
                        return Err("let value does not match its declared type".into());
                    }
                }
                let body = self.st.instantiate_rev(b, &[v]);
                self.infer(body, check)?
            }
            Node::Nat(_) => {
                let n = self.env.builtins.nat.ok_or("natural-number literal, but no Nat in the environment")?;
                self.get_const(n).ok_or("natural-number literal before Nat is declared")?;
                self.st.cnst(n, &[])
            }
            Node::Str(_) => {
                let n = self.env.builtins.string.ok_or("string literal, but no String in the environment")?;
                self.get_const(n).ok_or("string literal before String is declared")?;
                self.st.cnst(n, &[])
            }
            Node::Proj(s, i, x) => self.infer_proj(s, i, x, check)?,
        };
        if check {
            self.check_cache.insert(e, t);
        }
        self.infer_cache.insert(e, t);
        Ok(t)
    }

    fn check_level(&self, l: L) -> R<()> {
        let mut ps = Vec::new();
        self.st.level_params(l, &mut ps);
        match ps.iter().find(|p| !self.lparams.contains(p)) {
            Some(p) => Err(format!("undeclared universe parameter (name id {p})").into()),
            None => Ok(()),
        }
    }

    fn infer_app(&mut self, e: E, check: bool) -> R<E> {
        let (f, args) = self.st.spine(e);
        let mut ft = self.infer(f, check)?;
        let mut j = 0;
        for i in 0..args.len() {
            loop {
                if let Node::Pi(dom, body) = self.st.node(ft) {
                    if check {
                        let dom = self.st.instantiate_rev(dom, &args[j..i]);
                        let at = self.infer(args[i], true)?;
                        if !self.is_def_eq(at, dom)? {
                            return Err("application type mismatch".into());
                        }
                    }
                    ft = body;
                    break;
                }
                let t = self.st.instantiate_rev(ft, &args[j..i]);
                let t = self.whnf(t)?;
                if !matches!(self.st.node(t), Node::Pi(..)) {
                    return Err("function expected".into());
                }
                ft = t;
                j = i;
            }
        }
        Ok(self.st.instantiate_rev(ft, &args[j..]))
    }

    fn infer_lambda(&mut self, e: E, check: bool) -> R<E> {
        let mut fvars = Vec::new();
        let mut cur = e;
        while let Node::Lam(d, b) = self.st.node(cur) {
            let d = self.st.instantiate_rev(d, &fvars);
            if check {
                let s = self.infer(d, true)?;
                self.ensure_sort(s)?;
            }
            fvars.push(self.fresh_fvar(d, None));
            cur = b;
        }
        let body = self.st.instantiate_rev(cur, &fvars);
        let bt = self.infer(body, check)?;
        Ok(self.bind(true, &fvars, bt))
    }

    fn infer_pi(&mut self, e: E, check: bool) -> R<E> {
        let mut fvars = Vec::new();
        let mut levels = Vec::new();
        let mut cur = e;
        while let Node::Pi(d, b) = self.st.node(cur) {
            let d = self.st.instantiate_rev(d, &fvars);
            let s = self.infer(d, check)?;
            levels.push(self.ensure_sort(s)?);
            fvars.push(self.fresh_fvar(d, None));
            cur = b;
        }
        let body = self.st.instantiate_rev(cur, &fvars);
        let s = self.infer(body, check)?;
        let mut r = self.ensure_sort(s)?;
        for &l in levels.iter().rev() {
            r = self.st.imax(l, r);
        }
        Ok(self.st.sort(r))
    }

    fn infer_proj(&mut self, sname: NameId, idx: u32, x: E, check: bool) -> R<E> {
        let xt = self.infer(x, check)?;
        let xt = self.whnf(xt)?;
        let (h, args) = self.st.spine(xt);
        let Node::Const(iname, ls) = self.st.node(h) else {
            return Err("projection of a value whose type is not an inductive".into());
        };
        if iname != sname {
            return Err("projection names the wrong structure".into());
        }
        let ind = self.get_const(iname).ok_or("projection of an unknown type")?;
        let Kind::Induct { num_params, num_indices, ctors, .. } = &ind.kind else {
            return Err("projection of a non-inductive type".into());
        };
        if ctors.len() != 1 || *num_indices != 0 || args.len() != *num_params as usize {
            return Err("projection of a type that is not a structure".into());
        }
        let ctor = self.get_const(ctors[0]).ok_or("structure constructor missing")?;
        let ls: Vec<L> = self.st.list_of(ls).to_vec();
        let mut r = self.st.instantiate_lparams(ctor.ty, &ctor.lparams, &ls);
        for &a in &args {
            r = self.whnf(r)?;
            let Node::Pi(_, b) = self.st.node(r) else { return Err("malformed structure constructor".into()) };
            r = self.st.instantiate_rev(b, &[a]);
        }
        let is_prop_struct = self.is_proof_type(xt)?;
        for i in 0..idx {
            r = self.whnf(r)?;
            let Node::Pi(d, b) = self.st.node(r) else { return Err("projection index out of range".into()) };
            if self.st.info(b).lbr > 0 {
                if is_prop_struct && !self.is_proof_type(d)? {
                    return Err("cannot project data out of a proof".into());
                }
                let p = self.st.mk(Node::Proj(sname, i, x));
                r = self.st.instantiate_rev(b, &[p]);
            } else {
                r = b;
            }
        }
        r = self.whnf(r)?;
        let Node::Pi(d, _) = self.st.node(r) else { return Err("projection index out of range".into()) };
        if is_prop_struct && !self.is_proof_type(d)? {
            return Err("cannot project data out of a proof".into());
        }
        Ok(d)
    }

    pub fn ensure_sort(&mut self, t: E) -> R<L> {
        if let Node::Sort(l) = self.st.node(t) {
            return Ok(l);
        }
        let t = self.whnf(t)?;
        match self.st.node(t) {
            Node::Sort(l) => Ok(l),
            _ => Err("type expected".into()),
        }
    }

    /// The universe level of a type `t` (so `t : Sort l`).
    pub fn sort_of(&mut self, t: E) -> R<L> {
        let s = self.infer(t, false)?;
        self.ensure_sort(s)
    }

    /// Is `t` a proposition, i.e. `t : Prop`?
    pub fn is_proof_type(&mut self, t: E) -> R<bool> {
        let s = self.infer(t, false)?;
        let s = self.whnf(s)?;
        Ok(match self.st.node(s) {
            Node::Sort(l) => self.st.is_zero(l),
            _ => false,
        })
    }

    // ------------------------------------------------------------------
    // Reduction
    // ------------------------------------------------------------------

    /// Weak-head normal form without unfolding definitions.
    pub fn whnf_core(&mut self, e: E) -> R<E> {
        match self.st.node(e) {
            Node::BVar(_) | Node::Sort(_) | Node::Pi(..) | Node::Lam(..) | Node::Nat(_) | Node::Str(_) => {
                return Ok(e);
            }
            Node::Const(..) => return Ok(e),
            Node::FVar(i) => {
                return match self.lctx[i as usize].1 {
                    Some(v) => self.whnf_core(v),
                    None => Ok(e),
                };
            }
            _ => {}
        }
        if let Some(&r) = self.whnf_core_cache.get(&e) {
            return Ok(r);
        }
        self.burn()?;
        let r = match self.st.node(e) {
            Node::Let(_, v, b) => {
                let x = self.st.instantiate_rev(b, &[v]);
                self.whnf_core(x)?
            }
            Node::App(..) => {
                let (f, args) = self.st.spine(e);
                let f2 = self.whnf_core(f)?;
                if let Node::Lam(..) = self.st.node(f2) {
                    let mut m = 0;
                    let mut cur = f2;
                    while m < args.len() {
                        match self.st.node(cur) {
                            Node::Lam(_, b) => {
                                cur = b;
                                m += 1;
                            }
                            _ => break,
                        }
                    }
                    let body = self.st.instantiate_rev(cur, &args[..m]);
                    let r = self.st.apps(body, &args[m..]);
                    self.whnf_core(r)?
                } else if f2 == f {
                    match self.reduce_rec(e)? {
                        Some(r) => self.whnf_core(r)?,
                        None => e,
                    }
                } else {
                    let r = self.st.apps(f2, &args);
                    self.whnf_core(r)?
                }
            }
            Node::Proj(_, idx, s) => match self.reduce_proj(idx, s)? {
                Some(r) => self.whnf_core(r)?,
                None => e,
            },
            _ => unreachable!(),
        };
        self.whnf_core_cache.insert(e, r);
        Ok(r)
    }

    /// Full weak-head normal form.
    pub fn whnf(&mut self, e: E) -> R<E> {
        match self.st.node(e) {
            Node::BVar(_) | Node::Sort(_) | Node::Pi(..) | Node::Lam(..) | Node::Nat(_) | Node::Str(_) => {
                return Ok(e);
            }
            _ => {}
        }
        if let Some(&r) = self.whnf_cache.get(&e) {
            return Ok(r);
        }
        let mut t = e;
        loop {
            self.burn()?;
            let t1 = self.whnf_core(t)?;
            if let Some(v) = self.reduce_nat(t1)? {
                t = v;
                break;
            }
            match self.unfold(t1) {
                Some(u) => t = u,
                None => {
                    t = t1;
                    break;
                }
            }
        }
        self.whnf_cache.insert(e, t);
        Ok(t)
    }

    /// Unfold the head constant if it is a definition or theorem.
    fn unfold(&mut self, e: E) -> Option<E> {
        let (f, args) = self.st.spine(e);
        let Node::Const(n, ls) = self.st.node(f) else { return None };
        let c = self.get_const(n)?;
        let val = match c.kind {
            Kind::Def { val, .. } | Kind::Thm { val } => val,
            _ => return None,
        };
        let ls: Vec<L> = self.st.list_of(ls).to_vec();
        if ls.len() != c.lparams.len() {
            return None;
        }
        let v = self.st.instantiate_lparams(val, &c.lparams, &ls);
        Some(self.st.apps(v, &args))
    }

    /// Definitional height of the head constant, if it can be unfolded.
    fn delta_rank(&self, e: E) -> Option<(NameId, u64)> {
        let Node::Const(n, _) = self.st.node(self.st.head(e)) else { return None };
        match self.get_const(n)?.kind {
            Kind::Def { hints, .. } => Some((
                n,
                match hints {
                    Hints::Abbrev => u64::MAX,
                    Hints::Regular(h) => h as u64 + 1,
                    Hints::Opaque => 0,
                },
            )),
            Kind::Thm { .. } => Some((n, 0)),
            _ => None,
        }
    }

    fn reduce_proj(&mut self, idx: u32, s: E) -> R<Option<E>> {
        let mut w = self.whnf(s)?;
        if let Node::Str(_) = self.st.node(w) {
            w = self.str_to_ctor(w)?;
        }
        let (h, args) = self.st.spine(w);
        let Node::Const(c, _) = self.st.node(h) else { return Ok(None) };
        match self.get_const(c).map(|c| c.kind.clone()) {
            Some(Kind::Ctor { num_params, .. }) => Ok(args.get((num_params + idx) as usize).copied()),
            _ => Ok(None),
        }
    }

    fn reduce_rec(&mut self, e: E) -> R<Option<E>> {
        let (f, args) = self.st.spine(e);
        let Node::Const(n, ls) = self.st.node(f) else { return Ok(None) };
        let Some(c) = self.get_const(n) else { return Ok(None) };
        match &c.kind {
            Kind::Rec { major_induct, num_params, num_indices, num_motives, num_minors, rules, k } => {
                let major_idx = (num_params + num_motives + num_minors + num_indices) as usize;
                if args.len() <= major_idx {
                    return Ok(None);
                }
                let mut major = args[major_idx];
                if *k && let Some(m) = self.ctor_when_k(*major_induct, major)? {
                    major = m;
                }
                major = self.whnf(major)?;
                match self.st.node(major) {
                    Node::Nat(_) => major = self.nat_lit_to_ctor(major)?,
                    Node::Str(_) => major = self.str_to_ctor(major)?,
                    _ => major = self.ctor_when_structure(*major_induct, major)?,
                }
                let (mh, margs) = self.st.spine(major);
                let Node::Const(cn, _) = self.st.node(mh) else { return Ok(None) };
                let Some(rule) = rules.iter().find(|r| r.ctor == cn) else { return Ok(None) };
                let nf = rule.nfields as usize;
                if margs.len() < nf {
                    return Ok(None);
                }
                let ls: Vec<L> = self.st.list_of(ls).to_vec();
                if ls.len() != c.lparams.len() {
                    return Ok(None);
                }
                let mut r = self.st.instantiate_lparams(rule.rhs, &c.lparams, &ls);
                r = self.st.apps(r, &args[..(num_params + num_motives + num_minors) as usize]);
                r = self.st.apps(r, &margs[margs.len() - nf..]);
                r = self.st.apps(r, &args[major_idx + 1..]);
                Ok(Some(r))
            }
            Kind::Quot(QuotKind::Lift) => self.reduce_quot(&args, 5, 3),
            Kind::Quot(QuotKind::Ind) => self.reduce_quot(&args, 4, 3),
            _ => Ok(None),
        }
    }

    fn reduce_quot(&mut self, args: &[E], mk_pos: usize, f_pos: usize) -> R<Option<E>> {
        if args.len() <= mk_pos {
            return Ok(None);
        }
        let mk = self.whnf(args[mk_pos])?;
        let (h, margs) = self.st.spine(mk);
        let Node::Const(n, _) = self.st.node(h) else { return Ok(None) };
        let is_mk = matches!(self.get_const(n).map(|c| c.kind.clone()), Some(Kind::Quot(QuotKind::Ctor)));
        if !is_mk || margs.len() != 3 {
            return Ok(None);
        }
        let r = self.st.app(args[f_pos], margs[2]);
        Ok(Some(self.st.apps(r, &args[mk_pos + 1..])))
    }

    fn structure_like(&self, i: NameId) -> Option<(NameId, u32, u32)> {
        let c = self.get_const(i)?;
        let Kind::Induct { ctors, num_indices: 0, is_rec: false, num_params, .. } = &c.kind else { return None };
        if ctors.len() != 1 {
            return None;
        }
        let ctor = self.get_const(ctors[0])?;
        let Kind::Ctor { num_fields, .. } = ctor.kind else { return None };
        Some((ctors[0], *num_params, num_fields))
    }

    fn ctor_when_k(&mut self, induct: NameId, major: E) -> R<Option<E>> {
        let t = self.infer(major, false)?;
        let t = self.whnf(t)?;
        let (h, targs) = self.st.spine(t);
        let Node::Const(i, ls) = self.st.node(h) else { return Ok(None) };
        if i != induct {
            return Ok(None);
        }
        let Some(c) = self.get_const(i) else { return Ok(None) };
        let Kind::Induct { num_params, num_indices, ctors, .. } = &c.kind else { return Ok(None) };
        if targs.len() != (num_params + num_indices) as usize || ctors.is_empty() {
            return Ok(None);
        }
        let ctor = self.st.mk(Node::Const(ctors[0], ls));
        let new = self.st.apps(ctor, &targs[..*num_params as usize]);
        let nt = self.infer(new, false)?;
        Ok(if self.is_def_eq(t, nt)? { Some(new) } else { None })
    }

    fn ctor_when_structure(&mut self, induct: NameId, e: E) -> R<E> {
        let Some((ctor, np, nf)) = self.structure_like(induct) else { return Ok(e) };
        if let Node::Const(n, _) = self.st.node(self.st.head(e))
            && matches!(self.get_const(n).map(|c| c.kind.clone()), Some(Kind::Ctor { .. }))
        {
            return Ok(e);
        }
        let t = self.infer(e, false)?;
        let t = self.whnf(t)?;
        let (h, targs) = self.st.spine(t);
        let Node::Const(i, ls) = self.st.node(h) else { return Ok(e) };
        if i != induct || targs.len() != np as usize || self.is_proof_type(t)? {
            return Ok(e);
        }
        let mut r = self.st.mk(Node::Const(ctor, ls));
        r = self.st.apps(r, &targs);
        for k in 0..nf {
            let p = self.st.mk(Node::Proj(induct, k, e));
            r = self.st.app(r, p);
        }
        Ok(r)
    }

    fn nat_lit_to_ctor(&mut self, e: E) -> R<E> {
        let Node::Nat(i) = self.st.node(e) else { return Ok(e) };
        let v = self.st.nat_val(i).clone();
        let b = &self.env.builtins;
        if v.is_zero() {
            let z = b.nat_zero.ok_or("Nat.zero missing")?;
            Ok(self.st.cnst(z, &[]))
        } else {
            let s = b.nat_succ.ok_or("Nat.succ missing")?;
            let s = self.st.cnst(s, &[]);
            let p = self.st.nat(v - 1u32);
            Ok(self.st.app(s, p))
        }
    }

    /// `"ab"` becomes `String.mk [Char.ofNat 97, Char.ofNat 98]`.
    fn str_to_ctor(&mut self, e: E) -> R<E> {
        let Node::Str(i) = self.st.node(e) else { return Ok(e) };
        let s: Vec<u32> = self.st.str_val(i).chars().map(|c| c as u32).collect();
        let b = self.env.builtins.clone();
        let miss = "string literal needs String.mk, Char.ofNat, List.nil and List.cons";
        let (smk, ch, ofnat, nil, cons) = (
            b.string_mk.ok_or(miss)?,
            b.char.ok_or(miss)?,
            b.char_of_nat.ok_or(miss)?,
            b.list_nil.ok_or(miss)?,
            b.list_cons.ok_or(miss)?,
        );
        let z = self.st.zero;
        let ch = self.st.cnst(ch, &[]);
        let ofnat = self.st.cnst(ofnat, &[]);
        let nil = self.st.cnst(nil, &[z]);
        let cons = self.st.cnst(cons, &[z]);
        let mut list = self.st.app(nil, ch);
        for &c in s.iter().rev() {
            let n = self.st.nat(BigUint::from(c));
            let c = self.st.app(ofnat, n);
            list = self.st.apps(cons, &[ch, c, list]);
        }
        let smk = self.st.cnst(smk, &[]);
        Ok(self.st.app(smk, list))
    }

    fn nat_lit_value(&mut self, e: E) -> R<Option<BigUint>> {
        let w = self.whnf(e)?;
        Ok(match self.st.node(w) {
            Node::Nat(i) => Some(self.st.nat_val(i).clone()),
            Node::Const(n, _) if Some(n) == self.env.builtins.nat_zero => Some(BigUint::zero()),
            _ => None,
        })
    }

    /// Accelerated `Nat` arithmetic on literals.
    fn reduce_nat(&mut self, e: E) -> R<Option<E>> {
        if self.st.info(e).has_fvar {
            return Ok(None);
        }
        let (f, args) = self.st.spine(e);
        let Node::Const(n, _) = self.st.node(f) else { return Ok(None) };
        if args.len() == 1 && Some(n) == self.env.builtins.nat_succ {
            return Ok(match self.nat_lit_value(args[0])? {
                Some(v) => Some(self.st.nat(v + 1u32)),
                None => None,
            });
        }
        let Some(&(_, op)) = self.env.builtins.nat_ops.iter().find(|(m, _)| *m == n) else { return Ok(None) };
        if op == NatOp::Log2 {
            if args.len() != 1 {
                return Ok(None);
            }
            let Some(a) = self.nat_lit_value(args[0])? else { return Ok(None) };
            let r = if a.is_zero() { BigUint::zero() } else { BigUint::from(a.bits() - 1) };
            return Ok(Some(self.st.nat(r)));
        }
        if args.len() != 2 {
            return Ok(None);
        }
        let Some(a) = self.nat_lit_value(args[0])? else { return Ok(None) };
        let Some(b) = self.nat_lit_value(args[1])? else { return Ok(None) };
        let small = |x: &BigUint| x.to_u64().filter(|&v| v <= 1 << 24);
        let r = match op {
            NatOp::Add => a + b,
            NatOp::Sub => {
                if a > b {
                    a - b
                } else {
                    BigUint::zero()
                }
            }
            NatOp::Mul => a * b,
            NatOp::Div => {
                if b.is_zero() {
                    BigUint::zero()
                } else {
                    a / b
                }
            }
            NatOp::Mod => {
                if b.is_zero() {
                    a
                } else {
                    a % b
                }
            }
            NatOp::Gcd => a.gcd(&b),
            NatOp::Land => a & b,
            NatOp::Lor => a | b,
            NatOp::Xor => a ^ b,
            NatOp::ShiftLeft => match small(&b) {
                Some(s) => a << s,
                None => return Ok(None),
            },
            NatOp::ShiftRight => match b.to_u64() {
                Some(s) => a >> s,
                None => BigUint::zero(),
            },
            NatOp::Pow => match small(&b) {
                Some(s) => num_traits::pow(a, s as usize),
                None => return Ok(None),
            },
            NatOp::Beq | NatOp::Ble => {
                let truth = if op == NatOp::Beq { a == b } else { a <= b };
                let bl = &self.env.builtins;
                let name = if truth { bl.bool_true } else { bl.bool_false };
                let name = name.ok_or("Bool.true/Bool.false missing")?;
                return Ok(Some(self.st.cnst(name, &[])));
            }
            NatOp::Log2 => unreachable!(),
        };
        let _ = BigUint::one();
        Ok(Some(self.st.nat(r)))
    }

    // ------------------------------------------------------------------
    // Definitional equality
    // ------------------------------------------------------------------

    pub fn is_def_eq(&mut self, a: E, b: E) -> R<bool> {
        if a == b {
            return Ok(true);
        }
        let key = if a < b { (a, b) } else { (b, a) };
        if self.eq_cache.contains(&key) {
            return Ok(true);
        }
        if self.neq_cache.contains(&key) {
            return Ok(false);
        }
        let r = self.is_def_eq_core(a, b)?;
        if r {
            self.eq_cache.insert(key);
        } else {
            self.neq_cache.insert(key);
        }
        Ok(r)
    }

    fn quick_def_eq(&mut self, a: E, b: E) -> R<Option<bool>> {
        if a == b {
            return Ok(Some(true));
        }
        Ok(match (self.st.node(a), self.st.node(b)) {
            (Node::Lam(..), Node::Lam(..)) | (Node::Pi(..), Node::Pi(..)) => Some(self.def_eq_binding(a, b)?),
            (Node::Sort(x), Node::Sort(y)) => Some(self.st.level_eq(x, y)),
            (Node::Nat(_), Node::Nat(_)) | (Node::Str(_), Node::Str(_)) => Some(false),
            _ => None,
        })
    }

    fn def_eq_binding(&mut self, a: E, b: E) -> R<bool> {
        let mut fvars = Vec::new();
        let (mut x, mut y) = (a, b);
        while let (Node::Lam(d1, b1), Node::Lam(d2, b2)) | (Node::Pi(d1, b1), Node::Pi(d2, b2)) =
            (self.st.node(x), self.st.node(y))
        {
            let d1 = self.st.instantiate_rev(d1, &fvars);
            let d2 = self.st.instantiate_rev(d2, &fvars);
            if !self.is_def_eq(d1, d2)? {
                return Ok(false);
            }
            fvars.push(self.fresh_fvar(d1, None));
            x = b1;
            y = b2;
        }
        let x = self.st.instantiate_rev(x, &fvars);
        let y = self.st.instantiate_rev(y, &fvars);
        self.is_def_eq(x, y)
    }

    fn levels_eq(&mut self, a: crate::term::Ls, b: crate::term::Ls) -> bool {
        let (x, y) = (self.st.list_of(a).to_vec(), self.st.list_of(b).to_vec());
        x.len() == y.len() && x.iter().zip(&y).all(|(&p, &q)| self.st.level_eq(p, q))
    }

    fn is_def_eq_core(&mut self, a: E, b: E) -> R<bool> {
        self.burn()?;
        if let Some(r) = self.quick_def_eq(a, b)? {
            return Ok(r);
        }
        // Proof irrelevance: any two proofs of the same proposition are equal.
        let ta = self.infer(a, false)?;
        if self.is_proof_type(ta)? {
            let tb = self.infer(b, false)?;
            return self.is_def_eq(ta, tb);
        }
        let a1 = self.whnf_core(a)?;
        let b1 = self.whnf_core(b)?;
        if (a1 != a || b1 != b)
            && let Some(r) = self.quick_def_eq(a1, b1)?
        {
            return Ok(r);
        }
        let (t, s) = match self.lazy_delta(a1, b1)? {
            Lazy::Done(r) => return Ok(r),
            Lazy::Stuck(t, s) => (t, s),
        };
        match (self.st.node(t), self.st.node(s)) {
            (Node::Const(n1, l1), Node::Const(n2, l2)) if n1 == n2 && self.levels_eq(l1, l2) => return Ok(true),
            (Node::FVar(i), Node::FVar(j)) if i == j => return Ok(true),
            (Node::Proj(_, i1, s1), Node::Proj(_, i2, s2)) if i1 == i2 && self.is_def_eq(s1, s2)? => {
                return Ok(true);
            }
            _ => {}
        }
        if self.def_eq_app(t, s)? {
            return Ok(true);
        }
        if self.try_eta(t, s)? || self.try_eta(s, t)? {
            return Ok(true);
        }
        if self.try_eta_struct(t, s)? || self.try_eta_struct(s, t)? {
            return Ok(true);
        }
        if let Some(r) = self.lit_vs_ctor(t, s)? {
            return Ok(r);
        }
        if let Some(r) = self.lit_vs_ctor(s, t)? {
            return Ok(r);
        }
        self.def_eq_unit_like(t, s)
    }

    fn lazy_delta(&mut self, mut t: E, mut s: E) -> R<Lazy> {
        loop {
            self.burn()?;
            if let Some(t2) = self.reduce_nat(t)? {
                return Ok(Lazy::Done(self.is_def_eq(t2, s)?));
            }
            if let Some(s2) = self.reduce_nat(s)? {
                return Ok(Lazy::Done(self.is_def_eq(t, s2)?));
            }
            match (self.delta_rank(t), self.delta_rank(s)) {
                (None, None) => return Ok(Lazy::Stuck(t, s)),
                (Some(_), None) => t = self.unfold(t).expect("delta"),
                (None, Some(_)) => s = self.unfold(s).expect("delta"),
                (Some((n1, r1)), Some((n2, r2))) => {
                    if r1 > r2 {
                        t = self.unfold(t).expect("delta");
                    } else if r2 > r1 {
                        s = self.unfold(s).expect("delta");
                    } else {
                        if n1 == n2 && self.same_head_args_eq(t, s)? {
                            return Ok(Lazy::Done(true));
                        }
                        t = self.unfold(t).expect("delta");
                        s = self.unfold(s).expect("delta");
                    }
                }
            }
            t = self.whnf_core(t)?;
            s = self.whnf_core(s)?;
            if let Some(r) = self.quick_def_eq(t, s)? {
                return Ok(Lazy::Done(r));
            }
        }
    }

    /// `f.{ls} as =?= f.{ls'} bs` by comparing levels and arguments only.
    fn same_head_args_eq(&mut self, t: E, s: E) -> R<bool> {
        let (f, xs) = self.st.spine(t);
        let (g, ys) = self.st.spine(s);
        let (Node::Const(_, l1), Node::Const(_, l2)) = (self.st.node(f), self.st.node(g)) else { return Ok(false) };
        if xs.len() != ys.len() || !self.levels_eq(l1, l2) {
            return Ok(false);
        }
        for (x, y) in xs.into_iter().zip(ys) {
            if !self.is_def_eq(x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn def_eq_app(&mut self, t: E, s: E) -> R<bool> {
        if !matches!(self.st.node(t), Node::App(..)) || !matches!(self.st.node(s), Node::App(..)) {
            return Ok(false);
        }
        let (f, xs) = self.st.spine(t);
        let (g, ys) = self.st.spine(s);
        if xs.len() != ys.len() || !self.is_def_eq(f, g)? {
            return Ok(false);
        }
        for (x, y) in xs.into_iter().zip(ys) {
            if !self.is_def_eq(x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Eta for functions: `λx. f x =?= f`.
    fn try_eta(&mut self, t: E, s: E) -> R<bool> {
        if !matches!(self.st.node(t), Node::Lam(..)) || matches!(self.st.node(s), Node::Lam(..)) {
            return Ok(false);
        }
        let st = self.infer(s, false)?;
        let st = self.whnf(st)?;
        let Node::Pi(d, _) = self.st.node(st) else { return Ok(false) };
        let b0 = self.st.bvar(0);
        let body = self.st.app(s, b0);
        let lam = self.st.mk(Node::Lam(d, body));
        self.is_def_eq(t, lam)
    }

    /// Eta for structures: `⟨s.1, …, s.n⟩ =?= s`.
    fn try_eta_struct(&mut self, t: E, s: E) -> R<bool> {
        let (h, args) = self.st.spine(s);
        let Node::Const(c, _) = self.st.node(h) else { return Ok(false) };
        let Some(Kind::Ctor { induct, num_params, num_fields, .. }) = self.get_const(c).map(|c| c.kind.clone()) else {
            return Ok(false);
        };
        if args.len() != (num_params + num_fields) as usize || self.structure_like(induct).is_none() {
            return Ok(false);
        }
        let tt = self.infer(t, false)?;
        let ts = self.infer(s, false)?;
        if !self.is_def_eq(tt, ts)? {
            return Ok(false);
        }
        for i in 0..num_fields {
            let p = self.st.mk(Node::Proj(induct, i, t));
            if !self.is_def_eq(p, args[(num_params + i) as usize])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Any two values of a type with one constructor and no fields are equal.
    fn def_eq_unit_like(&mut self, t: E, s: E) -> R<bool> {
        let tt = self.infer(t, false)?;
        let tt = self.whnf(tt)?;
        let Node::Const(i, _) = self.st.node(self.st.head(tt)) else { return Ok(false) };
        match self.structure_like(i) {
            Some((_, _, 0)) => {
                let ts = self.infer(s, false)?;
                self.is_def_eq(tt, ts)
            }
            _ => Ok(false),
        }
    }

    /// A literal against a constructor form: `3 =?= Nat.succ x`, `"a" =?= String.mk l`.
    fn lit_vs_ctor(&mut self, t: E, s: E) -> R<Option<bool>> {
        let head = self.st.head(s);
        let head_name = match self.st.node(head) {
            Node::Const(n, _) => Some(n),
            _ => None,
        };
        let b = &self.env.builtins;
        match self.st.node(t) {
            Node::Nat(i) if head_name.is_some() && (head_name == b.nat_succ || head_name == b.nat_zero) => {
                // Compare structurally, one constructor at a time. (Rebuilding
                // `Nat.succ (n-1)` would just be folded back into `n`.)
                let v = self.st.nat_val(i).clone();
                let (_, args) = self.st.spine(s);
                if head_name == b.nat_zero {
                    return Ok(Some(v.is_zero() && args.is_empty()));
                }
                if v.is_zero() || args.len() != 1 {
                    return Ok(Some(false));
                }
                let pred = self.st.nat(v - 1u32);
                Ok(Some(self.is_def_eq(pred, args[0])?))
            }
            Node::Str(_) if head_name.is_some() && head_name == b.string_mk => {
                let c = self.str_to_ctor(t)?;
                Ok(Some(self.is_def_eq(c, s)?))
            }
            _ => Ok(None),
        }
    }
}

enum Lazy {
    Done(bool),
    Stuck(E, E),
}

/// Is `l` syntactically a universe parameter?
pub fn level_param(st: &Store, l: L) -> Option<NameId> {
    match st.lnode(l) {
        Level::Param(p) => Some(p),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `s (s (… (s x)))` with `n` applications.
    fn tower(tc: &mut TC, s: E, x: E, n: usize) -> E {
        (0..n).fold(x, |e, _| tc.st.app(s, e))
    }

    fn deep_def_eq(n: usize) -> R<bool> {
        let mut st = Store::new();
        let env = KEnv::default();
        let mut tc = TC::new(&mut st, &env, Vec::new());
        let prop = tc.st.sort(tc.st.zero);
        let p_to_p = tc.st.mk(Node::Pi(prop, prop));
        let s = tc.fresh_fvar(p_to_p, None);
        let x = tc.fresh_fvar(prop, None);
        let y = tc.fresh_fvar(prop, None);
        let a = tower(&mut tc, s, x, n);
        let b = tower(&mut tc, s, y, n);
        tc.is_def_eq(a, b)
    }

    #[test]
    fn deep_def_eq_is_a_resource_error_not_an_overflow() {
        // Off the `check` thread, `TC` assumes a small stack budget, so a deep
        // enough comparison must stop with a resource error, not overflow.
        let r =
            std::thread::Builder::new().stack_size(16 << 20).spawn(|| deep_def_eq(100_000)).unwrap().join().unwrap();
        match r {
            Err(e) => assert!(e.is_resource(), "expected a resource error, got: {e}"),
            Ok(v) => panic!("expected a resource error, got a verdict: {v}"),
        }
    }

    #[test]
    fn deep_def_eq_decides_on_the_checker_stack() {
        // The stack `check` runs on is deep enough for a long comparison.
        let r = std::thread::Builder::new()
            .stack_size(STACK_SIZE)
            .spawn(|| {
                set_stack_base();
                deep_def_eq(100_000)
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(r, Ok(false));
    }

    #[test]
    fn shallow_def_eq_still_decides() {
        assert_eq!(deep_def_eq(100), Ok(false));
    }
}
