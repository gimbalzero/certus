//! Hash-consed terms and universe levels.
//!
//! Every term is interned, so structurally equal terms share one id. Binder
//! names and binder info are dropped, since the kernel never looks at them.
//! As a result, alpha-equivalent terms have the *same* id, and the cheapest
//! definitional-equality check is a single integer comparison.

use certus_core::export::NameId;
use num_bigint::BigUint;
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct E(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct L(pub u32);

/// An interned list of levels (the universe arguments of a constant).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Ls(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Level {
    Zero,
    Succ(L),
    Max(L, L),
    IMax(L, L),
    Param(NameId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Node {
    BVar(u32),
    FVar(u32),
    Sort(L),
    Const(NameId, Ls),
    App(E, E),
    Lam(E, E),
    Pi(E, E),
    Let(E, E, E),
    Nat(u32),
    Str(u32),
    Proj(NameId, u32, E),
}

#[derive(Clone, Copy, Debug)]
pub struct Info {
    /// One more than the largest loose bound variable (0 = closed).
    pub lbr: u32,
    pub has_fvar: bool,
    pub has_lparam: bool,
}

pub struct Store {
    nodes: Vec<Node>,
    info: Vec<Info>,
    map: FxHashMap<Node, E>,
    levels: Vec<Level>,
    level_has_param: Vec<bool>,
    lmap: FxHashMap<Level, L>,
    lists: Vec<Box<[L]>>,
    list_map: FxHashMap<Box<[L]>, Ls>,
    nats: Vec<BigUint>,
    nat_map: FxHashMap<BigUint, u32>,
    strs: Vec<Box<str>>,
    str_map: FxHashMap<Box<str>, u32>,
    leq_cache: FxHashMap<(L, L), bool>,
    pub zero: L,
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

impl Store {
    pub fn new() -> Self {
        let mut s = Store {
            nodes: Vec::new(),
            info: Vec::new(),
            map: FxHashMap::default(),
            levels: Vec::new(),
            level_has_param: Vec::new(),
            lmap: FxHashMap::default(),
            lists: Vec::new(),
            list_map: FxHashMap::default(),
            nats: Vec::new(),
            nat_map: FxHashMap::default(),
            strs: Vec::new(),
            str_map: FxHashMap::default(),
            leq_cache: FxHashMap::default(),
            zero: L(0),
        };
        s.zero = s.level(Level::Zero);
        s
    }

    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    // ---------- levels ----------

    /// Intern a level exactly as given (no simplification).
    pub fn level(&mut self, l: Level) -> L {
        if let Some(&x) = self.lmap.get(&l) {
            return x;
        }
        let hp = match l {
            Level::Zero => false,
            Level::Param(_) => true,
            Level::Succ(a) => self.level_has_param[a.0 as usize],
            Level::Max(a, b) | Level::IMax(a, b) => {
                self.level_has_param[a.0 as usize] || self.level_has_param[b.0 as usize]
            }
        };
        let id = L(self.levels.len() as u32);
        self.levels.push(l);
        self.level_has_param.push(hp);
        self.lmap.insert(l, id);
        id
    }

    pub fn lnode(&self, l: L) -> Level {
        self.levels[l.0 as usize]
    }

    pub fn succ(&mut self, l: L) -> L {
        self.level(Level::Succ(l))
    }

    /// `max`, with semantics-preserving simplifications.
    pub fn max(&mut self, a: L, b: L) -> L {
        if a == b || b == self.zero {
            a
        } else if a == self.zero {
            b
        } else {
            self.level(Level::Max(a, b))
        }
    }

    /// `imax`, with semantics-preserving simplifications.
    pub fn imax(&mut self, a: L, b: L) -> L {
        match self.lnode(b) {
            Level::Succ(_) => self.max(a, b),
            Level::Zero => b,
            _ if a == self.zero || a == b => b,
            _ => self.level(Level::IMax(a, b)),
        }
    }

    pub fn list(&mut self, ls: &[L]) -> Ls {
        if let Some(&x) = self.list_map.get(ls) {
            return x;
        }
        let id = Ls(self.lists.len() as u32);
        self.lists.push(ls.into());
        self.list_map.insert(ls.into(), id);
        id
    }

    pub fn list_of(&self, ls: Ls) -> &[L] {
        &self.lists[ls.0 as usize]
    }

    pub fn level_params(&self, l: L, out: &mut Vec<NameId>) {
        match self.lnode(l) {
            Level::Zero => {}
            Level::Param(p) => {
                if !out.contains(&p) {
                    out.push(p)
                }
            }
            Level::Succ(a) => self.level_params(a, out),
            Level::Max(a, b) | Level::IMax(a, b) => {
                self.level_params(a, out);
                self.level_params(b, out);
            }
        }
    }

    pub fn instantiate_level(&mut self, l: L, ps: &[NameId], ls: &[L]) -> L {
        if !self.level_has_param[l.0 as usize] {
            return l;
        }
        match self.lnode(l) {
            Level::Zero => l,
            Level::Param(p) => ps.iter().position(|&q| q == p).map_or(l, |i| ls[i]),
            Level::Succ(a) => {
                let a = self.instantiate_level(a, ps, ls);
                self.succ(a)
            }
            Level::Max(a, b) => {
                let (a, b) = (self.instantiate_level(a, ps, ls), self.instantiate_level(b, ps, ls));
                self.max(a, b)
            }
            Level::IMax(a, b) => {
                let (a, b) = (self.instantiate_level(a, ps, ls), self.instantiate_level(b, ps, ls));
                self.imax(a, b)
            }
        }
    }

    /// Decide `a ≤ b` for every assignment of the universe parameters.
    ///
    /// Complete decision procedure: split each parameter into "is zero" or
    /// "is p'+1", which removes every `imax`. Each side is then a max of a
    /// constant and terms `p + k`, which compare directly.
    pub fn leq(&mut self, a: L, b: L) -> bool {
        if a == b || a == self.zero {
            return true;
        }
        if let Some(&r) = self.leq_cache.get(&(a, b)) {
            return r;
        }
        let mut ps = Vec::new();
        self.level_params(a, &mut ps);
        self.level_params(b, &mut ps);
        // More than 16 parameters in one comparison never happens in practice;
        // answer "no", which can only make checking fail, never succeed wrongly.
        let r = ps.len() <= 16
            && (0u32..(1 << ps.len())).all(|mask| {
                let na = self.norm(a, &ps, mask);
                let nb = self.norm(b, &ps, mask);
                norm_leq(&na, &nb)
            });
        self.leq_cache.insert((a, b), r);
        r
    }

    pub fn level_eq(&mut self, a: L, b: L) -> bool {
        a == b || (self.leq(a, b) && self.leq(b, a))
    }

    pub fn is_zero(&mut self, l: L) -> bool {
        let z = self.zero;
        self.leq(l, z)
    }

    pub fn is_never_zero(&mut self, l: L) -> bool {
        let z = self.zero;
        let one = self.succ(z);
        self.leq(one, l)
    }

    fn norm(&self, l: L, ps: &[NameId], mask: u32) -> Norm {
        match self.lnode(l) {
            Level::Zero => Norm::default(),
            Level::Param(p) => {
                let i = ps.iter().position(|&q| q == p).expect("collected");
                if mask & (1 << i) == 0 { Norm::default() } else { Norm { c: 0, terms: vec![(p, 1)] } }
            }
            Level::Succ(a) => {
                let mut n = self.norm(a, ps, mask);
                n.c += 1;
                for t in &mut n.terms {
                    t.1 += 1;
                }
                n
            }
            Level::Max(a, b) => self.norm(a, ps, mask).max(self.norm(b, ps, mask)),
            Level::IMax(a, b) => {
                let nb = self.norm(b, ps, mask);
                if nb.is_zero() { nb } else { self.norm(a, ps, mask).max(nb) }
            }
        }
    }

    // ---------- terms ----------

    pub fn mk(&mut self, n: Node) -> E {
        if let Some(&e) = self.map.get(&n) {
            return e;
        }
        let i = |s: &Self, e: E| s.info[e.0 as usize];
        let info = match n {
            Node::BVar(k) => Info { lbr: k + 1, has_fvar: false, has_lparam: false },
            Node::FVar(_) => Info { lbr: 0, has_fvar: true, has_lparam: false },
            Node::Sort(l) => Info { lbr: 0, has_fvar: false, has_lparam: self.level_has_param[l.0 as usize] },
            Node::Const(_, ls) => Info {
                lbr: 0,
                has_fvar: false,
                has_lparam: self.lists[ls.0 as usize].iter().any(|l| self.level_has_param[l.0 as usize]),
            },
            Node::App(f, a) => {
                let (x, y) = (i(self, f), i(self, a));
                Info {
                    lbr: x.lbr.max(y.lbr),
                    has_fvar: x.has_fvar || y.has_fvar,
                    has_lparam: x.has_lparam || y.has_lparam,
                }
            }
            Node::Lam(d, b) | Node::Pi(d, b) => {
                let (x, y) = (i(self, d), i(self, b));
                Info {
                    lbr: x.lbr.max(y.lbr.saturating_sub(1)),
                    has_fvar: x.has_fvar || y.has_fvar,
                    has_lparam: x.has_lparam || y.has_lparam,
                }
            }
            Node::Let(t, v, b) => {
                let (x, y, z) = (i(self, t), i(self, v), i(self, b));
                Info {
                    lbr: x.lbr.max(y.lbr).max(z.lbr.saturating_sub(1)),
                    has_fvar: x.has_fvar || y.has_fvar || z.has_fvar,
                    has_lparam: x.has_lparam || y.has_lparam || z.has_lparam,
                }
            }
            Node::Nat(_) | Node::Str(_) => Info { lbr: 0, has_fvar: false, has_lparam: false },
            Node::Proj(_, _, x) => i(self, x),
        };
        let e = E(self.nodes.len() as u32);
        self.nodes.push(n);
        self.info.push(info);
        self.map.insert(n, e);
        e
    }

    #[inline]
    pub fn node(&self, e: E) -> Node {
        self.nodes[e.0 as usize]
    }

    #[inline]
    pub fn info(&self, e: E) -> Info {
        self.info[e.0 as usize]
    }

    pub fn nat(&mut self, n: BigUint) -> E {
        let i = match self.nat_map.get(&n) {
            Some(&i) => i,
            None => {
                let i = self.nats.len() as u32;
                self.nats.push(n.clone());
                self.nat_map.insert(n, i);
                i
            }
        };
        self.mk(Node::Nat(i))
    }

    pub fn nat_val(&self, i: u32) -> &BigUint {
        &self.nats[i as usize]
    }

    pub fn str_lit(&mut self, s: &str) -> E {
        let i = match self.str_map.get(s) {
            Some(&i) => i,
            None => {
                let i = self.strs.len() as u32;
                self.strs.push(s.into());
                self.str_map.insert(s.into(), i);
                i
            }
        };
        self.mk(Node::Str(i))
    }

    pub fn str_val(&self, i: u32) -> &str {
        &self.strs[i as usize]
    }

    pub fn sort(&mut self, l: L) -> E {
        self.mk(Node::Sort(l))
    }

    pub fn cnst(&mut self, n: NameId, ls: &[L]) -> E {
        let ls = self.list(ls);
        self.mk(Node::Const(n, ls))
    }

    pub fn app(&mut self, f: E, a: E) -> E {
        self.mk(Node::App(f, a))
    }

    pub fn apps(&mut self, mut f: E, args: &[E]) -> E {
        for &a in args {
            f = self.app(f, a);
        }
        f
    }

    pub fn bvar(&mut self, i: u32) -> E {
        self.mk(Node::BVar(i))
    }

    /// Head and arguments of an application spine.
    pub fn spine(&self, mut e: E) -> (E, Vec<E>) {
        let mut args = Vec::new();
        while let Node::App(f, a) = self.node(e) {
            args.push(a);
            e = f;
        }
        args.reverse();
        (e, args)
    }

    pub fn head(&self, mut e: E) -> E {
        while let Node::App(f, _) = self.node(e) {
            e = f;
        }
        e
    }

    /// Replace loose bound variables: `BVar(i)` becomes `args[len-1-i]`, so
    /// the last argument fills the innermost binder.
    pub fn instantiate_rev(&mut self, e: E, args: &[E]) -> E {
        if args.is_empty() || self.info(e).lbr == 0 {
            return e;
        }
        let mut memo = FxHashMap::default();
        self.inst_go(e, 0, args, &mut memo)
    }

    fn inst_go(&mut self, e: E, off: u32, args: &[E], memo: &mut FxHashMap<(E, u32), E>) -> E {
        if self.info(e).lbr <= off {
            return e;
        }
        if let Some(&r) = memo.get(&(e, off)) {
            return r;
        }
        let r = match self.node(e) {
            Node::BVar(i) => {
                let n = args.len() as u32;
                if i - off < n {
                    let a = args[(n - 1 - (i - off)) as usize];
                    self.lift(a, off)
                } else {
                    self.bvar(i - n)
                }
            }
            Node::App(f, a) => {
                let (f, a) = (self.inst_go(f, off, args, memo), self.inst_go(a, off, args, memo));
                self.app(f, a)
            }
            Node::Lam(d, b) => {
                let (d, b) = (self.inst_go(d, off, args, memo), self.inst_go(b, off + 1, args, memo));
                self.mk(Node::Lam(d, b))
            }
            Node::Pi(d, b) => {
                let (d, b) = (self.inst_go(d, off, args, memo), self.inst_go(b, off + 1, args, memo));
                self.mk(Node::Pi(d, b))
            }
            Node::Let(t, v, b) => {
                let t = self.inst_go(t, off, args, memo);
                let v = self.inst_go(v, off, args, memo);
                let b = self.inst_go(b, off + 1, args, memo);
                self.mk(Node::Let(t, v, b))
            }
            Node::Proj(s, i, x) => {
                let x = self.inst_go(x, off, args, memo);
                self.mk(Node::Proj(s, i, x))
            }
            _ => e,
        };
        memo.insert((e, off), r);
        r
    }

    /// Shift loose bound variables of `e` up by `d`.
    pub fn lift(&mut self, e: E, d: u32) -> E {
        if d == 0 || self.info(e).lbr == 0 {
            return e;
        }
        let mut memo = FxHashMap::default();
        self.lift_go(e, 0, d, &mut memo)
    }

    fn lift_go(&mut self, e: E, off: u32, d: u32, memo: &mut FxHashMap<(E, u32), E>) -> E {
        if self.info(e).lbr <= off {
            return e;
        }
        if let Some(&r) = memo.get(&(e, off)) {
            return r;
        }
        let r = match self.node(e) {
            Node::BVar(i) => self.bvar(i + d),
            Node::App(f, a) => {
                let (f, a) = (self.lift_go(f, off, d, memo), self.lift_go(a, off, d, memo));
                self.app(f, a)
            }
            Node::Lam(x, b) => {
                let (x, b) = (self.lift_go(x, off, d, memo), self.lift_go(b, off + 1, d, memo));
                self.mk(Node::Lam(x, b))
            }
            Node::Pi(x, b) => {
                let (x, b) = (self.lift_go(x, off, d, memo), self.lift_go(b, off + 1, d, memo));
                self.mk(Node::Pi(x, b))
            }
            Node::Let(t, v, b) => {
                let t = self.lift_go(t, off, d, memo);
                let v = self.lift_go(v, off, d, memo);
                let b = self.lift_go(b, off + 1, d, memo);
                self.mk(Node::Let(t, v, b))
            }
            Node::Proj(s, i, x) => {
                let x = self.lift_go(x, off, d, memo);
                self.mk(Node::Proj(s, i, x))
            }
            _ => e,
        };
        memo.insert((e, off), r);
        r
    }

    /// Replace free variables by bound variables. `fvars` are given outermost
    /// first, so the last one becomes `BVar(0)`.
    pub fn abstract_fvars(&mut self, e: E, fvars: &[u32]) -> E {
        if fvars.is_empty() || !self.info(e).has_fvar {
            return e;
        }
        let mut memo = FxHashMap::default();
        self.abs_go(e, 0, fvars, &mut memo)
    }

    fn abs_go(&mut self, e: E, off: u32, fvars: &[u32], memo: &mut FxHashMap<(E, u32), E>) -> E {
        if !self.info(e).has_fvar {
            return e;
        }
        if let Some(&r) = memo.get(&(e, off)) {
            return r;
        }
        let r = match self.node(e) {
            Node::FVar(id) => match fvars.iter().rposition(|&f| f == id) {
                Some(k) => self.bvar(off + (fvars.len() - 1 - k) as u32),
                None => e,
            },
            Node::App(f, a) => {
                let (f, a) = (self.abs_go(f, off, fvars, memo), self.abs_go(a, off, fvars, memo));
                self.app(f, a)
            }
            Node::Lam(d, b) => {
                let (d, b) = (self.abs_go(d, off, fvars, memo), self.abs_go(b, off + 1, fvars, memo));
                self.mk(Node::Lam(d, b))
            }
            Node::Pi(d, b) => {
                let (d, b) = (self.abs_go(d, off, fvars, memo), self.abs_go(b, off + 1, fvars, memo));
                self.mk(Node::Pi(d, b))
            }
            Node::Let(t, v, b) => {
                let t = self.abs_go(t, off, fvars, memo);
                let v = self.abs_go(v, off, fvars, memo);
                let b = self.abs_go(b, off + 1, fvars, memo);
                self.mk(Node::Let(t, v, b))
            }
            Node::Proj(s, i, x) => {
                let x = self.abs_go(x, off, fvars, memo);
                self.mk(Node::Proj(s, i, x))
            }
            _ => e,
        };
        memo.insert((e, off), r);
        r
    }

    /// Substitute universe parameters.
    pub fn instantiate_lparams(&mut self, e: E, ps: &[NameId], ls: &[L]) -> E {
        if ps.is_empty() || !self.info(e).has_lparam {
            return e;
        }
        let mut memo = FxHashMap::default();
        self.ilp_go(e, ps, ls, &mut memo)
    }

    fn ilp_go(&mut self, e: E, ps: &[NameId], ls: &[L], memo: &mut FxHashMap<E, E>) -> E {
        if !self.info(e).has_lparam {
            return e;
        }
        if let Some(&r) = memo.get(&e) {
            return r;
        }
        let r = match self.node(e) {
            Node::Sort(l) => {
                let l = self.instantiate_level(l, ps, ls);
                self.sort(l)
            }
            Node::Const(n, lsid) => {
                let old: Vec<L> = self.list_of(lsid).to_vec();
                let new: Vec<L> = old.iter().map(|&l| self.instantiate_level(l, ps, ls)).collect();
                self.cnst(n, &new)
            }
            Node::App(f, a) => {
                let (f, a) = (self.ilp_go(f, ps, ls, memo), self.ilp_go(a, ps, ls, memo));
                self.app(f, a)
            }
            Node::Lam(d, b) => {
                let (d, b) = (self.ilp_go(d, ps, ls, memo), self.ilp_go(b, ps, ls, memo));
                self.mk(Node::Lam(d, b))
            }
            Node::Pi(d, b) => {
                let (d, b) = (self.ilp_go(d, ps, ls, memo), self.ilp_go(b, ps, ls, memo));
                self.mk(Node::Pi(d, b))
            }
            Node::Let(t, v, b) => {
                let t = self.ilp_go(t, ps, ls, memo);
                let v = self.ilp_go(v, ps, ls, memo);
                let b = self.ilp_go(b, ps, ls, memo);
                self.mk(Node::Let(t, v, b))
            }
            Node::Proj(s, i, x) => {
                let x = self.ilp_go(x, ps, ls, memo);
                self.mk(Node::Proj(s, i, x))
            }
            _ => e,
        };
        memo.insert(e, r);
        r
    }

    /// Does `e` mention any constant in `names`?
    pub fn mentions_const(&self, e: E, names: &[NameId]) -> bool {
        let mut stack = vec![e];
        let mut seen = rustc_hash::FxHashSet::default();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            match self.node(x) {
                Node::Const(n, _) if names.contains(&n) => return true,
                Node::App(f, a) => stack.extend([f, a]),
                Node::Lam(d, b) | Node::Pi(d, b) => stack.extend([d, b]),
                Node::Let(t, v, b) => stack.extend([t, v, b]),
                Node::Proj(_, _, y) => stack.push(y),
                _ => {}
            }
        }
        false
    }
}

/// `max(c, p₁+k₁, p₂+k₂, …)` with every pᵢ ranging over all naturals.
#[derive(Default, Debug)]
struct Norm {
    c: u64,
    terms: Vec<(NameId, u64)>,
}

impl Norm {
    fn is_zero(&self) -> bool {
        self.c == 0 && self.terms.is_empty()
    }
    fn max(mut self, o: Norm) -> Norm {
        self.c = self.c.max(o.c);
        for (p, k) in o.terms {
            match self.terms.iter_mut().find(|t| t.0 == p) {
                Some(t) => t.1 = t.1.max(k),
                None => self.terms.push((p, k)),
            }
        }
        self
    }
}

/// `a ≤ b` for all values of the variables.
fn norm_leq(a: &Norm, b: &Norm) -> bool {
    let b_min = b.terms.iter().map(|t| t.1).fold(b.c, u64::max);
    a.c <= b_min && a.terms.iter().all(|&(p, k)| b.terms.iter().any(|&(q, j)| q == p && j >= k))
}

impl Store {
    /// Describe the first place two terms differ (for diagnostics).
    pub fn first_difference(&self, a: E, b: E) -> Option<String> {
        if a == b {
            return None;
        }
        let (x, y) = (self.node(a), self.node(b));
        let kids = |n: Node| -> Vec<E> {
            match n {
                Node::App(f, a) => vec![f, a],
                Node::Lam(d, b) | Node::Pi(d, b) => vec![d, b],
                Node::Let(t, v, b) => vec![t, v, b],
                Node::Proj(_, _, e) => vec![e],
                _ => vec![],
            }
        };
        if std::mem::discriminant(&x) == std::mem::discriminant(&y) {
            let (kx, ky) = (kids(x), kids(y));
            if !kx.is_empty() {
                for (i, (p, q)) in kx.iter().zip(&ky).enumerate() {
                    if let Some(d) = self.first_difference(*p, *q) {
                        return Some(format!("{}.{i} > {d}", short(x)));
                    }
                }
            }
        }
        let lv = |n: Node| match n {
            Node::Sort(l) => format!(" level={:?}", self.lnode(l)),
            Node::Const(_, ls) => {
                format!(" levels={:?}", self.list_of(ls).iter().map(|l| self.lnode(*l)).collect::<Vec<_>>())
            }
            _ => String::new(),
        };
        Some(format!("{:?}{} vs {:?}{}", x, lv(x), y, lv(y)))
    }
}

fn short(n: Node) -> &'static str {
    match n {
        Node::App(..) => "app",
        Node::Lam(..) => "lam",
        Node::Pi(..) => "pi",
        Node::Let(..) => "let",
        Node::Proj(..) => "proj",
        _ => "?",
    }
}

impl Store {}
