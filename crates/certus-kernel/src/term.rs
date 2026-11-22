//! Hash-consed terms and universe levels.
//!
//! Every term is interned, so structurally equal terms share one id. Binder
//! names and binder info are dropped, since the kernel never looks at them.
//! As a result, alpha-equivalent terms have the *same* id, and the cheapest
//! definitional-equality check is a single integer comparison.

use certus_core::export::NameId;
use num_bigint::BigUint;
use rustc_hash::FxHashMap;
use std::sync::Arc;

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

// `PartialEq` is written out below; it is plain structural equality, so it
// agrees with the derived `Hash`.
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Clone, Copy, Eq, Hash, Debug)]
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

// Written out instead of derived only so that it is always inlined: it runs
// on every hash-consing lookup.
impl PartialEq for Node {
    #[inline(always)]
    fn eq(&self, o: &Node) -> bool {
        use Node::*;
        match (*self, *o) {
            (BVar(a), BVar(b)) | (FVar(a), FVar(b)) | (Nat(a), Nat(b)) | (Str(a), Str(b)) => a == b,
            (Sort(a), Sort(b)) => a == b,
            (Const(a, x), Const(b, y)) => a == b && x == y,
            (App(a, x), App(b, y)) | (Lam(a, x), Lam(b, y)) | (Pi(a, x), Pi(b, y)) => a == b && x == y,
            (Let(a, x, p), Let(b, y, q)) => a == b && x == y && p == q,
            (Proj(a, i, x), Proj(b, j, y)) => a == b && i == j && x == y,
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Info {
    /// One more than the largest loose bound variable (0 = closed).
    pub lbr: u32,
    pub has_fvar: bool,
    pub has_lparam: bool,
}

/// End of a `nat_next` chain.
const NO_NAT: u32 = u32::MAX;

/// The interned objects themselves: terms, levels, level lists and literals.
#[derive(Default)]
struct Tables {
    nodes: Vec<Node>,
    info: Vec<Info>,
    map: FxHashMap<Node, E>,
    levels: Vec<Level>,
    level_has_param: Vec<bool>,
    lmap: FxHashMap<Level, L>,
    lists: Vec<Box<[L]>>,
    list_map: FxHashMap<Box<[L]>, Ls>,
    nats: Vec<BigUint>,
    /// Hash of a literal's value -> index of the last literal with that hash;
    /// `nat_next` chains literals whose values collide. Literals can be huge
    /// (megabits), so each value is stored once, in `nats`.
    nat_map: FxHashMap<u64, u32>,
    nat_next: Vec<u32>,
    strs: Vec<Box<str>>,
    str_map: FxHashMap<Box<str>, u32>,
}

/// A frozen store, shared read-only by several [`Store`]s (see [`Store::on`]).
#[derive(Clone)]
pub struct Frozen(Arc<Tables>);

/// Hash-consing store.
///
/// A store may sit on top of a [`Frozen`] base: every id below the base's
/// length (of terms, levels, level lists and literals) is the base's, and new
/// objects get ids from the base's length up. An object is interned in the
/// base or in the store, never in both, so equal terms still have equal ids.
/// An object whose parts are not all in the base cannot be in the base, so
/// only objects built from base parts are looked up there.
pub struct Store {
    base: Arc<Tables>,
    /// Lengths of the base's tables: nodes, levels, lists, nats, strings.
    nb: u32,
    lb: u32,
    sb: u32,
    natb: u32,
    strb: u32,
    own: Tables,
    leq_cache: FxHashMap<(L, L), bool>,
    /// Interned lists of universe parameter names (keys of `ilp_cache`).
    name_lists: FxHashMap<Box<[NameId]>, u32>,
    /// `instantiate_lparams(e, ps, ls)`, keyed by `(e, ps, ls)`. Unfolding a
    /// definition instantiates its value afresh each time; this makes repeats free.
    ilp_cache: FxHashMap<(E, u32, Ls), E>,
    /// Reusable memo tables for the term traversals (cleared after each use),
    /// so small substitutions do not allocate.
    memo_inst: FxHashMap<(E, u32), E>,
    memo_lift: FxHashMap<(E, u32), E>,
    memo_abs: FxHashMap<(E, u32), E>,
    memo_ilp: FxHashMap<E, E>,
    pub zero: L,
}

/// A memo table that grew past this many entries is dropped rather than
/// cleared, so one huge traversal does not slow down every later small one.
const MEMO_KEEP: usize = 1 << 9;

fn recycle<K, V>(mut m: FxHashMap<K, V>) -> FxHashMap<K, V> {
    if m.capacity() > MEMO_KEEP {
        FxHashMap::default()
    } else {
        m.clear();
        m
    }
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

impl Store {
    pub fn new() -> Self {
        Self::on_tables(Arc::new(Tables::default()))
    }

    /// An empty store on top of `base`: every object of `base` is available
    /// under its id there.
    pub fn on(base: &Frozen) -> Self {
        Self::on_tables(base.0.clone())
    }

    fn on_tables(base: Arc<Tables>) -> Self {
        let len = |n: usize| u32::try_from(n).expect("base store too large");
        let mut s = Store {
            nb: len(base.nodes.len()),
            lb: len(base.levels.len()),
            sb: len(base.lists.len()),
            natb: len(base.nats.len()),
            strb: len(base.strs.len()),
            base,
            own: Tables::default(),
            leq_cache: FxHashMap::default(),
            name_lists: FxHashMap::default(),
            ilp_cache: FxHashMap::default(),
            memo_inst: FxHashMap::default(),
            memo_lift: FxHashMap::default(),
            memo_abs: FxHashMap::default(),
            memo_ilp: FxHashMap::default(),
            zero: L(0),
        };
        s.zero = s.level(Level::Zero);
        s
    }

    /// Freeze this store, so that other stores can share its objects. Only a
    /// store without a base can be frozen.
    pub fn freeze(self) -> Frozen {
        assert!(self.nb == 0 && self.lb == 0 && self.sb == 0 && self.natb == 0 && self.strb == 0);
        Frozen(Arc::new(self.own))
    }

    pub fn num_nodes(&self) -> usize {
        self.nb as usize + self.own.nodes.len()
    }

    #[inline(always)]
    fn has_param(&self, l: L) -> bool {
        match self.own.level_has_param.get(l.0.wrapping_sub(self.lb) as usize) {
            Some(&x) => x,
            None => self.base.level_has_param[l.0 as usize],
        }
    }

    // ---------- levels ----------

    /// Intern a level exactly as given (no simplification).
    pub fn level(&mut self, l: Level) -> L {
        let in_base = match l {
            Level::Zero | Level::Param(_) => true,
            Level::Succ(a) => a.0 < self.lb,
            Level::Max(a, b) | Level::IMax(a, b) => a.0 < self.lb && b.0 < self.lb,
        };
        if self.lb != 0
            && in_base
            && let Some(&x) = self.base.lmap.get(&l)
        {
            return x;
        }
        if let Some(&x) = self.own.lmap.get(&l) {
            return x;
        }
        let hp = match l {
            Level::Zero => false,
            Level::Param(_) => true,
            Level::Succ(a) => self.has_param(a),
            Level::Max(a, b) | Level::IMax(a, b) => self.has_param(a) || self.has_param(b),
        };
        let id = L(self.lb + self.own.levels.len() as u32);
        self.own.levels.push(l);
        self.own.level_has_param.push(hp);
        self.own.lmap.insert(l, id);
        id
    }

    #[inline(always)]
    pub fn lnode(&self, l: L) -> Level {
        match self.own.levels.get(l.0.wrapping_sub(self.lb) as usize) {
            Some(&x) => x,
            None => self.base.levels[l.0 as usize],
        }
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
        if self.sb != 0
            && ls.iter().all(|l| l.0 < self.lb)
            && let Some(&x) = self.base.list_map.get(ls)
        {
            return x;
        }
        if let Some(&x) = self.own.list_map.get(ls) {
            return x;
        }
        let id = Ls(self.sb + self.own.lists.len() as u32);
        self.own.lists.push(ls.into());
        self.own.list_map.insert(ls.into(), id);
        id
    }

    #[inline]
    pub fn list_of(&self, ls: Ls) -> &[L] {
        match self.own.lists.get(ls.0.wrapping_sub(self.sb) as usize) {
            Some(x) => x,
            None => &self.base.lists[ls.0 as usize],
        }
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
        if !self.has_param(l) {
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

    /// `n`, if it is interned in the base.
    #[inline(never)]
    fn in_base(&self, n: Node) -> Option<E> {
        let b = |e: E| e.0 < self.nb;
        let parts_in_base = match n {
            Node::BVar(_) | Node::FVar(_) => true,
            Node::Sort(l) => l.0 < self.lb,
            Node::Const(_, ls) => ls.0 < self.sb,
            Node::App(f, a) | Node::Lam(f, a) | Node::Pi(f, a) => b(f) && b(a),
            Node::Let(t, v, x) => b(t) && b(v) && b(x),
            Node::Nat(i) => i < self.natb,
            Node::Str(i) => i < self.strb,
            Node::Proj(_, _, x) => b(x),
        };
        if parts_in_base { self.base.map.get(&n).copied() } else { None }
    }

    pub fn mk(&mut self, n: Node) -> E {
        if self.nb != 0
            && let Some(e) = self.in_base(n)
        {
            return e;
        }
        if let Some(&e) = self.own.map.get(&n) {
            return e;
        }
        let info = self.node_info(n);
        let id = self.nb as usize + self.own.nodes.len();
        let e = E(u32::try_from(id).expect("term store full"));
        self.own.nodes.push(n);
        self.own.info.push(info);
        self.own.map.insert(n, e);
        e
    }

    #[inline]
    fn node_info(&self, n: Node) -> Info {
        let i = |s: &Self, e: E| s.info(e);
        match n {
            Node::BVar(k) => Info { lbr: k + 1, has_fvar: false, has_lparam: false },
            Node::FVar(_) => Info { lbr: 0, has_fvar: true, has_lparam: false },
            Node::Sort(l) => Info { lbr: 0, has_fvar: false, has_lparam: self.has_param(l) },
            Node::Const(_, ls) => {
                Info { lbr: 0, has_fvar: false, has_lparam: self.list_of(ls).iter().any(|&l| self.has_param(l)) }
            }
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
        }
    }

    #[inline(always)]
    pub fn node(&self, e: E) -> Node {
        // Ids below the base's length wrap around to indices past the end.
        match self.own.nodes.get(e.0.wrapping_sub(self.nb) as usize) {
            Some(&x) => x,
            None => self.base.nodes[e.0 as usize],
        }
    }

    #[inline(always)]
    pub fn info(&self, e: E) -> Info {
        // Ids below the base's length wrap around to indices past the end.
        match self.own.info.get(e.0.wrapping_sub(self.nb) as usize) {
            Some(&x) => x,
            None => self.base.info[e.0 as usize],
        }
    }

    pub fn nat(&mut self, n: BigUint) -> E {
        use std::hash::BuildHasher;
        let h = rustc_hash::FxBuildHasher.hash_one(&n);
        // Base literals have indices below `natb`, this store's from `natb` up;
        // each table's chain holds its own indices.
        let find = |t: &Tables| {
            let mut cur = t.nat_map.get(&h).copied().unwrap_or(NO_NAT);
            while cur != NO_NAT && t.nats[cur as usize] != n {
                cur = t.nat_next[cur as usize];
            }
            (cur != NO_NAT).then_some(cur)
        };
        if let Some(i) = find(&self.base) {
            return self.mk(Node::Nat(i));
        }
        if let Some(i) = find(&self.own) {
            return self.mk(Node::Nat(self.natb + i));
        }
        let i = self.own.nats.len() as u32;
        self.own.nats.push(n);
        self.own.nat_next.push(self.own.nat_map.insert(h, i).unwrap_or(NO_NAT));
        self.mk(Node::Nat(self.natb + i))
    }

    pub fn nat_val(&self, i: u32) -> &BigUint {
        if i < self.natb { &self.base.nats[i as usize] } else { &self.own.nats[(i - self.natb) as usize] }
    }

    pub fn str_lit(&mut self, s: &str) -> E {
        let i = match self.base.str_map.get(s).or_else(|| self.own.str_map.get(s)) {
            Some(&i) => i,
            None => {
                let i = self.strb + self.own.strs.len() as u32;
                self.own.strs.push(s.into());
                self.own.str_map.insert(s.into(), i);
                i
            }
        };
        self.mk(Node::Str(i))
    }

    pub fn str_val(&self, i: u32) -> &str {
        if i < self.strb { &self.base.strs[i as usize] } else { &self.own.strs[(i - self.strb) as usize] }
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
    pub fn spine(&self, e: E) -> (E, Vec<E>) {
        // Count first, so the vector is allocated once at its final size.
        let mut n = 0;
        let mut h = e;
        while let Node::App(f, _) = self.node(h) {
            n += 1;
            h = f;
        }
        let mut args = vec![E(0); n];
        let mut cur = e;
        while let Node::App(f, a) = self.node(cur) {
            n -= 1;
            args[n] = a;
            cur = f;
        }
        (h, args)
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
        let mut memo = std::mem::take(&mut self.memo_inst);
        let r = self.inst_go(e, 0, args, &mut memo);
        self.memo_inst = recycle(memo);
        r
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
        let mut memo = std::mem::take(&mut self.memo_lift);
        let r = self.lift_go(e, 0, d, &mut memo);
        self.memo_lift = recycle(memo);
        r
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
        let mut memo = std::mem::take(&mut self.memo_abs);
        let r = self.abs_go(e, 0, fvars, &mut memo);
        self.memo_abs = recycle(memo);
        r
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
        let ls_id = self.list(ls);
        let ps_id = match self.name_lists.get(ps) {
            Some(&i) => i,
            None => {
                let i = self.name_lists.len() as u32;
                self.name_lists.insert(ps.into(), i);
                i
            }
        };
        if let Some(&r) = self.ilp_cache.get(&(e, ps_id, ls_id)) {
            return r;
        }
        let mut memo = std::mem::take(&mut self.memo_ilp);
        let r = self.ilp_go(e, ps, ls, &mut memo);
        self.memo_ilp = recycle(memo);
        self.ilp_cache.insert((e, ps_id, ls_id), r);
        r
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nat_literals_are_interned_by_value() {
        let mut st = Store::new();
        let big = BigUint::from(3u32).pow(100_000);
        let a = st.nat(big.clone());
        let b = st.nat(big.clone() + 1u32);
        assert_ne!(a, b);
        assert_eq!(st.nat(big.clone()), a);
        assert_eq!(st.nat(big + 1u32), b);
        assert_eq!(st.nat(BigUint::from(0u32)), st.nat(BigUint::from(0u32)));
        assert_eq!(st.own.nats.len(), 3, "each value is stored once");
    }

    #[test]
    fn overlay_store_shares_the_base_and_keeps_ids_canonical() {
        let mut b = Store::new();
        let u = b.level(Level::Param(7));
        let su = b.sort(u);
        let c = b.cnst(3, &[u]);
        let app = b.app(c, su);
        let big = b.nat(BigUint::from(10u32).pow(40));
        let s = b.str_lit("hi");
        let n = b.num_nodes();
        let base = b.freeze();
        let mut x = Store::on(&base);
        let mut y = Store::on(&base);
        for st in [&mut x, &mut y] {
            // Objects of the base keep their ids.
            let u2 = st.level(Level::Param(7));
            assert_eq!(u2, u);
            assert_eq!(st.sort(u2), su);
            let c2 = st.cnst(3, &[u2]);
            assert_eq!(c2, c);
            assert_eq!(st.app(c2, su), app);
            assert_eq!(st.nat(BigUint::from(10u32).pow(40)), big);
            assert_eq!(st.str_lit("hi"), s);
            assert_eq!(st.node(app), Node::App(c, su));
            // New objects get new ids, past the base, and are interned too.
            let v = st.succ(u);
            let sv = st.sort(v);
            assert!(sv.0 as usize >= n);
            assert_eq!(st.sort(v), sv);
            let a2 = st.app(app, sv);
            assert_eq!(st.app(app, sv), a2);
            assert_eq!(st.node(a2), Node::App(app, sv));
            let m = st.nat(BigUint::from(5u32));
            assert_eq!(st.nat(BigUint::from(5u32)), m);
            let Node::Nat(i) = st.node(m) else { panic!() };
            assert_eq!(st.nat_val(i), &BigUint::from(5u32));
            let t = st.str_lit("new");
            let Node::Str(j) = st.node(t) else { panic!() };
            assert_eq!(st.str_val(j), "new");
            assert!(st.info(sv).has_lparam && st.info(a2).has_lparam);
            let su2 = st.instantiate_lparams(sv, &[7], &[st.zero]);
            let one = st.succ(st.zero);
            assert_eq!(su2, st.sort(one));
        }
    }

    #[test]
    fn instantiate_lparams_cache_respects_parameter_order() {
        let mut st = Store::new();
        let (u, v) = (st.level(Level::Param(1)), st.level(Level::Param(2)));
        let one = st.succ(st.zero);
        let su = st.sort(u);
        let sv = st.sort(v);
        let e = st.mk(Node::Pi(su, sv)); // Sort u → Sort v
        let z = st.zero;
        let a = st.instantiate_lparams(e, &[1, 2], &[z, one]);
        let b = st.instantiate_lparams(e, &[2, 1], &[z, one]);
        assert_ne!(a, b);
        let (s0, s1) = (st.sort(z), st.sort(one));
        assert_eq!(a, st.mk(Node::Pi(s0, s1)));
        assert_eq!(b, st.mk(Node::Pi(s1, s0)));
        // Cached results agree with fresh ones.
        assert_eq!(st.instantiate_lparams(e, &[1, 2], &[z, one]), a);
        assert_eq!(st.instantiate_lparams(e, &[2, 1], &[z, one]), b);
    }
}
