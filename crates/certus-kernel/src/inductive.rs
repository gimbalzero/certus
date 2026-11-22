//! Checking inductive types, and regenerating their recursors.
//!
//! The export ships recursors (`T.rec`) with their types and reduction rules.
//! Certus does not trust them: it rebuilds each one from the type and
//! constructor declarations, following the construction in Lean 4's kernel,
//! and requires the result to match the export exactly (up to binder names,
//! which the term store ignores).

use crate::env::{ConstInfo, Kind, RecRule};
use crate::tc::{R, TC};
use crate::term::{E, L, Level, Node, Store};
use certus_core::export::{Name, NameId};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

#[derive(Clone)]
pub struct IndType {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: E,
    pub num_params: u32,
    pub num_indices: u32,
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub num_nested: u32,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

#[derive(Clone)]
pub struct Ctor {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: E,
    pub induct: NameId,
    pub cidx: u32,
    pub num_params: u32,
    pub num_fields: u32,
    pub is_unsafe: bool,
}

#[derive(Clone)]
pub struct Rec {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: E,
    pub all: Vec<NameId>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub rules: Vec<RecRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

pub struct Block {
    pub types: Vec<IndType>,
    pub ctors: Vec<Ctor>,
    pub recs: Vec<Rec>,
}

struct Checker<'b, 'a> {
    tc: &'b mut TC<'a>,
    /// The block being checked: the declared types followed by the
    /// auxiliary types that replace nested occurrences (see `Nested`).
    blk: &'b Block,
    /// The block as exported.
    orig: &'b Block,
    nested: &'b Nested,
    np: usize,
    params: Vec<E>,
    levels: Vec<L>,
    result_level: L,
    /// Names of every type in `blk`, auxiliary ones included.
    ind_names: Vec<NameId>,
    /// Names of the declared types (the `all` field of every constant).
    orig_names: Vec<NameId>,
}

/// Check a block and return every constant it defines.
///
/// Nested inductive types are handled as in Lean 4's kernel (`elim_nested_inductive_fn`
/// and `environment::add_inductive`): every nested occurrence `J Ds` (an existing
/// inductive type applied to parameters that mention the block) is replaced by an
/// auxiliary type whose constructors are `J`'s, instantiated at `Ds`. The resulting
/// mutual block is checked, its recursors are generated, and the auxiliary types are
/// translated back (`aux As` to `J Ds`, `aux.c As` to `J.c Ds`) before the comparison
/// with the exported recursors, the auxiliary ones being `T.rec_1`, `T.rec_2`, ...
pub fn check_block(tc: &mut TC, names: &[Name], blk: &Block) -> R<Vec<(NameId, ConstInfo)>> {
    let Some(first) = blk.types.first() else { return Err("inductive block with no types".into()) };
    if blk.types.iter().any(|t| t.is_unsafe)
        || blk.ctors.iter().any(|c| c.is_unsafe)
        || blk.recs.iter().any(|r| r.is_unsafe)
    {
        return Err("unsafe inductive types are not accepted".into());
    }
    let lparams = first.lparams.clone();
    check_distinct(&lparams)?;
    if blk.types.iter().any(|t| t.lparams != lparams) || blk.ctors.iter().any(|c| c.lparams != lparams) {
        return Err("inductive block with inconsistent universe parameters".into());
    }
    tc.lparams = lparams.clone();
    let orig_names: Vec<NameId> = blk.types.iter().map(|t| t.name).collect();
    for t in &blk.types {
        if t.all != orig_names {
            return Err("inductive `all` list does not match the block".into());
        }
        if t.num_params != first.num_params {
            return Err("inductive types in a block disagree on parameters".into());
        }
    }
    let np = first.num_params as usize;
    let levels: Vec<L> = lparams.iter().map(|&p| tc.st.level(Level::Param(p))).collect();
    check_uniform_ind_occs(tc.st, blk, np, &levels)?;

    // Eliminate nested occurrences.
    let mut el = Elim {
        tc: &mut *tc,
        np,
        levels: levels.clone(),
        next_name: u32::try_from(names.len()).map_err(|_| "too many names")?,
        params: Vec::new(),
        block_names: orig_names.clone(),
        aux: Vec::new(),
    };
    let aux_blk = el.run(blk)?;
    let nested = el.finish();
    if blk.types.iter().any(|t| t.num_nested as usize != nested.aux.len()) {
        return Err("inductive metadata (numNested) is wrong".into());
    }
    let aux_blk = Block { recs: order_recs(names, blk, nested.aux.len())?, ..aux_blk };

    let ind_names: Vec<NameId> = aux_blk.types.iter().map(|t| t.name).collect();
    let mut c = Checker {
        tc: &mut *tc,
        blk: &aux_blk,
        orig: blk,
        nested: &nested,
        np,
        params: Vec::new(),
        levels,
        result_level: L(0),
        ind_names,
        orig_names,
    };
    c.check_types()?;
    c.check_ctors()?;
    let out = c.check_recs()?;
    if !nested.aux.is_empty() {
        recheck_nested(tc, &nested, &lparams, &out)?;
    }
    Ok(out)
}

fn check_distinct(ps: &[NameId]) -> R<()> {
    for (i, p) in ps.iter().enumerate() {
        if ps[..i].contains(p) {
            return Err("duplicate universe parameter".into());
        }
    }
    Ok(())
}

/// Every occurrence of a type of the block in a constructor type must be applied
/// to the block's universe levels and parameters (Lean's `check_uniform_ind_occs`).
/// This is checked syntactically, before anything is reduced or the parametric
/// arguments of nested occurrences are set aside.
fn check_uniform_ind_occs(st: &Store, blk: &Block, np: usize, levels: &[L]) -> R<()> {
    let names: Vec<NameId> = blk.types.iter().map(|t| t.name).collect();
    let mut seen = FxHashSet::default();
    for c in &blk.ctors {
        let mut stack = vec![(c.ty, 0u32)];
        while let Some((e, off)) = stack.pop() {
            if !seen.insert((e, off)) {
                continue;
            }
            let (h, args) = st.spine(e);
            if let Node::Const(n, ls) = st.node(h)
                && names.contains(&n)
                && args.len() <= np
            {
                let ok = args.len() == np
                    && off as usize >= np
                    && st.list_of(ls) == levels
                    && args.iter().enumerate().all(|(i, &a)| st.node(a) == Node::BVar(off - 1 - i as u32));
                if !ok {
                    return Err("invalid occurrence of a type being declared: it must be applied to the parameters \
                                and universe levels of the block"
                        .into());
                }
                continue;
            }
            match st.node(e) {
                Node::App(f, a) => stack.extend([(f, off), (a, off)]),
                Node::Lam(d, b) | Node::Pi(d, b) => stack.extend([(d, off), (b, off + 1)]),
                Node::Let(t, v, b) => stack.extend([(t, off), (v, off), (b, off + 1)]),
                Node::Proj(_, _, x) => stack.push((x, off)),
                _ => {}
            }
        }
    }
    Ok(())
}

/// An auxiliary type standing for the nested occurrence `key = J Ds`.
struct Aux {
    name: NameId,
    /// `J Ds`, over the free variables `Nested::params`.
    key: E,
    /// `J Ds` with the parameters abstracted (loose bound variables).
    key_abs: E,
    ty: E,
    /// Auxiliary constructor name, the constructor of `J` it copies, and its type.
    ctors: Vec<(NameId, NameId, E)>,
}

/// The result of eliminating nested occurrences.
struct Nested {
    np: usize,
    params: Vec<E>,
    aux: Vec<Aux>,
    /// Auxiliary constructor to (constructor of `J`, auxiliary type index).
    aux_ctor: FxHashMap<NameId, (NameId, usize)>,
    /// Auxiliary type name to its index.
    aux_index: FxHashMap<NameId, usize>,
}

struct Elim<'b, 'a> {
    tc: &'b mut TC<'a>,
    np: usize,
    levels: Vec<L>,
    /// Auxiliary names are numbered past the export's names, so no declaration
    /// can mention them.
    next_name: NameId,
    params: Vec<E>,
    block_names: Vec<NameId>,
    aux: Vec<Aux>,
}

impl Elim<'_, '_> {
    fn fresh_name(&mut self) -> R<NameId> {
        let n = self.next_name;
        self.next_name = n.checked_add(1).ok_or("too many names")?;
        Ok(n)
    }

    /// Open the first `np` binders of `ty` as free variables (domains as written).
    fn open_params(&mut self, mut ty: E) -> R<(Vec<E>, E)> {
        let mut xs = Vec::new();
        for _ in 0..self.np {
            let Node::Pi(d, b) = self.tc.st.node(ty) else {
                return Err("invalid inductive declaration: fewer binders than parameters".into());
            };
            let x = self.tc.fresh_fvar(d, None);
            xs.push(x);
            ty = self.tc.st.instantiate_rev(b, &[x]);
        }
        Ok((xs, ty))
    }

    fn fvar_ids(&self, xs: &[E]) -> Vec<u32> {
        xs.iter()
            .map(|&x| match self.tc.st.node(x) {
                Node::FVar(i) => i,
                _ => unreachable!(),
            })
            .collect()
    }

    /// `e` with the free variables `xs` replaced by the block's parameters.
    fn replace_params(&mut self, e: E, xs: &[E]) -> E {
        let ids = self.fvar_ids(xs);
        let a = self.tc.st.abstract_fvars(e, &ids);
        let ps = self.params.clone();
        self.tc.st.instantiate_rev(a, &ps)
    }

    /// Instantiate the first `n` (syntactic) binders of `e` with `args`.
    fn instantiate_pi_params(&mut self, mut e: E, args: &[E]) -> R<E> {
        for _ in 0..args.len() {
            let Node::Pi(_, b) = self.tc.st.node(e) else {
                return Err("invalid nested inductive datatype, ill-formed declaration".into());
            };
            e = b;
        }
        Ok(self.tc.st.instantiate_rev(e, args))
    }

    fn run(&mut self, blk: &Block) -> R<Block> {
        let (params, _) = self.open_params(blk.types[0].ty)?;
        self.params = params;
        let mut ctors = Vec::with_capacity(blk.ctors.len());
        for c in &blk.ctors {
            let ty = self.replace_in_ctor(c.ty)?;
            ctors.push(Ctor { ty, ..c.clone() });
        }
        let mut q = 0;
        while q < self.aux.len() {
            for k in 0..self.aux[q].ctors.len() {
                let ty = self.replace_in_ctor(self.aux[q].ctors[k].2)?;
                self.aux[q].ctors[k].2 = ty;
            }
            q += 1;
        }
        // Assemble the auxiliary mutual block.
        let first = &blk.types[0];
        let all: Vec<NameId> = self.block_names.clone();
        let mut types: Vec<IndType> = blk.types.clone();
        for a in &self.aux {
            types.push(IndType {
                name: a.name,
                lparams: first.lparams.clone(),
                ty: a.ty,
                num_params: first.num_params,
                num_indices: count_pis(self.tc.st, a.ty).saturating_sub(self.np) as u32,
                all: all.clone(),
                ctors: a.ctors.iter().map(|c| c.0).collect(),
                num_nested: first.num_nested,
                is_rec: first.is_rec,
                is_unsafe: false,
                is_reflexive: first.is_reflexive,
            });
            for (cidx, &(cname, _, cty)) in a.ctors.iter().enumerate() {
                ctors.push(Ctor {
                    name: cname,
                    lparams: first.lparams.clone(),
                    ty: cty,
                    induct: a.name,
                    cidx: cidx as u32,
                    num_params: first.num_params,
                    num_fields: count_pis(self.tc.st, cty).saturating_sub(self.np) as u32,
                    is_unsafe: false,
                });
            }
        }
        Ok(Block { types, ctors, recs: Vec::new() })
    }

    fn finish(self) -> Nested {
        let mut aux_ctor = FxHashMap::default();
        let mut aux_index = FxHashMap::default();
        for (i, a) in self.aux.iter().enumerate() {
            aux_index.insert(a.name, i);
            for &(c, jc, _) in &a.ctors {
                aux_ctor.insert(c, (jc, i));
            }
        }
        Nested { np: self.np, params: self.params, aux: self.aux, aux_ctor, aux_index }
    }

    /// Replace every nested occurrence in a constructor type. The parameters are
    /// re-opened for each constructor, as in Lean.
    fn replace_in_ctor(&mut self, cty: E) -> R<E> {
        let (xs, body) = self.open_params(cty)?;
        let mut memo = FxHashMap::default();
        let body = self.replace_all(body, &xs, &mut memo)?;
        Ok(self.tc.bind(true, &xs, body))
    }

    /// Top-down replacement (Lean's `replace`): a replaced term is not visited further.
    fn replace_all(&mut self, e: E, xs: &[E], memo: &mut FxHashMap<E, E>) -> R<E> {
        if let Some(&r) = memo.get(&e) {
            return Ok(r);
        }
        let r = if let Some(r) = self.replace_if_nested(e, xs)? {
            r
        } else {
            match self.tc.st.node(e) {
                Node::App(f, a) => {
                    let f = self.replace_all(f, xs, memo)?;
                    let a = self.replace_all(a, xs, memo)?;
                    self.tc.st.app(f, a)
                }
                Node::Lam(d, b) => {
                    let d = self.replace_all(d, xs, memo)?;
                    let b = self.replace_all(b, xs, memo)?;
                    self.tc.st.mk(Node::Lam(d, b))
                }
                Node::Pi(d, b) => {
                    let d = self.replace_all(d, xs, memo)?;
                    let b = self.replace_all(b, xs, memo)?;
                    self.tc.st.mk(Node::Pi(d, b))
                }
                Node::Let(t, v, b) => {
                    let t = self.replace_all(t, xs, memo)?;
                    let v = self.replace_all(v, xs, memo)?;
                    let b = self.replace_all(b, xs, memo)?;
                    self.tc.st.mk(Node::Let(t, v, b))
                }
                Node::Proj(s, i, x) => {
                    let x = self.replace_all(x, xs, memo)?;
                    self.tc.st.mk(Node::Proj(s, i, x))
                }
                _ => e,
            }
        };
        memo.insert(e, r);
        Ok(r)
    }

    /// If `e` is a nested occurrence `I Ds is`, return `Iaux xs is`, creating
    /// auxiliary types for every type of `I`'s block on first sight.
    fn replace_if_nested(&mut self, e: E, xs: &[E]) -> R<Option<E>> {
        if !matches!(self.tc.st.node(e), Node::App(..)) {
            return Ok(None);
        }
        let (h, args) = self.tc.st.spine(e);
        let Node::Const(i_name, i_ls) = self.tc.st.node(h) else { return Ok(None) };
        // Only previously declared inductive types can be nested.
        let Some(info) = self.tc.env.get(i_name) else { return Ok(None) };
        let Kind::Induct { num_params, all: i_all, .. } = &info.kind else { return Ok(None) };
        let inp = *num_params as usize;
        if inp > args.len() {
            return Ok(None);
        }
        let mut is_nested = false;
        let mut loose = false;
        for &a in &args[..inp] {
            loose |= self.tc.st.info(a).lbr != 0;
            is_nested |= self.tc.st.mentions_const(a, &self.block_names);
        }
        if !is_nested {
            return Ok(None);
        }
        if loose {
            return Err(
                "invalid nested inductive datatype: nested inductive datatypes parameters cannot contain local variables"
                    .into(),
            );
        }
        let i_lvls: Vec<L> = self.tc.st.list_of(i_ls).to_vec();
        let ias = self.tc.st.apps(h, &args[..inp]);
        let iparams = self.replace_params(ias, xs);
        let lv = self.levels.clone();
        let make = |el: &mut Self, aux: NameId| {
            let c = el.tc.st.cnst(aux, &lv);
            let c = el.tc.st.apps(c, xs);
            el.tc.st.apps(c, &args[inp..])
        };
        if let Some(a) = self.aux.iter().find(|a| a.key == iparams) {
            let n = a.name;
            return Ok(Some(make(self, n)));
        }
        let mut result = None;
        for &j_name in i_all.clone().iter() {
            let j_info = self.tc.env.get(j_name).ok_or("nested inductive datatype: unknown type in its block")?;
            let Kind::Induct { ctors: j_ctors, .. } = &j_info.kind else {
                return Err("nested inductive datatype: its block contains a non-inductive constant".into());
            };
            if j_info.lparams.len() != i_lvls.len() {
                return Err("nested inductive datatype: wrong number of universe levels".into());
            }
            let j = self.tc.st.cnst(j_name, &i_lvls);
            let jas = self.tc.st.apps(j, &args[..inp]);
            let aux_name = self.fresh_name()?;
            let mut aux_ty = self.tc.st.instantiate_lparams(j_info.ty, &j_info.lparams, &i_lvls);
            aux_ty = self.instantiate_pi_params(aux_ty, &args[..inp])?;
            aux_ty = self.tc.bind(true, xs, aux_ty);
            let key = self.replace_params(jas, xs);
            let pids = self.fvar_ids(&self.params.clone());
            let key_abs = self.tc.st.abstract_fvars(key, &pids);
            if j_name == i_name {
                result = Some(make(self, aux_name));
            }
            let mut ctors = Vec::new();
            for &jc in j_ctors {
                let c_info = self.tc.env.get(jc).ok_or("nested inductive datatype: unknown constructor")?;
                if !matches!(c_info.kind, Kind::Ctor { .. }) || c_info.lparams.len() != i_lvls.len() {
                    return Err("nested inductive datatype: ill-formed constructor".into());
                }
                let c_name = self.fresh_name()?;
                let mut cty = self.tc.st.instantiate_lparams(c_info.ty, &c_info.lparams, &i_lvls);
                cty = self.instantiate_pi_params(cty, &args[..inp])?;
                cty = self.tc.bind(true, xs, cty);
                ctors.push((c_name, jc, cty));
            }
            self.block_names.push(aux_name);
            self.aux.push(Aux { name: aux_name, key, key_abs, ty: aux_ty, ctors });
        }
        result.map(Some).ok_or_else(|| "nested inductive datatype: type missing from its own block".into())
    }
}

fn count_pis(st: &Store, mut e: E) -> usize {
    let mut n = 0;
    while let Node::Pi(_, b) = st.node(e) {
        e = b;
        n += 1;
    }
    n
}

/// The exported recursors in block order: `T.rec` for each declared type `T`,
/// then `T₀.rec_1`, `T₀.rec_2`, ... (named after the first type) for the
/// auxiliary types, as in Lean's `mk_aux_rec_name_map`.
fn order_recs(names: &[Name], blk: &Block, n_aux: usize) -> R<Vec<Rec>> {
    if blk.recs.len() != blk.types.len() + n_aux {
        return Err("expected one recursor per inductive type (auxiliary types included)".into());
    }
    let is = |r: &Rec, pre: NameId, s: &str| matches!(&names[r.name as usize], Name::Str { pre: p, s: q } if *p == pre && q == s);
    let mut out = Vec::new();
    for t in &blk.types {
        let r = blk.recs.iter().find(|r| is(r, t.name, "rec")).ok_or("recursor has an unexpected name")?;
        out.push(r.clone());
    }
    let main = blk.types[0].name;
    for i in 1..=n_aux {
        let s = format!("rec_{i}");
        let r = blk.recs.iter().find(|r| is(r, main, &s)).ok_or("recursor has an unexpected name")?;
        out.push(r.clone());
    }
    Ok(out)
}

impl Nested {
    /// Translate a term of the auxiliary block back (Lean's `restore_nested`):
    /// `aux As is` becomes `J Ds is` and `aux.c As fs` becomes `J.c Ds fs`, where
    /// `As` are the term's own leading `np` binders.
    fn restore(&self, tc: &mut TC, e: E) -> R<E> {
        if self.aux.is_empty() {
            return Ok(e);
        }
        let pi = matches!(tc.st.node(e), Node::Pi(..));
        let mut body = e;
        let mut xs = Vec::with_capacity(self.np);
        for _ in 0..self.np {
            let (Node::Pi(d, b) | Node::Lam(d, b)) = tc.st.node(body) else {
                return Err("failed to restore nested inductive types, fewer binders than parameters".into());
            };
            let x = tc.fresh_fvar(d, None);
            xs.push(x);
            body = tc.st.instantiate_rev(b, &[x]);
        }
        let mut memo = FxHashMap::default();
        let body = self.restore_go(tc, body, &xs, &mut memo)?;
        Ok(tc.bind(pi, &xs, body))
    }

    fn restore_go(&self, tc: &mut TC, t: E, xs: &[E], memo: &mut FxHashMap<E, E>) -> R<E> {
        if let Some(&r) = memo.get(&t) {
            return Ok(r);
        }
        let (h, args) = tc.st.spine(t);
        if let Node::Const(n, _) = tc.st.node(h) {
            if let Some(&i) = self.aux_index.get(&n) {
                if args.len() < self.np {
                    return Err(
                        "failed to restore nested inductive types, auxiliary type is not applied to all parameters"
                            .into(),
                    );
                }
                let new_t = tc.st.instantiate_rev(self.aux[i].key_abs, xs);
                let r = tc.st.apps(new_t, &args[self.np..]);
                memo.insert(t, r);
                return Ok(r);
            }
            if let Some(&(jc, i)) = self.aux_ctor.get(&n) {
                if args.len() < self.np {
                    return Err(
                        "failed to restore nested inductive types, auxiliary constructor is not applied to all parameters"
                            .into(),
                    );
                }
                let nested = tc.st.instantiate_rev(self.aux[i].key_abs, xs);
                let (ih, i_args) = tc.st.spine(nested);
                let Node::Const(_, i_ls) = tc.st.node(ih) else {
                    return Err("failed to restore nested inductive types, nested occurrence is not an inductive type application".into());
                };
                let lv: Vec<L> = tc.st.list_of(i_ls).to_vec();
                let f = tc.st.cnst(jc, &lv);
                let f = tc.st.apps(f, &i_args);
                let r = tc.st.apps(f, &args[self.np..]);
                memo.insert(t, r);
                return Ok(r);
            }
        }
        let r = match tc.st.node(t) {
            Node::App(f, a) => {
                let f = self.restore_go(tc, f, xs, memo)?;
                let a = self.restore_go(tc, a, xs, memo)?;
                tc.st.app(f, a)
            }
            Node::Lam(d, b) => {
                let d = self.restore_go(tc, d, xs, memo)?;
                let b = self.restore_go(tc, b, xs, memo)?;
                tc.st.mk(Node::Lam(d, b))
            }
            Node::Pi(d, b) => {
                let d = self.restore_go(tc, d, xs, memo)?;
                let b = self.restore_go(tc, b, xs, memo)?;
                tc.st.mk(Node::Pi(d, b))
            }
            Node::Let(ty, v, b) => {
                let ty = self.restore_go(tc, ty, xs, memo)?;
                let v = self.restore_go(tc, v, xs, memo)?;
                let b = self.restore_go(tc, b, xs, memo)?;
                tc.st.mk(Node::Let(ty, v, b))
            }
            Node::Proj(s, i, x) => {
                let x = self.restore_go(tc, x, xs, memo)?;
                tc.st.mk(Node::Proj(s, i, x))
            }
            _ => t,
        };
        memo.insert(t, r);
        Ok(r)
    }

    /// The constructor a rule of an auxiliary recursor is for, translated back.
    fn restore_ctor_name(&self, c: NameId) -> NameId {
        self.aux_ctor.get(&c).map_or(c, |&(jc, _)| jc)
    }

    /// The inductive type of the major premise of the recursor of type `ti`.
    fn major_induct(&self, tc: &TC, n_orig: usize, ti: usize, own: NameId) -> NameId {
        if ti < n_orig {
            return own;
        }
        match tc.st.node(tc.st.head(self.aux[ti - n_orig].key)) {
            Node::Const(n, _) => n,
            _ => unreachable!("auxiliary keys are constant applications"),
        }
    }
}

/// Lean re-checks, in an environment without the auxiliary types, the nested
/// occurrences `J Ds` (whose parametric arguments do not otherwise appear in
/// the auxiliary block) and everything the translation back produced.
fn recheck_nested(tc: &mut TC, nested: &Nested, lparams: &[NameId], out: &[(NameId, ConstInfo)]) -> R<()> {
    let keys: Vec<E> = nested.aux.iter().map(|a| tc.bind(false, &nested.params, a.key)).collect();
    let mut tc2 = TC::new(&mut *tc.st, tc.env, lparams.to_vec());
    for (n, info) in out {
        tc2.local.insert(*n, Arc::new(info.clone()));
    }
    // `J Ds` need not be a type: `J` may have indices.
    for k in keys {
        tc2.infer(k, true)?;
    }
    for (_, info) in out {
        tc2.lparams = info.lparams.clone();
        match &info.kind {
            Kind::Ctor { .. } | Kind::Rec { .. } => {
                let s = tc2.infer(info.ty, true)?;
                tc2.ensure_sort(s)?;
            }
            _ => {}
        }
        if let Kind::Rec { rules, .. } = &info.kind {
            for r in rules {
                tc2.infer(r.rhs, true)?;
            }
        }
    }
    Ok(())
}

impl Checker<'_, '_> {
    fn st(&mut self) -> &mut crate::term::Store {
        self.tc.st
    }

    fn check_types(&mut self) -> R<()> {
        for (ti, t) in self.blk.types.iter().enumerate() {
            let s = self.tc.infer(t.ty, true)?;
            self.tc.ensure_sort(s)?;
            // As in Lean's kernel, the type is put in weak head normal form
            // before each binder, so it may reach its parameters and indices
            // through definitions (`Presieve X := ∀ ⦃Y⦄, (Y ⟶ X) → Prop`).
            let mut ty = self.tc.whnf(t.ty)?;
            let mut i = 0usize;
            let mut nidx = 0u32;
            let mut idx_fvars = Vec::new();
            while let Node::Pi(d, b) = self.tc.st.node(ty) {
                if i < self.np {
                    if ti == 0 {
                        let p = self.local_for(d);
                        self.params.push(p);
                    } else {
                        let pt = self.param_type(i);
                        if !self.tc.is_def_eq(d, pt)? {
                            return Err("inductive types in a block disagree on parameter types".into());
                        }
                    }
                    let p = self.params[i];
                    ty = self.st().instantiate_rev(b, &[p]);
                } else {
                    let x = self.local_for(d);
                    idx_fvars.push(x);
                    ty = self.st().instantiate_rev(b, &[x]);
                    nidx += 1;
                }
                ty = self.tc.whnf(ty)?;
                i += 1;
            }
            if i < self.np {
                return Err("inductive type has fewer binders than parameters".into());
            }
            if nidx != t.num_indices {
                return Err("inductive type: wrong number of indices".into());
            }
            let l = self.tc.ensure_sort(ty)?;
            if ti == 0 {
                self.result_level = l;
            } else if !self.tc.st.level_eq(l, self.result_level) {
                return Err("inductive types in a block live in different universes".into());
            }
        }
        // Make the types available to the constructors.
        for t in &self.blk.types {
            let info = ConstInfo {
                lparams: t.lparams.clone(),
                ty: t.ty,
                kind: Kind::Induct {
                    num_params: t.num_params,
                    num_indices: t.num_indices,
                    all: t.all.clone(),
                    ctors: t.ctors.clone(),
                    is_rec: t.is_rec,
                },
            };
            if self.tc.get_const(t.name).is_some() {
                return Err("constant already declared".into());
            }
            self.tc.local.insert(t.name, Arc::new(info));
        }
        Ok(())
    }

    /// A free variable for a binder of type `d` (annotations stripped, as in Lean).
    fn local_for(&mut self, d: E) -> E {
        let d = self.tc.consume_annotations(d);
        self.tc.fresh_fvar(d, None)
    }

    fn param_type(&self, i: usize) -> E {
        let Node::FVar(id) = self.tc.st.node(self.params[i]) else { unreachable!() };
        self.tc.lctx[id as usize].0
    }

    fn has_ind_occ(&self, e: E) -> bool {
        self.tc.st.mentions_const(e, &self.ind_names)
    }

    /// Is `t` of the form `I params indices` for a type `I` of this block?
    fn valid_ind_app(&self, t: E) -> Option<usize> {
        let (h, args) = self.tc.st.spine(t);
        let Node::Const(n, ls) = self.tc.st.node(h) else { return None };
        let ti = self.ind_names.iter().position(|&m| m == n)?;
        if self.tc.st.list_of(ls) != self.levels.as_slice() {
            return None;
        }
        if args.len() != self.np + self.blk.types[ti].num_indices as usize {
            return None;
        }
        if args[..self.np] != self.params[..] {
            return None;
        }
        // Indices must not mention the types being declared (lean4#2125).
        if args[self.np..].iter().any(|&a| self.has_ind_occ(a)) {
            return None;
        }
        Some(ti)
    }

    fn is_rec_argument(&mut self, ty: E) -> R<Option<usize>> {
        let mut t = self.tc.whnf(ty)?;
        while let Node::Pi(d, b) = self.tc.st.node(t) {
            let x = self.local_for(d);
            let t2 = self.st().instantiate_rev(b, &[x]);
            t = self.tc.whnf(t2)?;
        }
        Ok(self.valid_ind_app(t))
    }

    fn check_positivity(&mut self, ty: E) -> R<()> {
        let t = self.tc.whnf(ty)?;
        if !self.has_ind_occ(t) {
            return Ok(());
        }
        if let Node::Pi(d, b) = self.tc.st.node(t) {
            if self.has_ind_occ(d) {
                return Err("non-positive occurrence of the type being defined".into());
            }
            let x = self.local_for(d);
            let b = self.st().instantiate_rev(b, &[x]);
            return self.check_positivity(b);
        }
        if self.valid_ind_app(t).is_some() {
            Ok(())
        } else {
            Err("invalid occurrence of the type being defined".into())
        }
    }

    fn check_ctors(&mut self) -> R<()> {
        let mut k = 0usize;
        let result_is_zero = self.tc.st.is_zero(self.result_level);
        for (ti, t) in self.blk.types.iter().enumerate() {
            for (cidx, &cname) in t.ctors.iter().enumerate() {
                let c = self.blk.ctors.get(k).ok_or("constructor list shorter than declared")?;
                k += 1;
                if c.name != cname || c.induct != t.name || c.cidx as usize != cidx {
                    return Err("constructor does not match its inductive type".into());
                }
                if c.num_params as usize != self.np {
                    return Err("constructor: wrong number of parameters".into());
                }
                let s = self.tc.infer(c.ty, true)?;
                self.tc.ensure_sort(s)?;
                let mut ty = c.ty;
                let mut i = 0usize;
                while let Node::Pi(d, b) = self.tc.st.node(ty) {
                    if i < self.np {
                        let pt = self.param_type(i);
                        if !self.tc.is_def_eq(d, pt)? {
                            return Err("constructor parameter does not match the inductive's".into());
                        }
                        let p = self.params[i];
                        ty = self.st().instantiate_rev(b, &[p]);
                    } else {
                        let fl = self.tc.sort_of(d)?;
                        if !(result_is_zero || self.tc.st.leq(fl, self.result_level)) {
                            return Err("constructor field lives in too large a universe".into());
                        }
                        self.check_positivity(d)?;
                        let x = self.local_for(d);
                        ty = self.st().instantiate_rev(b, &[x]);
                    }
                    i += 1;
                }
                if self.valid_ind_app(ty) != Some(ti) {
                    return Err("constructor has an invalid result type".into());
                }
                if (i - self.np) as u32 != c.num_fields {
                    return Err("constructor: wrong number of fields".into());
                }
            }
        }
        if k != self.blk.ctors.len() {
            return Err("constructor list longer than declared".into());
        }
        for c in &self.blk.ctors {
            if self.tc.get_const(c.name).is_some() {
                return Err("constant already declared".into());
            }
            let info = ConstInfo {
                lparams: c.lparams.clone(),
                ty: c.ty,
                kind: Kind::Ctor { induct: c.induct, cidx: c.cidx, num_params: c.num_params, num_fields: c.num_fields },
            };
            self.tc.local.insert(c.name, Arc::new(info));
        }
        Ok(())
    }

    /// Fields of a constructor (after the parameters), as fresh free variables.
    fn open_ctor(&mut self, cty: E) -> (Vec<E>, E) {
        let mut ty = cty;
        let mut fields = Vec::new();
        let mut i = 0usize;
        while let Node::Pi(d, b) = self.tc.st.node(ty) {
            if i < self.np {
                let p = self.params[i];
                ty = self.st().instantiate_rev(b, &[p]);
            } else {
                let x = self.local_for(d);
                fields.push(x);
                ty = self.st().instantiate_rev(b, &[x]);
            }
            i += 1;
        }
        (fields, ty)
    }

    fn fvar_type(&self, f: E) -> E {
        let Node::FVar(id) = self.tc.st.node(f) else { unreachable!() };
        self.tc.lctx[id as usize].0
    }

    fn elim_only_at_zero(&mut self) -> R<bool> {
        if self.tc.st.is_never_zero(self.result_level) {
            return Ok(false);
        }
        if self.blk.types.len() > 1 {
            return Ok(true);
        }
        let n = self.blk.types[0].ctors.len();
        if n > 1 {
            return Ok(true);
        }
        if n == 0 {
            return Ok(false);
        }
        let mut ty = self.blk.ctors[0].ty;
        let mut i = 0usize;
        let mut to_check = Vec::new();
        while let Node::Pi(d, b) = self.tc.st.node(ty) {
            let x = self.local_for(d);
            if i >= self.np {
                let l = self.tc.sort_of(d)?;
                if !self.tc.st.is_zero(l) {
                    to_check.push(x);
                }
            }
            ty = self.st().instantiate_rev(b, &[x]);
            i += 1;
        }
        let (_, result_args) = self.tc.st.spine(ty);
        Ok(to_check.iter().any(|x| !result_args.contains(x)))
    }

    /// For recursive field `u`, its type is `Π xs, I params idx`.
    fn rec_field_shape(&mut self, u: E) -> R<(Vec<E>, usize, Vec<E>)> {
        let uty = self.fvar_type(u);
        let mut t = self.tc.whnf(uty)?;
        let mut xs = Vec::new();
        while let Node::Pi(d, b) = self.tc.st.node(t) {
            let x = self.local_for(d);
            xs.push(x);
            let t2 = self.st().instantiate_rev(b, &[x]);
            t = self.tc.whnf(t2)?;
        }
        let ti = self.valid_ind_app(t).ok_or("malformed recursive field")?;
        let (_, args) = self.tc.st.spine(t);
        Ok((xs, ti, args[self.np..].to_vec()))
    }

    fn check_recs(&mut self) -> R<Vec<(NameId, ConstInfo)>> {
        let blk = self.blk;
        let n_orig = self.orig.types.len();
        // Universe of the motive.
        let elim_zero = self.elim_only_at_zero()?;
        let rec_lparams = blk.recs[0].lparams.clone();
        let elim_level = if elim_zero {
            if rec_lparams != blk.types[0].lparams {
                return Err("recursor universe parameters are wrong (expected elimination into Prop only)".into());
            }
            self.tc.st.zero
        } else {
            let (u, rest) = rec_lparams.split_first().ok_or("recursor is missing its motive universe")?;
            if rest != blk.types[0].lparams.as_slice() || rest.contains(u) {
                return Err("recursor universe parameters are wrong".into());
            }
            self.tc.st.level(Level::Param(*u))
        };
        let mut rec_levels = Vec::new();
        if !elim_zero {
            rec_levels.push(elim_level);
        }
        rec_levels.extend_from_slice(&self.levels);

        // K-like: a single Prop type with one constructor that has no fields.
        let k_target = blk.types.len() == 1
            && self.tc.st.is_zero(self.result_level)
            && blk.types[0].ctors.len() == 1
            && blk.ctors[0].num_fields == 0;

        // Motives, indices and major premises.
        let mut motives = Vec::new();
        let mut indices: Vec<Vec<E>> = Vec::new();
        let mut majors = Vec::new();
        for t in &blk.types {
            // Indices as Lean's `mk_rec_infos` finds them: from the type in weak
            // head normal form before each binder (see `check_types`).
            let mut ty = self.tc.whnf(t.ty)?;
            let mut i = 0usize;
            let mut idx = Vec::new();
            while let Node::Pi(d, b) = self.tc.st.node(ty) {
                if i < self.np {
                    let p = self.params[i];
                    ty = self.st().instantiate_rev(b, &[p]);
                } else {
                    let x = self.local_for(d);
                    idx.push(x);
                    ty = self.st().instantiate_rev(b, &[x]);
                }
                ty = self.tc.whnf(ty)?;
                i += 1;
            }
            let lv = self.levels.clone();
            let ind = self.tc.st.cnst(t.name, &lv);
            let params = self.params.clone();
            let mut major_ty = self.st().apps(ind, &params);
            major_ty = self.st().apps(major_ty, &idx);
            let major = self.tc.fresh_fvar(major_ty, None);
            let sort = self.st().sort(elim_level);
            let mty = self.tc.bind(true, &[major], sort);
            let mty = self.tc.bind(true, &idx, mty);
            motives.push(self.tc.fresh_fvar(mty, None));
            indices.push(idx);
            majors.push(major);
        }

        // Minor premises, one per constructor, in block order.
        let mut minors = Vec::new();
        for t in &blk.types {
            for &cname in &t.ctors {
                let c = blk.ctors.iter().find(|c| c.name == cname).expect("checked");
                let (fields, res) = self.open_ctor(c.ty);
                let mut ihs = Vec::new();
                for &f in &fields {
                    let fty = self.fvar_type(f);
                    if self.is_rec_argument(fty)?.is_none() {
                        continue;
                    }
                    let (xs, ti, idx) = self.rec_field_shape(f)?;
                    let mut m = self.st().apps(motives[ti], &idx);
                    let fx = self.st().apps(f, &xs);
                    m = self.st().app(m, fx);
                    let ih_ty = self.tc.bind(true, &xs, m);
                    ihs.push(self.tc.fresh_fvar(ih_ty, None));
                }
                let ti = self.valid_ind_app(res).expect("checked");
                let (_, rargs) = self.tc.st.spine(res);
                let np = self.np;
                let mut m = self.tc.st.apps(motives[ti], &rargs[np..]);
                let lv = self.levels.clone();
                let ctor_c = self.tc.st.cnst(cname, &lv);
                let params = self.params.clone();
                let mut ctor_app = self.st().apps(ctor_c, &params);
                ctor_app = self.st().apps(ctor_app, &fields);
                m = self.st().app(m, ctor_app);
                let mty = self.tc.bind(true, &ihs, m);
                let mty = self.tc.bind(true, &fields, mty);
                minors.push(self.tc.fresh_fvar(mty, None));
            }
        }

        let all: Vec<NameId> = self.orig_names.clone();
        let nested = self.nested;
        let mut out = Vec::new();
        let mut minor_idx = 0usize;
        for (ti, t) in blk.types.iter().enumerate() {
            // `check_block` put the exported recursors in block order, by name.
            let r = &blk.recs[ti];
            if r.lparams != rec_lparams {
                return Err("recursors in a block disagree on universe parameters".into());
            }
            // Type.
            let mut c = self.st().apps(motives[ti], &indices[ti]);
            c = self.st().app(c, majors[ti]);
            let mut ty = self.tc.bind(true, &[majors[ti]], c);
            ty = self.tc.bind(true, &indices[ti], ty);
            ty = self.tc.bind(true, &minors, ty);
            ty = self.tc.bind(true, &motives, ty);
            let params = self.params.clone();
            ty = self.tc.bind(true, &params, ty);
            let ty = nested.restore(self.tc, ty)?;
            if ty != r.ty {
                let d = self.tc.st.first_difference(ty, r.ty).unwrap_or_default();
                return Err(format!(
                    "recursor type does not match the one generated from the inductive (generated vs exported: {d})"
                ));
            }
            // Reduction rules.
            let mut rules = Vec::new();
            for &cname in &t.ctors {
                let c = blk.ctors.iter().find(|c| c.name == cname).expect("checked");
                let (fields, _) = self.open_ctor(c.ty);
                let mut vs = Vec::new();
                for &f in &fields {
                    let fty = self.fvar_type(f);
                    if self.is_rec_argument(fty)?.is_none() {
                        continue;
                    }
                    let (xs, tj, idx) = self.rec_field_shape(f)?;
                    let rec_c = self.st().cnst(blk.recs[tj].name, &rec_levels);
                    let mut app = self.st().apps(rec_c, &params);
                    app = self.st().apps(app, &motives);
                    app = self.st().apps(app, &minors);
                    app = self.st().apps(app, &idx);
                    let fx = self.st().apps(f, &xs);
                    app = self.st().app(app, fx);
                    vs.push(self.tc.bind(false, &xs, app));
                }
                let mut e = self.st().apps(minors[minor_idx], &fields);
                e = self.st().apps(e, &vs);
                let mut rhs = self.tc.bind(false, &fields, e);
                rhs = self.tc.bind(false, &minors, rhs);
                rhs = self.tc.bind(false, &motives, rhs);
                rhs = self.tc.bind(false, &params, rhs);
                let rhs = nested.restore(self.tc, rhs)?;
                let ctor = nested.restore_ctor_name(cname);
                rules.push(RecRule { ctor, nfields: fields.len() as u32, rhs });
                minor_idx += 1;
            }
            if r.rules.len() != rules.len() {
                return Err("recursor rules do not match the ones generated from the inductive (wrong number)".into());
            }
            for (a, b) in r.rules.iter().zip(&rules) {
                if a.ctor != b.ctor || a.nfields != b.nfields || a.rhs != b.rhs {
                    let d = self.tc.st.first_difference(b.rhs, a.rhs).unwrap_or_default();
                    return Err(format!(
                        "recursor rules do not match the ones generated from the inductive (generated vs exported: {d})"
                    ));
                }
            }
            if r.num_params as usize != self.np
                || r.num_indices != t.num_indices
                || r.num_motives as usize != motives.len()
                || r.num_minors as usize != minors.len()
                || r.k != k_target
                || r.all != all
            {
                return Err("recursor metadata does not match the inductive".into());
            }
            out.push((
                r.name,
                ConstInfo {
                    lparams: r.lparams.clone(),
                    ty: r.ty,
                    kind: Kind::Rec {
                        major_induct: nested.major_induct(self.tc, n_orig, ti, t.name),
                        num_params: r.num_params,
                        num_indices: r.num_indices,
                        num_motives: r.num_motives,
                        num_minors: r.num_minors,
                        rules,
                        k: k_target,
                    },
                },
            ));
        }

        // Cross-check the remaining metadata. Like Lean, both flags are
        // properties of the whole block.
        let mut is_rec = false;
        let mut is_reflexive = false;
        for c in &blk.ctors {
            let (fields, _) = self.open_ctor(c.ty);
            for f in fields {
                let fty = self.fvar_type(f);
                if self.has_ind_occ(fty) {
                    is_rec = true;
                    if matches!(self.tc.st.node(fty), Node::Pi(..)) {
                        is_reflexive = true;
                    }
                }
            }
        }
        if blk.types.iter().any(|t| t.is_rec != is_rec || t.is_reflexive != is_reflexive) {
            return Err("inductive metadata (isRec / isReflexive) is wrong".into());
        }

        // The declared types and their constructors, translated back. Lean adds the
        // translated constructor types; they must be the exported ones.
        let mut result = Vec::new();
        for t in &self.orig.types {
            result.push((t.name, (*self.tc.local[&t.name]).clone()));
        }
        for (k, c) in self.orig.ctors.iter().enumerate() {
            let ty = nested.restore(self.tc, blk.ctors[k].ty)?;
            if ty != c.ty {
                let d = self.tc.st.first_difference(ty, c.ty).unwrap_or_default();
                return Err(format!(
                    "constructor type does not survive the translation back from the auxiliary block ({d})"
                ));
            }
            let kind =
                Kind::Ctor { induct: c.induct, cidx: c.cidx, num_params: c.num_params, num_fields: c.num_fields };
            result.push((c.name, ConstInfo { lparams: c.lparams.clone(), ty: c.ty, kind }));
        }
        result.extend(out);
        Ok(result)
    }
}
