//! Checking inductive types, and regenerating their recursors.
//!
//! The export ships recursors (`T.rec`) with their types and reduction rules.
//! Certus does not trust them: it rebuilds each one from the type and
//! constructor declarations, following the construction in Lean 4's kernel,
//! and requires the result to match the export exactly (up to binder names,
//! which the term store ignores).

use crate::env::{ConstInfo, Kind, RecRule};
use crate::tc::{R, TC};
use crate::term::{E, L, Level, Node};
use certus_core::export::{Name, NameId};
use std::sync::Arc;

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
    names: &'b [Name],
    blk: &'b Block,
    np: usize,
    params: Vec<E>,
    levels: Vec<L>,
    result_level: L,
    ind_names: Vec<NameId>,
}

/// Check a block and return every constant it defines.
pub fn check_block(tc: &mut TC, names: &[Name], blk: &Block) -> R<Vec<(NameId, ConstInfo)>> {
    let Some(first) = blk.types.first() else { return Err("inductive block with no types".into()) };
    if blk.types.iter().any(|t| t.is_unsafe)
        || blk.ctors.iter().any(|c| c.is_unsafe)
        || blk.recs.iter().any(|r| r.is_unsafe)
    {
        return Err("unsafe inductive types are not accepted".into());
    }
    if blk.types.iter().any(|t| t.num_nested > 0) {
        return Err("nested inductive types are not supported yet".into());
    }
    let lparams = first.lparams.clone();
    check_distinct(&lparams)?;
    if blk.types.iter().any(|t| t.lparams != lparams) || blk.ctors.iter().any(|c| c.lparams != lparams) {
        return Err("inductive block with inconsistent universe parameters".into());
    }
    tc.lparams = lparams.clone();
    let ind_names: Vec<NameId> = blk.types.iter().map(|t| t.name).collect();
    for t in &blk.types {
        if t.all != ind_names {
            return Err("inductive `all` list does not match the block".into());
        }
        if t.num_params != first.num_params {
            return Err("inductive types in a block disagree on parameters".into());
        }
    }
    let levels: Vec<L> = lparams.iter().map(|&p| tc.st.level(Level::Param(p))).collect();
    let mut c = Checker {
        tc,
        names,
        blk,
        np: first.num_params as usize,
        params: Vec::new(),
        levels,
        result_level: L(0),
        ind_names,
    };
    c.check_types()?;
    c.check_ctors()?;
    c.check_recs()
}

fn check_distinct(ps: &[NameId]) -> R<()> {
    for (i, p) in ps.iter().enumerate() {
        if ps[..i].contains(p) {
            return Err("duplicate universe parameter".into());
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
            let mut ty = t.ty;
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
        if blk.recs.len() != blk.types.len() {
            return Err("expected one recursor per inductive type".into());
        }
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
            let mut ty = t.ty;
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

        let all: Vec<NameId> = self.ind_names.clone();
        let mut out = Vec::new();
        let mut minor_idx = 0usize;
        for (ti, t) in blk.types.iter().enumerate() {
            let r = &blk.recs[ti];
            if !self.is_rec_name(r.name, t.name) {
                return Err("recursor has an unexpected name".into());
            }
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
                rules.push(RecRule { ctor: cname, nfields: fields.len() as u32, rhs });
                minor_idx += 1;
            }
            if r.rules.len() != rules.len()
                || r.rules.iter().zip(&rules).any(|(a, b)| a.ctor != b.ctor || a.nfields != b.nfields || a.rhs != b.rhs)
            {
                return Err("recursor rules do not match the ones generated from the inductive".into());
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
                        major_induct: t.name,
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

        let mut result = Vec::new();
        for t in &blk.types {
            result.push((t.name, (*self.tc.local[&t.name]).clone()));
        }
        for c in &blk.ctors {
            result.push((c.name, (*self.tc.local[&c.name]).clone()));
        }
        result.extend(out);
        Ok(result)
    }

    fn is_rec_name(&self, rec: NameId, ind: NameId) -> bool {
        matches!(&self.names[rec as usize], Name::Str { pre, s } if *pre == ind && s == "rec")
    }
}
