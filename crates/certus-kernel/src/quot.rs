//! Quotient types. Lean's kernel builds `Quot`, `Quot.mk`, `Quot.lift` and
//! `Quot.ind` in, and the export repeats them. Certus rebuilds their types
//! and requires an exact match, after first checking that `Eq` is the
//! standard equality type (since `Quot.lift` mentions it).

use crate::env::{Kind, QuotKind};
use crate::tc::{R, TC};
use crate::term::{E, Level};
use certus_core::export::NameId;

pub fn check_quot(tc: &mut TC, kind: QuotKind, lparams: &[NameId], ty: E) -> R<()> {
    let b = tc.env.builtins.clone();
    let miss = "quotient declaration needs Eq, Eq.refl and the other Quot constants";
    let (eq, eq_refl, quot, quot_mk) = (b.eq.ok_or(miss)?, b.eq_refl.ok_or(miss)?, b.quot.ok_or(miss)?, b.quot_mk);
    check_eq(tc, eq, eq_refl)?;

    let expected_params = if kind == QuotKind::Lift { 2 } else { 1 };
    if lparams.len() != expected_params || (expected_params == 2 && lparams[0] == lparams[1]) {
        return Err("quotient constant has the wrong universe parameters".into());
    }
    let u = tc.st.level(Level::Param(lparams[0]));
    let sort_u = tc.st.sort(u);
    let prop = tc.st.sort(tc.st.zero);

    let alpha = tc.fresh_fvar(sort_u, None);
    let x = tc.fresh_fvar(alpha, None);
    let y = tc.fresh_fvar(alpha, None);
    let rel_ty = tc.bind(true, &[x, y], prop);
    let r = tc.fresh_fvar(rel_ty, None);
    let quot_c = tc.st.cnst(quot, &[u]);
    let quot_ar = tc.st.apps(quot_c, &[alpha, r]);

    let expected = match kind {
        QuotKind::Type => tc.bind(true, &[alpha, r], sort_u),
        QuotKind::Ctor => {
            let a = tc.fresh_fvar(alpha, None);
            tc.bind(true, &[alpha, r, a], quot_ar)
        }
        QuotKind::Lift => {
            let v = tc.st.level(Level::Param(lparams[1]));
            let sort_v = tc.st.sort(v);
            let beta = tc.fresh_fvar(sort_v, None);
            let x = tc.fresh_fvar(alpha, None);
            let f_ty = tc.bind(true, &[x], beta);
            let f = tc.fresh_fvar(f_ty, None);
            let a = tc.fresh_fvar(alpha, None);
            let bb = tc.fresh_fvar(alpha, None);
            let rab_ty = tc.st.apps(r, &[a, bb]);
            let rab = tc.fresh_fvar(rab_ty, None);
            let fa = tc.st.app(f, a);
            let fb = tc.st.app(f, bb);
            let eq_c = tc.st.cnst(eq, &[v]);
            let eq_app = tc.st.apps(eq_c, &[beta, fa, fb]);
            let h_ty = tc.bind(true, &[a, bb, rab], eq_app);
            let h = tc.fresh_fvar(h_ty, None);
            let q = tc.fresh_fvar(quot_ar, None);
            tc.bind(true, &[alpha, r, beta, f, h, q], beta)
        }
        QuotKind::Ind => {
            let quot_mk = quot_mk.ok_or(miss)?;
            let q0 = tc.fresh_fvar(quot_ar, None);
            let beta_ty = tc.bind(true, &[q0], prop);
            let beta = tc.fresh_fvar(beta_ty, None);
            let a = tc.fresh_fvar(alpha, None);
            let mk_c = tc.st.cnst(quot_mk, &[u]);
            let mk_a = tc.st.apps(mk_c, &[alpha, r, a]);
            let beta_mk = tc.st.app(beta, mk_a);
            let mk_ty = tc.bind(true, &[a], beta_mk);
            let mk = tc.fresh_fvar(mk_ty, None);
            let q = tc.fresh_fvar(quot_ar, None);
            let beta_q = tc.st.app(beta, q);
            tc.bind(true, &[alpha, r, beta, mk, q], beta_q)
        }
    };
    if expected != ty {
        return Err("quotient constant does not have the built-in type".into());
    }
    let s = tc.infer(ty, true)?;
    tc.ensure_sort(s)?;
    Ok(())
}

/// `Eq.{u} : {α : Sort u} → α → α → Prop` with the single constructor
/// `Eq.refl.{u} : ∀ {α : Sort u} (a : α), Eq a a`.
fn check_eq(tc: &mut TC, eq: NameId, eq_refl: NameId) -> R<()> {
    let bad = || "Eq is not the standard equality type".to_string();
    let e = tc.get_const(eq).ok_or("quotients need Eq to be declared first")?;
    let Kind::Induct { num_params: 2, num_indices: 1, ctors, .. } = &e.kind else { return Err(bad()) };
    if ctors.as_slice() != [eq_refl] || e.lparams.len() != 1 {
        return Err(bad());
    }
    let refl = tc.get_const(eq_refl).ok_or_else(bad)?;
    if refl.lparams != e.lparams {
        return Err(bad());
    }
    let u = tc.st.level(Level::Param(e.lparams[0]));
    let sort_u = tc.st.sort(u);
    let prop = tc.st.sort(tc.st.zero);
    let alpha = tc.fresh_fvar(sort_u, None);
    let a = tc.fresh_fvar(alpha, None);
    let b = tc.fresh_fvar(alpha, None);
    let eq_ty = tc.bind(true, &[alpha, a, b], prop);
    let eq_c = tc.st.cnst(eq, &[u]);
    let eq_aa = tc.st.apps(eq_c, &[alpha, a, a]);
    let refl_ty = tc.bind(true, &[alpha, a], eq_aa);
    if eq_ty != e.ty || refl_ty != refl.ty {
        return Err(bad());
    }
    Ok(())
}
