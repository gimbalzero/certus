//! Dependency closure: everything a set of declarations transitively uses.
//!
//! This answers two questions:
//! - "What must be checked to trust this theorem?" Only the closure, not the
//!   whole library.
//! - "Which axioms does it rest on?" The axioms inside the closure. This is the
//!   seed of the statement audit (scoreboard axes 16 and 17).

use crate::export::*;
use std::collections::BTreeSet;

#[derive(Debug, Default)]
pub struct Closure {
    /// Declaration indices in the closure, ascending (file order).
    pub decls: Vec<usize>,
    /// Distinct expression nodes reached.
    pub exprs_visited: usize,
    /// Axioms in the closure.
    pub axioms: Vec<usize>,
    /// Unsafe or partial declarations in the closure.
    pub unsafe_or_partial: Vec<usize>,
    /// Constants referenced but never defined in the export (should be empty).
    pub missing: Vec<NameId>,
}

pub fn closure(env: &Env, roots: &[usize]) -> Closure {
    let mut seen_decl = vec![false; env.decls.len()];
    let mut seen_expr = vec![false; env.exprs.len()];
    let mut work: Vec<usize> = Vec::new();
    for &r in roots {
        if !seen_decl[r] {
            seen_decl[r] = true;
            work.push(r);
        }
    }
    let mut stack: Vec<ExprId> = Vec::new();
    let mut refs: Vec<NameId> = Vec::new();
    let mut missing = BTreeSet::new();
    let mut exprs_visited = 0usize;

    while let Some(d) = work.pop() {
        stack.extend(env.decls[d].roots());
        while let Some(e) = stack.pop() {
            let seen = &mut seen_expr[e as usize];
            if *seen {
                continue;
            }
            *seen = true;
            exprs_visited += 1;
            match &env.exprs[e as usize] {
                Expr::Const { name, .. } => refs.push(*name),
                Expr::App { f, a } => stack.extend([*f, *a]),
                Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => stack.extend([*ty, *body]),
                Expr::Let { ty, val, body, .. } => stack.extend([*ty, *val, *body]),
                Expr::Proj { type_name, structure, .. } => {
                    refs.push(*type_name);
                    stack.push(*structure);
                }
                Expr::BVar(_) | Expr::Sort(_) | Expr::NatLit(_) | Expr::StrLit(_) => {}
            }
        }
        for n in refs.drain(..) {
            match env.decl_of_name.get(&n) {
                Some(&j) if !seen_decl[j] => {
                    seen_decl[j] = true;
                    work.push(j);
                }
                Some(_) => {}
                None => {
                    missing.insert(n);
                }
            }
        }
    }

    let decls: Vec<usize> = (0..env.decls.len()).filter(|&i| seen_decl[i]).collect();
    let axioms = decls.iter().copied().filter(|&i| matches!(env.decls[i], Decl::Axiom(_))).collect();
    let unsafe_or_partial = decls.iter().copied().filter(|&i| env.decls[i].is_unsafe_or_partial()).collect();
    Closure { decls, exprs_visited, axioms, unsafe_or_partial, missing: missing.into_iter().collect() }
}
