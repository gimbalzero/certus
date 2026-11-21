//! Write a self-contained subset of an export: chosen declarations plus every
//! name, level and expression they need, renumbered densely. The result is a
//! valid lean4export 3.x file: a minimal *certificate* for those declarations.

use crate::export::{Decl, Env, Expr, Level, Name};
use serde_json::{Value, json};
use std::io::{self, Write};

pub fn write_subset<W: Write>(env: &Env, decls: &[usize], mut w: W) -> io::Result<()> {
    let (nn, nl, ne) = (env.names.len(), env.levels.len(), env.exprs.len());
    let mut need_name = vec![false; nn];
    let mut need_level = vec![false; nl];
    let mut need_expr = vec![false; ne];

    // Mark reachable expressions.
    let mut stack: Vec<u32> = Vec::new();
    for &i in decls {
        let mut d = env.decls[i].clone();
        let _ = d.map_names(&mut |n| {
            need_name[n as usize] = true;
            Ok(n)
        });
        stack.extend(d.roots());
    }
    while let Some(e) = stack.pop() {
        if std::mem::replace(&mut need_expr[e as usize], true) {
            continue;
        }
        match &env.exprs[e as usize] {
            Expr::Sort(l) => need_level[*l as usize] = true,
            Expr::Const { name, levels } => {
                need_name[*name as usize] = true;
                for &l in levels.iter() {
                    need_level[l as usize] = true;
                }
            }
            Expr::App { f, a } => stack.extend([*f, *a]),
            Expr::Lam { name, ty, body, .. } | Expr::Pi { name, ty, body, .. } => {
                need_name[*name as usize] = true;
                stack.extend([*ty, *body]);
            }
            Expr::Let { name, ty, val, body, .. } => {
                need_name[*name as usize] = true;
                stack.extend([*ty, *val, *body]);
            }
            Expr::Proj { type_name, structure, .. } => {
                need_name[*type_name as usize] = true;
                stack.push(*structure);
            }
            Expr::BVar(_) | Expr::NatLit(_) | Expr::StrLit(_) => {}
        }
    }
    // Levels close over their sub-levels and parameter names (ids are topological).
    for l in (0..nl).rev() {
        if !need_level[l] {
            continue;
        }
        match env.levels[l] {
            Level::Zero => {}
            Level::Succ(a) => need_level[a as usize] = true,
            Level::Max(a, b) | Level::IMax(a, b) => {
                need_level[a as usize] = true;
                need_level[b as usize] = true;
            }
            Level::Param(p) => need_name[p as usize] = true,
        }
    }
    // Names close over their prefixes.
    for n in (0..nn).rev() {
        if need_name[n] {
            match env.names[n] {
                Name::Str { pre, .. } | Name::Num { pre, .. } => need_name[pre as usize] = true,
                Name::Anon => {}
            }
        }
    }
    need_name[0] = true;
    need_level[0] = true;

    // Dense renumbering in original order (keeps references pointing backwards).
    let renumber = |need: &[bool]| {
        let mut map = vec![u32::MAX; need.len()];
        let mut next = 0u32;
        for (i, &k) in need.iter().enumerate() {
            if k {
                map[i] = next;
                next += 1;
            }
        }
        map
    };
    let (mn, ml, me) = (renumber(&need_name), renumber(&need_level), renumber(&need_expr));

    writeln!(w, "{}", json!({ "meta": env.meta }))?;
    for (i, n) in env.names.iter().enumerate().skip(1) {
        if !need_name[i] {
            continue;
        }
        let v = match n {
            Name::Str { pre, s } => json!({"in": mn[i], "str": {"pre": mn[*pre as usize], "str": s}}),
            Name::Num { pre, n } => json!({"in": mn[i], "num": {"pre": mn[*pre as usize], "i": n}}),
            Name::Anon => unreachable!(),
        };
        writeln!(w, "{v}")?;
    }
    for (i, l) in env.levels.iter().enumerate().skip(1) {
        if !need_level[i] {
            continue;
        }
        let id = ml[i];
        let v = match *l {
            Level::Succ(a) => json!({"il": id, "succ": ml[a as usize]}),
            Level::Max(a, b) => json!({"il": id, "max": [ml[a as usize], ml[b as usize]]}),
            Level::IMax(a, b) => json!({"il": id, "imax": [ml[a as usize], ml[b as usize]]}),
            Level::Param(p) => json!({"il": id, "param": mn[p as usize]}),
            Level::Zero => unreachable!(),
        };
        writeln!(w, "{v}")?;
    }
    for (i, e) in env.exprs.iter().enumerate() {
        if !need_expr[i] {
            continue;
        }
        let id = me[i];
        let x = |k: u32| me[k as usize];
        let v = match e {
            Expr::BVar(k) => json!({"ie": id, "bvar": k}),
            Expr::Sort(l) => json!({"ie": id, "sort": ml[*l as usize]}),
            Expr::Const { name, levels } => json!({"ie": id, "const": {"name": mn[*name as usize],
                "us": levels.iter().map(|&l| ml[l as usize]).collect::<Vec<_>>()}}),
            Expr::App { f, a } => json!({"ie": id, "app": {"fn": x(*f), "arg": x(*a)}}),
            Expr::Lam { name, ty, body, bi } => json!({"ie": id, "lam": {"name": mn[*name as usize],
                "type": x(*ty), "body": x(*body), "binderInfo": bi}}),
            Expr::Pi { name, ty, body, bi } => json!({"ie": id, "forallE": {"name": mn[*name as usize],
                "type": x(*ty), "body": x(*body), "binderInfo": bi}}),
            Expr::Let { name, ty, val, body, nondep } => json!({"ie": id, "letE": {"name": mn[*name as usize],
                "type": x(*ty), "value": x(*val), "body": x(*body), "nondep": nondep}}),
            Expr::NatLit(s) => json!({"ie": id, "natVal": &**s}),
            Expr::StrLit(s) => json!({"ie": id, "strVal": &**s}),
            Expr::Proj { type_name, idx, structure } => json!({"ie": id, "proj": {"typeName": mn[*type_name as usize],
                "idx": idx, "struct": x(*structure)}}),
        };
        writeln!(w, "{v}")?;
    }
    for &i in decls {
        let mut d = env.decls[i].clone();
        let _ = d.map_names(&mut |n| Ok(mn[n as usize]));
        d.map_exprs(&mut |e| me[e as usize]);
        let v: Value = match &d {
            Decl::Axiom(a) => json!({ "axiom": a }),
            Decl::Def(a) => json!({ "def": a }),
            Decl::Thm(a) => json!({ "thm": a }),
            Decl::Opaque(a) => json!({ "opaque": a }),
            Decl::Quot(a) => json!({ "quot": a }),
            Decl::Inductive(a) => json!({ "inductive": a }),
        };
        writeln!(w, "{v}")?;
    }
    w.flush()
}
