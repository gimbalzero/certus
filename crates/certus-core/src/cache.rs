//! Keys for the per-declaration verdict cache (issue #9).
//!
//! A declaration's key is a Merkle hash over everything its verdict can
//! depend on:
//!
//! ```text
//! key(d) = BLAKE3-derive_key(CONTEXT) of
//!          checker || alpha_hash(d) || n || key(dep_1) || … || key(dep_n)
//! ```
//!
//! - `checker` identifies the exact checker build (the CLI uses a hash of
//!   its own executable), so a new build never reuses an old verdict;
//! - `alpha_hash(d)` is the alpha-normal declaration hash (spec v1), which is
//!   independent of export order and binder names;
//! - the dependencies are the declarations whose constants `d` mentions,
//!   plus the implicit ones: `Nat` for a natural-number literal, the string
//!   constants for a string literal, and `Eq` for the quotient constants
//!   (their check compares against `Eq`). Their keys are sorted, so the key
//!   does not depend on export order either.
//!
//! Because each key covers the keys of its dependencies, it covers the whole
//! dependency closure: changing one declaration changes the key of exactly
//! that declaration and its (transitive) dependents.
//!
//! A declaration that mentions a constant not defined *before* it in the
//! file gets no key. Checking it fails exactly as it would without a cache,
//! and so does any declaration that depends on it.

use crate::export::*;
use crate::hash::{self, Hash};

/// Derive-key context of a cache key.
pub const CONTEXT: &str = "certus verdict cache v1 2026-11-22 declaration key";

/// Cache key of every declaration (`None`: not cacheable), indexed like `env.decls`.
pub fn keys(env: &Env, checker: &[u8; 32]) -> Vec<Option<Hash>> {
    let alpha = hash::hash_env_alpha(env);
    let implicit = Implicit::find(env);
    let mut keys: Vec<Option<Hash>> = Vec::with_capacity(env.decls.len());
    // Expression ids already visited for the current declaration.
    let mut stamp = vec![u32::MAX; env.exprs.len()];
    let mut stack: Vec<ExprId> = Vec::new();
    let mut deps: Vec<usize> = Vec::new();
    for (i, d) in env.decls.iter().enumerate() {
        deps.clear();
        let mut ok = true;
        let (mut nat, mut string) = (false, false);
        let mut refer = |n: NameId, deps: &mut Vec<usize>| match env.decl_of_name.get(&n) {
            Some(&j) if j < i => deps.push(j),
            Some(&j) if j == i => {}
            _ => ok = false,
        };
        stack.extend(d.roots());
        while let Some(e) = stack.pop() {
            if stamp[e as usize] == i as u32 {
                continue;
            }
            stamp[e as usize] = i as u32;
            match &env.exprs[e as usize] {
                Expr::Const { name, .. } => refer(*name, &mut deps),
                Expr::Proj { type_name, structure, .. } => {
                    refer(*type_name, &mut deps);
                    stack.push(*structure);
                }
                Expr::App { f, a } => stack.extend([*f, *a]),
                Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => stack.extend([*ty, *body]),
                Expr::Let { ty, val, body, .. } => stack.extend([*ty, *val, *body]),
                Expr::NatLit(_) => nat = true,
                Expr::StrLit(_) => string = true,
                Expr::BVar(_) | Expr::Sort(_) => {}
            }
        }
        let mut extra: Vec<Option<usize>> = Vec::new();
        if nat || string {
            extra.push(implicit.nat);
        }
        if string {
            extra.extend(&implicit.string);
        }
        if matches!(d, Decl::Quot(_)) {
            extra.push(implicit.eq);
        }
        for j in extra {
            match j {
                Some(j) if j < i => deps.push(j),
                Some(j) if j == i => {}
                _ => ok = false,
            }
        }
        let mut dep_keys: Vec<Hash> = Vec::with_capacity(deps.len());
        for &j in &deps {
            match keys[j] {
                Some(k) => dep_keys.push(k),
                None => ok = false,
            }
        }
        if !ok {
            keys.push(None);
            continue;
        }
        dep_keys.sort_unstable();
        dep_keys.dedup();
        let mut h = blake3::Hasher::new_derive_key(CONTEXT);
        h.update(checker).update(&alpha.decls[i]).update(&(dep_keys.len() as u64).to_le_bytes());
        for k in &dep_keys {
            h.update(k);
        }
        keys.push(Some(*h.finalize().as_bytes()));
    }
    keys
}

/// Declarations the kernel uses without the term mentioning them.
struct Implicit {
    nat: Option<usize>,
    string: Vec<Option<usize>>,
    eq: Option<usize>,
}

impl Implicit {
    fn find(env: &Env) -> Self {
        let names =
            ["Nat", "String", "String.ofList", "String.mk", "Char", "Char.ofNat", "List.nil", "List.cons", "Eq"];
        let f = env.find_decls(&names);
        // Exactly the constants the kernel expands string literals with (as in
        // `deps::closure`): `String.ofList` where it exists (Lean 4.22 on, where
        // `String.mk` is a later deprecated alias), otherwise `String.mk`. A
        // missing one makes the literal fail in the kernel anyway, so it does
        // not need a key.
        let expand = f[2].or(f[3]);
        let string = [f[1], expand, f[4], f[5], f[6], f[7]].into_iter().filter(Option::is_some).collect();
        Implicit { nat: f[0], string, eq: f[8] }
    }
}

/// Derive-key context of the integrity check stored with each entry.
const ENTRY_CONTEXT: &str = "certus verdict cache v1 2026-11-22 entry check";

/// The line stored for an accepted declaration with key `key`: the key and a
/// check value, both in hex. The check value catches truncated or corrupted
/// lines; an entry whose check value does not match is ignored.
pub fn entry(key: &Hash) -> String {
    format!("{} {}", hash::hex(key), hash::hex(&check_value(key)))
}

fn check_value(key: &Hash) -> Hash {
    let mut h = blake3::Hasher::new_derive_key(ENTRY_CONTEXT);
    h.update(b"accepted").update(key);
    *h.finalize().as_bytes()
}

/// Parse one stored line; `Some(key)` only if it is well formed and its
/// check value matches.
pub fn parse_entry(line: &str) -> Option<Hash> {
    let (k, c) = line.trim_end().split_once(' ')?;
    let key = unhex(k)?;
    (unhex(c)? == check_value(&key)).then_some(key)
}

fn unhex(s: &str) -> Option<Hash> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, o) in out.iter_mut().enumerate() {
        *o = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}
