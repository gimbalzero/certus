//! The audit report of a check (scoreboard axes 16, 17 and 18): what exactly
//! was established, in a form a person or a program can review.
//!
//! The report names the checker build and the exact export (by the hash of its
//! bytes), gives the verdict, and for every target its statement, a hash of
//! that statement, the axioms it rests on and anything unsafe or partial it
//! depends on. It holds no timings, paths or other incidental data, and every
//! list is in a fixed order, so the same build checking the same export for
//! the same targets writes the same report, byte for byte.

use crate::export::*;
use crate::hash::{self, Hash, LazyHashes, Mode};
use crate::{deps, pretty};
use serde::Serialize;

/// The axioms accepted by Mathlib and by Lean's own checkers.
pub const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

/// Version tag of the report format.
pub const FORMAT: &str = "certus-report-v1";

/// How a check ended.
pub enum Verdict {
    Accepted,
    /// The export is invalid.
    Rejected(String),
    /// The checker ran out of resources before reaching a verdict.
    Declined(String),
}

#[derive(Serialize)]
pub struct Report {
    pub format: &'static str,
    /// Hash of the checker executable (see `docs/CACHE.md`).
    pub checker: String,
    pub export: ExportInfo,
    /// `"accepted"`, `"rejected"` or `"declined"`.
    pub verdict: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    /// Number of declarations checked: the targets' dependency closure, or
    /// the whole export when no targets were named.
    pub declarations: usize,
    /// How many of them were admitted from the verdict cache, which only
    /// holds declarations this same build accepted before (`docs/CACHE.md`),
    /// rather than type-checked in this run.
    pub from_cache: usize,
    /// Every axiom among the declarations checked, by name.
    pub axioms: Vec<Axiom>,
    /// Unsafe or partial declarations among those checked, by name.
    pub unsafe_or_partial: Vec<String>,
    /// The declarations named on the command line, in that order.
    pub targets: Vec<Target>,
}

#[derive(Serialize)]
pub struct ExportInfo {
    /// BLAKE3 hash of the export file's bytes, in hex.
    pub blake3: String,
    pub format: String,
    pub lean_version: String,
    pub lean_githash: String,
}

#[derive(Serialize)]
pub struct Axiom {
    pub name: String,
    /// `"standard"` (propext, Classical.choice, Quot.sound), `"sorry"`
    /// (`sorryAx`: an unfinished proof) or `"non-standard"`.
    pub class: &'static str,
}

#[derive(Serialize)]
pub struct Target {
    pub name: String,
    pub kind: &'static str,
    pub universe_params: Vec<String>,
    /// The statement (type), printed with notation.
    pub statement: String,
    /// Alpha-normal hash (spec v1) of the statement: binder names do not
    /// matter, everything else does. Equal hashes mean equal statements.
    pub statement_hash: String,
    /// Axioms the target depends on, transitively.
    pub axioms: Vec<Axiom>,
    pub unsafe_or_partial: Vec<String>,
    /// Size of the target's dependency closure.
    pub closure: usize,
}

fn classify(name: &str) -> &'static str {
    if STANDARD_AXIOMS.contains(&name) {
        "standard"
    } else if name == "sorryAx" {
        "sorry"
    } else {
        "non-standard"
    }
}

fn names(env: &Env, decls: &[usize]) -> Vec<String> {
    let mut v: Vec<String> = decls.iter().map(|&i| env.name_str(env.decls[i].primary_name())).collect();
    v.sort();
    v
}

fn axioms(env: &Env, decls: &[usize]) -> Vec<Axiom> {
    names(env, decls).into_iter().map(|name| Axiom { class: classify(&name), name }).collect()
}

/// The report of checking `targets` (indices into `env.decls`; none: the
/// whole export) with checker `checker`, where `bytes` is the hash of the
/// export file.
pub fn build(
    env: &Env,
    targets: &[usize],
    checker: &Hash,
    bytes: &Hash,
    verdict: Verdict,
    from_cache: usize,
) -> Report {
    let all: Vec<usize>;
    let scope = if targets.is_empty() {
        all = (0..env.decls.len()).collect();
        &all[..]
    } else {
        targets
    };
    let closure = deps::closure(env, scope);
    let mut alpha = LazyHashes::new(env, Mode::AlphaNormal);
    let targets = targets
        .iter()
        .map(|&t| {
            let d = &env.decls[t];
            let c = deps::closure(env, &[t]);
            let info = pretty::const_info(env, d.primary_name()).expect("a declaration's primary name is a constant");
            Target {
                name: env.name_str(d.primary_name()),
                kind: info.kind,
                universe_params: info.level_params.iter().map(|&p| pretty::name_to_string(env, p)).collect(),
                statement: pretty::statement(env, &info, pretty::Options::NOTATION),
                statement_hash: hash::hex(&alpha.expr(info.ty)),
                axioms: axioms(env, &c.axioms),
                unsafe_or_partial: names(env, &c.unsafe_or_partial),
                closure: c.decls.len(),
            }
        })
        .collect();
    let (verdict, message) = match verdict {
        Verdict::Accepted => ("accepted", None),
        Verdict::Rejected(m) => ("rejected", Some(m)),
        Verdict::Declined(m) => ("declined", Some(m)),
    };
    Report {
        format: FORMAT,
        checker: hash::hex(checker),
        export: ExportInfo {
            blake3: hash::hex(bytes),
            format: env.meta.format.version.clone(),
            lean_version: env.meta.lean.version.clone(),
            lean_githash: env.meta.lean.githash.clone(),
        },
        verdict,
        message,
        declarations: closure.decls.len(),
        from_cache,
        axioms: axioms(env, &closure.axioms),
        unsafe_or_partial: names(env, &closure.unsafe_or_partial),
        targets,
    }
}

/// The report as pretty-printed JSON, ending with a newline.
pub fn to_json(r: &Report) -> String {
    let mut s = serde_json::to_string_pretty(r).expect("a report serialises");
    s.push('\n');
    s
}

#[cfg(test)]
mod tests {
    #[test]
    fn axioms_are_classified() {
        assert_eq!(super::classify("propext"), "standard");
        assert_eq!(super::classify("Classical.choice"), "standard");
        assert_eq!(super::classify("Quot.sound"), "standard");
        assert_eq!(super::classify("sorryAx"), "sorry");
        assert_eq!(super::classify("Lean.ofReduceBool"), "non-standard");
        assert_eq!(super::classify("myAxiom"), "non-standard");
    }
}
