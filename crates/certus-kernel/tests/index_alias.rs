//! Inductive types whose type reaches its indices through definitions
//! (issue #29, Mathlib's `CategoryTheory.Presieve.map`).
//!
//! `fixtures/index_alias.cert.ndjson` is the certificate for `image_elim` and
//! `step_elim` from `fixtures/IndexAlias.lean`: lean4export 3.1.0 from Lean
//! 4.36, then `certus extract`. `Image … : Pred β` has one index and
//! `Step : Rel Nat` has two, where `Pred` and `Rel` are definitions that
//! unfold to Pis.

use certus_core::{deps, parse};
use serde_json::Value;

const CERT: &str = include_str!("fixtures/index_alias.cert.ndjson");

fn check(text: &str) -> Result<certus_kernel::Report, certus_kernel::CheckError> {
    let env = parse(text.as_bytes()).expect("export parses");
    let roots: Vec<usize> = ["image_elim", "step_elim"].iter().map(|n| env.find_decl(n).unwrap()).collect();
    let closure = deps::closure(&env, &roots);
    certus_kernel::check(&env, &closure.decls)
}

/// The certificate as JSON records, with the inductive block declaring `ty`.
struct Cert {
    lines: Vec<Value>,
}

impl Cert {
    fn load() -> Self {
        Cert { lines: CERT.lines().map(|l| serde_json::from_str(l).unwrap()).collect() }
    }

    fn name_id(&self, name: &str) -> u64 {
        let r = self.lines.iter().find(|r| r.get("in").is_some() && r["str"]["pre"] == 0 && r["str"]["str"] == name);
        r.unwrap_or_else(|| panic!("name {name} not found"))["in"].as_u64().unwrap()
    }

    fn block(&mut self, ty: &str) -> &mut Value {
        let id = self.name_id(ty);
        self.lines
            .iter_mut()
            .find(|r| r.get("inductive").is_some_and(|b| b["types"][0]["name"] == id))
            .unwrap_or_else(|| panic!("inductive {ty} not found"))
            .get_mut("inductive")
            .unwrap()
    }

    fn text(&self) -> String {
        self.lines.iter().map(|r| format!("{r}\n")).collect()
    }
}

fn rejected(text: &str, why: &str) {
    match check(text) {
        Ok(_) => panic!("tampered certificate was ACCEPTED (expected: {why})"),
        Err(e) => assert!(e.msg.contains(why), "rejected for the wrong reason: {e} (expected: {why})"),
    }
}

#[test]
fn accepts_indices_behind_definitions() {
    let r = check(CERT).expect("genuine certificate must be accepted");
    assert_eq!(r.checked, 37);
}

#[test]
fn rejects_an_index_count_that_ignores_the_definition() {
    // Counting only syntactic binders gives `Image` no indices.
    let mut c = Cert::load();
    let b = c.block("Image");
    assert_eq!(b["types"][0]["numIndices"], 1);
    b["types"][0]["numIndices"] = 0.into();
    rejected(&c.text(), "wrong number of indices");
}

#[test]
fn rejects_a_recursor_with_the_wrong_index_count() {
    let mut c = Cert::load();
    let b = c.block("Step");
    assert_eq!(b["recs"][0]["numIndices"], 2);
    b["recs"][0]["numIndices"] = 1.into();
    rejected(&c.text(), "recursor");
}
