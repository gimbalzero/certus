//! The kernel must accept a genuine certificate and reject every tampered one.
//!
//! The fixture is the certificate for `sum_formula_explicit` (the sum of the
//! first n numbers), made with `certus extract` from Lean 4.36's export: the
//! theorem plus all 82 declarations it depends on, back to `Nat` and `Eq`.

use certus_core::{deps, parse};
use serde_json::Value;

const CERT: &str = include_str!("fixtures/sum_explicit.cert.ndjson");
const THM: &str = "sum_formula_explicit";

fn check(text: &str) -> Result<certus_kernel::Report, String> {
    let env = parse(text.as_bytes()).map_err(|e| e.to_string())?;
    let root = env.find_decl(THM).ok_or("theorem missing")?;
    let closure = deps::closure(&env, &[root]);
    let one = certus_kernel::check(&env, &closure.decls).map_err(|e| e.to_string());
    // Multi-core checking must reach exactly the same verdict.
    for jobs in [2, 3, 8] {
        let many = certus_kernel::check_jobs(&env, &closure.decls, jobs).map_err(|e| e.to_string());
        match (&one, &many) {
            (Ok(a), Ok(b)) => assert_eq!((a.checked, a.native_nat_ops), (b.checked, b.native_nat_ops)),
            (Err(a), Err(b)) => assert_eq!(a, b, "--jobs {jobs} gave a different error"),
            _ => panic!("--jobs {jobs} gave a different verdict: {:?} vs {:?}", one.is_ok(), many.is_ok()),
        }
    }
    one
}

/// The certificate as JSON records, with a way to find declarations by name.
struct Cert {
    lines: Vec<Value>,
}

impl Cert {
    fn load() -> Self {
        Cert { lines: CERT.lines().map(|l| serde_json::from_str(l).unwrap()).collect() }
    }

    fn name(&self, mut id: u64) -> String {
        let mut parts = Vec::new();
        while id != 0 {
            let r = self.lines.iter().find(|r| r.get("in").and_then(Value::as_u64) == Some(id)).unwrap();
            let (part, pre) = if let Some(s) = r.get("str") {
                (s["str"].as_str().unwrap().to_string(), s["pre"].as_u64().unwrap())
            } else {
                (r["num"]["i"].to_string(), r["num"]["pre"].as_u64().unwrap())
            };
            parts.push(part);
            id = pre;
        }
        parts.reverse();
        parts.join(".")
    }

    /// Index of the declaration record of `kind` named `name`.
    fn find(&self, kind: &str, name: &str) -> usize {
        self.lines
            .iter()
            .position(|r| {
                r.get(kind).is_some_and(|d| {
                    let id = d.get("name").or_else(|| d["types"][0].get("name")).unwrap().as_u64().unwrap();
                    self.name(id) == name
                })
            })
            .unwrap_or_else(|| panic!("{kind} {name} not found"))
    }

    fn text(&self) -> String {
        self.lines.iter().map(|r| format!("{r}\n")).collect()
    }
}

fn rejected(text: &str, why: &str) {
    match check(text) {
        Ok(_) => panic!("tampered certificate was ACCEPTED (expected: {why})"),
        Err(e) => assert!(e.contains(why), "rejected for the wrong reason: {e} (expected: {why})"),
    }
}

#[test]
fn accepts_the_genuine_certificate() {
    let r = check(CERT).expect("genuine certificate must be accepted");
    assert_eq!(r.checked, 83);
    assert_eq!(r.native_nat_ops, 2, "Nat.add and Nat.mul are recognised as genuine");
}

#[test]
fn rejects_a_proof_of_something_else() {
    let mut c = Cert::load();
    let (t, other) = (c.find("thm", THM), c.find("thm", "Nat.add_comm"));
    c.lines[t]["thm"]["value"] = c.lines[other]["thm"]["value"].clone();
    rejected(&c.text(), "value does not have the declared type");
}

#[test]
fn rejects_a_changed_statement() {
    let mut c = Cert::load();
    let (t, other) = (c.find("thm", THM), c.find("thm", "Nat.mul_comm"));
    c.lines[t]["thm"]["type"] = c.lines[other]["thm"]["type"].clone();
    rejected(&c.text(), "value does not have the declared type");
}

#[test]
fn rejects_a_missing_dependency() {
    let mut c = Cert::load();
    let nat = c.find("inductive", "Nat");
    c.lines.remove(nat);
    rejected(&c.text(), "unknown constant");
}

#[test]
fn rejects_a_forged_recursor() {
    let mut c = Cert::load();
    let nat = c.find("inductive", "Nat");
    let rules = c.lines[nat]["inductive"]["recs"][0]["rules"].as_array_mut().unwrap();
    let (a, b) = (rules[0]["rhs"].clone(), rules[1]["rhs"].clone());
    rules[0]["rhs"] = b;
    rules[1]["rhs"] = a;
    rejected(&c.text(), "recursor rules do not match");
}

#[test]
fn rejects_data_passed_off_as_a_theorem() {
    let mut c = Cert::load();
    let (t, d) = (c.find("thm", THM), c.find("def", "sumTo"));
    c.lines[t]["thm"]["type"] = c.lines[d]["def"]["type"].clone();
    c.lines[t]["thm"]["value"] = c.lines[d]["def"]["value"].clone();
    rejected(&c.text(), "theorem type is not a proposition");
}

#[test]
fn rejects_unknown_fields() {
    let mut c = Cert::load();
    let t = c.find("thm", THM);
    c.lines[t]["thm"]["trustMe"] = Value::Bool(true);
    rejected(&c.text(), "unknown field");
}

#[test]
fn rejects_unsafe_and_partial_definitions() {
    let mut c = Cert::load();
    let d = c.find("def", "sumTo");
    c.lines[d]["def"]["safety"] = Value::String("partial".into());
    rejected(&c.text(), "partial definitions are not accepted");
}

#[test]
fn native_arithmetic_needs_the_genuine_dependencies() {
    // The fingerprint covers Nat.add's whole dependency closure, not only its
    // own definition: changing a helper it unfolds through (even only its
    // reducibility hint) turns native arithmetic off for Nat.add and for
    // Nat.mul (which uses Nat.add), and the certificate is still accepted.
    let mut c = Cert::load();
    let helper = c.find("def", "Nat.add.match_1");
    c.lines[helper]["def"]["hints"] = serde_json::json!({"regular": 7});
    assert_eq!(check(&c.text()).unwrap().native_nat_ops, 0);
}

#[test]
fn native_arithmetic_ignores_binder_names() {
    // Fingerprints are alpha-normal: renaming every binder keeps native arithmetic.
    let mut c = Cert::load();
    for r in &mut c.lines {
        for k in ["lam", "forallE"] {
            if let Some(b) = r.get_mut(k) {
                b["binderInfo"] = Value::String("default".into());
            }
        }
    }
    assert_eq!(check(&c.text()).unwrap().native_nat_ops, 2);
}

#[test]
fn parallel_checking_reports_the_earliest_failure() {
    // Break two theorems: the verdict names the one earlier in the file,
    // whichever thread finds it, as sequential checking does.
    let mut c = Cert::load();
    let (a, b) = (c.find("thm", "Nat.add_comm"), c.find("thm", THM));
    let other = c.find("thm", "Nat.mul_comm");
    c.lines[a]["thm"]["value"] = c.lines[other]["thm"]["value"].clone();
    c.lines[b]["thm"]["value"] = c.lines[other]["thm"]["value"].clone();
    let text = c.text();
    let env = parse(text.as_bytes()).unwrap();
    let all: Vec<usize> = (0..env.decls.len()).collect();
    let first = certus_kernel::check(&env, &all).unwrap_err().to_string();
    assert!(first.starts_with("Nat.add_comm"), "{first}");
    for jobs in 1..=8 {
        assert_eq!(certus_kernel::check_jobs(&env, &all, jobs).unwrap_err().to_string(), first);
    }
}

#[test]
fn a_declaration_cannot_use_a_later_one() {
    // Threads share one table of all constants; each declaration must still
    // see only those declared before it. Move a theorem that others use
    // (`Nat.add_comm`) to the end: its first user now refers to a later
    // constant.
    let env = parse(CERT.as_bytes()).unwrap();
    let used = env.find_decl("Nat.add_comm").unwrap();
    let mut order: Vec<usize> = (0..env.decls.len()).filter(|&i| i != used).collect();
    order.push(used);
    let first = certus_kernel::check(&env, &order).unwrap_err().to_string();
    assert!(first.contains(": unknown constant"), "{first}");
    for jobs in 2..=8 {
        assert_eq!(certus_kernel::check_jobs(&env, &order, jobs).unwrap_err().to_string(), first);
    }
}

#[test]
fn verdict_cache_rechecks_only_what_changed() {
    use certus_core::{Decl, cache};
    use std::collections::HashSet;
    let checker = [9u8; 32];
    let old = parse(CERT.as_bytes()).unwrap();
    let old_keys: HashSet<_> = cache::keys(&old, &checker).into_iter().flatten().collect();
    assert_eq!(old_keys.len(), old.decls.len(), "every declaration is cacheable");

    // Change one definition in a way that keeps it valid.
    let mut c = Cert::load();
    let d = c.find("def", "sumTo");
    c.lines[d]["def"]["hints"] = serde_json::json!({"regular": 9});
    let text = c.text();
    let new = parse(text.as_bytes()).unwrap();
    let keys = cache::keys(&new, &checker);
    let all: Vec<usize> = (0..new.decls.len()).collect();
    let known: Vec<bool> = keys.iter().map(|k| k.is_some_and(|k| old_keys.contains(&k))).collect();

    // Exactly sumTo and what depends on it get new keys.
    let sum_to = new.find_decl("sumTo").unwrap();
    let changed: Vec<String> =
        all.iter().filter(|&&i| !known[i]).map(|&i| new.name_str(new.decls[i].primary_name())).collect();
    let dependents: Vec<String> = all
        .iter()
        .filter(|&&i| deps::closure(&new, &[i]).decls.contains(&sum_to))
        .map(|&i| new.name_str(new.decls[i].primary_name()))
        .collect();
    assert_eq!(changed, dependents);
    assert!(changed.len() >= 2 && changed.len() < 10, "{changed:?}");

    for jobs in [1, 4] {
        let r = certus_kernel::check_with(&new, &all, jobs, &known).unwrap();
        let cached_kinds =
            all.iter().filter(|&&i| known[i] && !matches!(new.decls[i], Decl::Inductive(_) | Decl::Quot(_)));
        assert_eq!(r.from_cache, cached_kinds.count());
    }
}
