//! Nested inductive types: the kernel must accept genuine ones and reject
//! tampered auxiliary recursors (`T.rec_1`, `T.rec_2`, ...).
//!
//! The fixture is a certificate made with `certus extract` from Lean 4.36's
//! export of `fixtures/Nested.lean`: nesting through `List`, `Array (List _)`,
//! `Option`, `Prod`, an indexed type and a mutual block, a mutual block with
//! nested occurrences, and two theorems proved by computation through the
//! auxiliary recursors.

use certus_core::{deps, parse};
use serde_json::Value;

const CERT: &str = include_str!("fixtures/nested.cert.ndjson");

fn check(text: &str) -> Result<certus_kernel::Report, String> {
    let env = parse(text.as_bytes()).map_err(|e| e.to_string())?;
    let all: Vec<usize> = (0..env.decls.len()).collect();
    let closure = deps::closure(&env, &all);
    certus_kernel::check(&env, &closure.decls).map_err(|e| e.to_string())
}

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

    /// The inductive block whose first type is `ty`.
    fn block(&self, ty: &str) -> usize {
        self.lines
            .iter()
            .position(|r| r.get("inductive").is_some_and(|d| self.name(d["types"][0]["name"].as_u64().unwrap()) == ty))
            .unwrap_or_else(|| panic!("inductive {ty} not found"))
    }

    /// Index of the recursor called `rec` in block `b`.
    fn rec(&self, b: usize, rec: &str) -> usize {
        let recs = self.lines[b]["inductive"]["recs"].as_array().unwrap();
        recs.iter()
            .position(|r| self.name(r["name"].as_u64().unwrap()) == rec)
            .unwrap_or_else(|| panic!("recursor {rec} not found"))
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
fn accepts_genuine_nested_inductives() {
    let r = check(CERT).expect("genuine certificate must be accepted");
    assert_eq!(r.checked, 109);
}

#[test]
fn nested_blocks_have_auxiliary_recursors() {
    let c = Cert::load();
    for (ty, n) in [("Tree", 1), ("Rose", 4), ("Term", 2), ("A", 3), ("VTree", 1), ("UsesEv", 2)] {
        let b = c.block(ty);
        let types = c.lines[b]["inductive"]["types"].as_array().unwrap();
        assert_eq!(types[0]["numNested"].as_u64(), Some(n), "{ty}");
        for i in 1..=n {
            c.rec(b, &format!("{ty}.rec_{i}"));
        }
    }
}

#[test]
fn rejects_a_forged_rec_1_rule() {
    // `Tree.rec_1` is the recursor for the auxiliary copy of `List (Tree α)`:
    // swap the right-hand sides of its `List.nil` and `List.cons` rules.
    let mut c = Cert::load();
    let b = c.block("Tree");
    let r = c.rec(b, "Tree.rec_1");
    let rules = c.lines[b]["inductive"]["recs"][r]["rules"].as_array_mut().unwrap();
    assert_eq!(rules.len(), 2);
    let (x, y) = (rules[0]["rhs"].clone(), rules[1]["rhs"].clone());
    rules[0]["rhs"] = y;
    rules[1]["rhs"] = x;
    rejected(&c.text(), "recursor rules do not match");
}

#[test]
fn rejects_a_rec_1_rule_for_the_wrong_constructor() {
    let mut c = Cert::load();
    let b = c.block("Tree");
    let r = c.rec(b, "Tree.rec_1");
    let rules = c.lines[b]["inductive"]["recs"][r]["rules"].as_array_mut().unwrap();
    rules[1]["ctor"] = rules[0]["ctor"].clone();
    rejected(&c.text(), "recursor rules do not match");
}

#[test]
fn rejects_swapped_auxiliary_recursors() {
    // `Rose.rec_1` (for `Array (List Rose)`) and `Rose.rec_2` (for `Option Rose`)
    // must come in Lean's order.
    let mut c = Cert::load();
    let b = c.block("Rose");
    let (r1, r2) = (c.rec(b, "Rose.rec_1"), c.rec(b, "Rose.rec_2"));
    let recs = c.lines[b]["inductive"]["recs"].as_array_mut().unwrap();
    let (n1, n2) = (recs[r1]["name"].clone(), recs[r2]["name"].clone());
    recs[r1]["name"] = n2;
    recs[r2]["name"] = n1;
    rejected(&c.text(), "recursor type does not match");
}

#[test]
fn rejects_a_missing_auxiliary_recursor() {
    let mut c = Cert::load();
    let b = c.block("Rose");
    let r = c.rec(b, "Rose.rec_4");
    c.lines[b]["inductive"]["recs"].as_array_mut().unwrap().remove(r);
    rejected(&c.text(), "expected one recursor per inductive type");
}

#[test]
fn rejects_wrong_nested_metadata() {
    let mut c = Cert::load();
    let b = c.block("Tree");
    c.lines[b]["inductive"]["types"][0]["numNested"] = Value::from(2);
    rejected(&c.text(), "numNested");
}
