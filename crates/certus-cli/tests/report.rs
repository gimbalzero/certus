//! `certus check --report`: what it records, and that it is reproducible.

use std::path::{Path, PathBuf};
use std::process::Command;

const GOOD: &str = "../certus-kernel/tests/fixtures/sum_explicit.cert.ndjson";
const BAD: &str = "../certus-kernel/tests/fixtures/string_literals_bad_list.ndjson";

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("certus-report-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn report(file: &str, names: &[&str], extra: &[&str], out: &Path) -> (i32, serde_json::Value, String) {
    let st = Command::new(env!("CARGO_BIN_EXE_certus"))
        .arg("check")
        .arg(file)
        .args(names)
        .args(["--no-cache", "--report"])
        .arg(out)
        .args(extra)
        .output()
        .expect("run certus");
    let text = std::fs::read_to_string(out).expect("a report is written whatever the verdict");
    (st.status.code().unwrap_or(-1), serde_json::from_str(&text).expect("the report is JSON"), text)
}

#[test]
fn an_accepted_check_reports_statements_and_axioms() {
    let d = scratch("ok");
    let (code, r, _) = report(GOOD, &["sum_formula_explicit", "Nat.add_comm"], &[], &d.join("r.json"));
    assert_eq!(code, 0);
    assert_eq!(r["format"], "certus-report-v1");
    assert_eq!(r["verdict"], "accepted");
    assert_eq!(r["declarations"], 83);
    assert_eq!(r["export"]["lean_version"], "4.36.0");
    let t = &r["targets"][0];
    assert_eq!(t["name"], "sum_formula_explicit");
    assert_eq!(t["statement"], "∀ (n : Nat), 2 * sumTo n = n * (n + 1)");
    assert_eq!(t["axioms"], serde_json::json!([{"name": "propext", "class": "standard"}]));
    assert_eq!(r["targets"][1]["name"], "Nat.add_comm");
    assert_eq!(r["targets"][1]["axioms"], serde_json::json!([]));
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn the_report_is_the_same_byte_for_byte_on_any_number_of_threads() {
    let d = scratch("same");
    let names = ["sum_formula_explicit"];
    let (_, _, one) = report(GOOD, &names, &["--jobs", "1"], &d.join("1.json"));
    let (_, _, many) = report(GOOD, &names, &["--jobs", "5"], &d.join("5.json"));
    let (_, _, again) = report(GOOD, &names, &["--jobs", "1"], &d.join("1b.json"));
    assert_eq!(one, many);
    assert_eq!(one, again);
    let _ = std::fs::remove_dir_all(&d);
}

#[test]
fn a_rejected_check_reports_why() {
    let d = scratch("bad");
    let (code, r, _) = report(BAD, &[], &[], &d.join("r.json"));
    assert_eq!(code, 1);
    assert_eq!(r["verdict"], "rejected");
    assert!(r["message"].as_str().unwrap().contains("string literal"), "{r}");
    let _ = std::fs::remove_dir_all(&d);
}
