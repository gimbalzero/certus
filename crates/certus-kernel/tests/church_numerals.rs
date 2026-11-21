//! Deep definitional equality (issue #20).
//!
//! `fixtures/church-numerals.ndjson` is the Lean Kernel Arena test
//! `perf/church-numerals` from round 2026-09
//! (`lean-arena-round-2026-09-tests.tar.gz`, file
//! `good/perf/church-numerals.ndjson`, sha256
//! `1234703fc7082cdf99eaf7ecd18fe09f1e11191c9c5b4ffcc5c159c50595927a`), committed
//! unchanged. Its theorem compares two products of Church numerals whose
//! normal forms are thousands of applications deep. Certus used to reject it
//! with "definitional-equality check nested too deeply".

use certus_core::{deps, parse};

const CHURCH: &str = include_str!("fixtures/church-numerals.ndjson");

#[test]
fn accepts_deep_church_numeral_comparison() {
    let env = parse(CHURCH.as_bytes()).expect("export parses");
    let root = env.find_decl("kernel_church_numerals").expect("theorem present");
    let closure = deps::closure(&env, &[root]);
    let r = certus_kernel::check(&env, &closure.decls).expect("valid deep proof must be accepted");
    assert_eq!(r.checked, 4);
}
