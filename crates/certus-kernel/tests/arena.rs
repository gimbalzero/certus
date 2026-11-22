//! Regression tests from the Lean Kernel Arena.
//!
//! `fixtures/proj-of-subst-prop.ndjson` is the Arena test `bugs/proj-of-subst-prop`
//! from round 2026-09 (`lean-arena-round-2026-09-tests.tar.gz`, file
//! `bad/bugs/proj-of-subst-prop.ndjson`, sha256
//! `1c9d8a266c198b7d4a1cfbe3fffd2de2d2b75e603fb3cedfa5d5309f7b295b9d`), committed
//! unchanged. It proves `False` with no axioms by projecting a `Bool` out of a
//! proposition whose sort is a stuck term (issue #17, leanprover/lean4#14807).

use certus_core::{deps, parse};

const PROJ_OF_SUBST_PROP: &str = include_str!("fixtures/proj-of-subst-prop.ndjson");

fn check(text: &str, root: &str) -> Result<certus_kernel::Report, certus_kernel::CheckError> {
    let env = parse(text.as_bytes()).expect("export parses");
    let root = env.find_decl(root).expect("root declaration present");
    let closure = deps::closure(&env, &[root]);
    certus_kernel::check(&env, &closure.decls)
}

#[test]
fn rejects_projection_out_of_a_prop_with_a_stuck_sort() {
    match check(PROJ_OF_SUBST_PROP, "inconsistent") {
        Ok(r) => panic!("proof of False was ACCEPTED ({} declarations)", r.checked),
        Err(e) => {
            // `observe := fun p : proposition => p.1` is the first bad declaration:
            // `proposition` unfolds to `Owner witness`, whose sort is stuck.
            assert_eq!(e.decl, "PR14806Subst.observe", "rejected at the wrong declaration: {e}");
            assert_eq!(e.msg, "type expected", "rejected for the wrong reason: {e}");
        }
    }
}
