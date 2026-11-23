//! Native `Nat` arithmetic on open terms with huge arguments. The fixture is
//! the Lean Kernel Arena's `good/bugs/nat-shift-huge` test (Lean 4.36): it
//! proves `n >>> 2^64 = 0` and `0 <<< 2^64 = 0`, both for literals and for
//! `const42 x` / `const0 x`, where `x` is a local variable. Unfolding the
//! shifts would take 2^64 steps, so these need the native operations, also
//! when the arguments only reduce to literals inside an open term.

use certus_core::{deps, parse};

const TEXT: &str = include_str!("fixtures/nat_shift_huge.ndjson");

#[test]
fn huge_shifts_of_literals_and_of_open_terms_that_reduce_to_literals() {
    let env = parse(TEXT.as_bytes()).expect("export parses");
    for thm in ["natShiftRightHuge", "natShiftLeftZeroHuge", "natShiftRightHugeOpen", "natShiftLeftZeroHugeOpen"] {
        let root = env.find_decl(thm).expect("theorem present");
        let closure = deps::closure(&env, &[root]);
        let r = certus_kernel::check(&env, &closure.decls).unwrap_or_else(|e| panic!("{thm} must be accepted: {e}"));
        assert!(r.native_nat_ops > 0, "{thm}: the genuine Nat operations are recognised");
    }
}
