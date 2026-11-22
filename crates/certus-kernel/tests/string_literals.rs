//! String literals (issue #13): they are typed and expanded only once
//! `String`, `String.ofList`, `Char`, `Char.ofNat`, `List.nil` and
//! `List.cons` have their standard shapes, and a theorem's dependency closure
//! includes those constants even when it only mentions a literal.
//! The fixtures come from `fixtures/StringLiterals.lean`.

use certus_core::{deps, parse};

const GOOD: &str = include_str!("fixtures/string_literals.ndjson");
const BAD_CHAR_OF_NAT: &str = include_str!("fixtures/string_literals_bad_char_of_nat.ndjson");
const BAD_OF_LIST: &str = include_str!("fixtures/string_literals_bad_of_list.ndjson");
const BAD_LIST: &str = include_str!("fixtures/string_literals_bad_list.ndjson");

fn check(text: &str, root: &str) -> Result<certus_kernel::Report, certus_kernel::CheckError> {
    let env = parse(text.as_bytes()).expect("export parses");
    let root = env.find_decl(root).expect("root declaration present");
    let closure = deps::closure(&env, &[root]);
    certus_kernel::check(&env, &closure.decls)
}

#[test]
fn accepts_literal_expansion_projection_and_iota() {
    // `lit_eq`: "\x01\x02" ≡ String.ofList [Char.ofNat 1, Char.ofNat 2];
    // `lit_proj`: a projection out of a literal; `lit_rec`: a literal as a
    // recursor's major premise.
    for thm in ["lit_eq", "lit_proj", "lit_rec"] {
        check(GOOD, thm).unwrap_or_else(|e| panic!("{thm} must be accepted: {e}"));
    }
}

#[test]
fn closure_includes_what_literals_depend_on() {
    // `lit_proj` mentions neither `String.ofList` nor `Char.ofNat`, but
    // checking it needs both (lean4export includes them too).
    let env = parse(GOOD.as_bytes()).unwrap();
    let root = env.find_decl("lit_proj").unwrap();
    let names: Vec<String> =
        deps::closure(&env, &[root]).decls.iter().map(|&i| env.name_str(env.decls[i].primary_name())).collect();
    for n in ["Nat", "List", "Char", "Char.ofNat", "String", "String.ofList"] {
        assert!(names.iter().any(|m| m == n), "{n} missing from the closure: {names:?}");
    }
}

#[test]
fn rejects_literals_when_a_constant_has_a_non_standard_shape() {
    for (what, text) in [
        ("Char.ofNat : Nat → Nat", BAD_CHAR_OF_NAT),
        ("String.ofList : List Nat → String", BAD_OF_LIST),
        ("List with constructors cons, nil", BAD_LIST),
    ] {
        match check(text, "lit_trivial") {
            Ok(_) => panic!("string literal ACCEPTED although {what}"),
            Err(e) => {
                assert_eq!(e.decl, "lit_trivial", "{what}: rejected at the wrong declaration: {e}");
                assert!(e.msg.starts_with("string literal, but"), "{what}: rejected for the wrong reason: {e}");
            }
        }
    }
}
