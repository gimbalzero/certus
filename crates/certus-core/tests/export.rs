use certus_core::{Env, deps, hash, parse};

const TINY: &str = include_str!("fixtures/tiny.ndjson");

fn env_of(s: &str) -> Env {
    parse(s.as_bytes()).expect("fixture parses")
}

fn err_of(s: &str) -> String {
    parse(s.as_bytes()).expect_err("should be rejected").to_string()
}

fn names(env: &Env, idx: &[usize]) -> Vec<String> {
    let mut v: Vec<String> = idx.iter().map(|&i| env.name_str(env.decls[i].primary_name())).collect();
    v.sort();
    v
}

#[test]
fn parses_fixture() {
    let env = env_of(TINY);
    assert_eq!(env.meta.format.version, "3.1.0");
    assert_eq!(env.names.len(), 6);
    assert_eq!(env.exprs.len(), 4);
    assert_eq!(env.decls.len(), 4);
    assert_eq!(env.name_str(3), "myThm");
    assert_eq!(env.find_decl("myThm"), Some(2));
    assert_eq!(env.find_decl("nope"), None);
}

#[test]
fn duplicate_names_are_canonicalised() {
    let env = env_of(TINY);
    assert_eq!(env.name_canon[5], 1, "second \"P\" record maps to the first");
}

#[test]
fn closure_finds_dependencies_and_axioms() {
    let env = env_of(TINY);
    let thm = env.find_decl("myThm").unwrap();
    let c = deps::closure(&env, &[thm]);
    assert_eq!(names(&env, &c.decls), ["P", "myAx", "myThm"]);
    assert_eq!(names(&env, &c.axioms), ["P", "myAx"]);
    assert!(c.missing.is_empty());
    assert!(c.unsafe_or_partial.is_empty());
}

#[test]
fn closure_follows_duplicate_name_records() {
    // `unused` refers to P through the duplicate name record (id 5).
    let env = env_of(TINY);
    let c = deps::closure(&env, &[env.find_decl("unused").unwrap()]);
    assert_eq!(names(&env, &c.decls), ["P", "unused"]);
}

#[test]
fn hashes_are_deterministic_and_detect_repeats() {
    let env = env_of(TINY);
    let a = hash::hash_env(&env);
    let b = hash::hash_env(&env_of(TINY));
    assert_eq!(a.root, b.root);
    // Expressions 1 and 3 are both `P` (via different name records).
    assert_eq!(a.exprs[1], a.exprs[3]);
    assert_ne!(a.exprs[0], a.exprs[1]);
    assert_eq!(a.names[1], a.names[5]);
}

#[test]
fn hash_changes_when_content_changes() {
    let base = hash::hash_env(&env_of(TINY)).root;
    let renamed = TINY.replace("\"myThm\"", "\"myThm2\"");
    assert_ne!(base, hash::hash_env(&env_of(&renamed)).root);
    let unsafe_ax = TINY.replacen("\"isUnsafe\":false", "\"isUnsafe\":true", 1);
    assert_ne!(base, hash::hash_env(&env_of(&unsafe_ax)).root);
}

#[test]
fn hash_v0_is_pinned() {
    // Changing this value is a breaking change to the certificate spec.
    let root = hash::hex(&hash::hash_env(&env_of(TINY)).root);
    assert_eq!(root, "dedd4861dc32db3cbfb519ce2d1a3aa417993fcf5981a96b92c21b00f0a44587");
}

#[test]
fn flags_unsafe_and_partial() {
    let partial = TINY.replace("\"safety\":\"safe\"", "\"safety\":\"partial\"");
    let env = env_of(&partial);
    let c = deps::closure(&env, &[env.find_decl("unused").unwrap()]);
    assert_eq!(names(&env, &c.unsafe_or_partial), ["unused"]);
}

#[test]
fn rejects_forward_reference() {
    let bad = TINY.replace("{\"ie\":1,\"const\":{\"name\":1,", "{\"ie\":1,\"const\":{\"name\":9,");
    assert!(err_of(&bad).contains("undefined name 9"));
}

#[test]
fn rejects_out_of_order_ids() {
    let bad = TINY.replace("{\"in\":2,", "{\"in\":7,");
    assert!(err_of(&bad).contains("out of sequence"));
}

#[test]
fn rejects_unknown_fields_and_kinds() {
    let bad = TINY.replace("{\"ie\":0,\"sort\":0}", "{\"ie\":0,\"mvar\":0}");
    assert!(err_of(&bad).starts_with("line 7:"));
    let bad = TINY.replace(
        "\"isUnsafe\":false,\"levelParams\":[],\"name\":1",
        "\"isUnsafe\":false,\"extra\":1,\"levelParams\":[],\"name\":1",
    );
    assert!(err_of(&bad).contains("unknown field"));
}

#[test]
fn rejects_duplicate_declarations() {
    let bad = format!("{TINY}{{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":[],\"name\":5,\"type\":0}}}}\n");
    assert!(err_of(&bad).contains("defined twice"));
}

#[test]
fn rejects_missing_or_misplaced_meta() {
    let no_meta: String = TINY.lines().skip(1).map(|l| format!("{l}\n")).collect();
    assert!(err_of(&no_meta).contains("meta"));
}

#[test]
fn rejects_malformed_nat_literal() {
    let bad = TINY.replace("{\"ie\":0,\"sort\":0}", "{\"ie\":0,\"natVal\":\"007\"}");
    assert!(err_of(&bad).contains("natural-number literal"));
}
