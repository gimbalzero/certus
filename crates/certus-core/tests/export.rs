use certus_core::{Env, deps, hash, parse};

const TINY: &str = include_str!("fixtures/tiny.ndjson");
const ALPHA: &str = include_str!("fixtures/alpha.ndjson");

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
fn hash_alpha_is_pinned() {
    // Changing these values is a breaking change to spec v1 (alpha-normal mode).
    let tiny = hash::hex(&hash::hash_env_alpha(&env_of(TINY)).root);
    assert_eq!(tiny, "3b4e75815a2e0ab06cd7b9733d8b6a2896501c6a041c1822b34733dabb5e8550");
    let alpha = hash::hex(&hash::hash_env_alpha(&env_of(ALPHA)).root);
    assert_eq!(alpha, "68baf0795614185d7d75a6e5f71cf2fd8174a56810a48558e9bcaca296f0b77a");
}

#[test]
fn alpha_mode_uses_its_own_key() {
    // TINY has no binders, so only the key differs between the two modes.
    let env = env_of(TINY);
    let (v0, v1) = (hash::hash_env(&env), hash::hash_env_alpha(&env));
    assert_ne!(v0.root, v1.root);
    assert_ne!(v0.exprs[0], v1.exprs[0]);
    assert_eq!(hash::hash_env_with(&env, hash::Mode::Faithful).root, v0.root);
}

#[test]
fn alpha_equivalent_terms_collide_only_in_alpha_mode() {
    let env = env_of(ALPHA);
    let v0 = hash::hash_env(&env);
    let v1 = hash::hash_env_alpha(&env);
    // Pairs that differ only in binder name and binder info (or `nondep`).
    for (a, b) in [(3, 4), (5, 6), (7, 8)] {
        assert_ne!(v0.exprs[a], v0.exprs[b], "v0 must tell exprs {a} and {b} apart");
        assert_eq!(v1.exprs[a], v1.exprs[b], "alpha mode must identify exprs {a} and {b}");
    }
    // Different structure still differs: `forall x : Prop, x` vs `forall x : Prop, P`,
    // and pi vs lambda vs let over the same parts.
    assert_ne!(v1.exprs[3], v1.exprs[9]);
    assert_ne!(v1.exprs[3], v1.exprs[5]);
    assert_ne!(v1.exprs[5], v1.exprs[7]);
    // Declaration names are still hashed, so ax1 and ax2 remain distinct.
    assert_ne!(v1.decls[1], v1.decls[2]);
}

#[test]
fn renaming_a_binder_changes_only_the_v0_root() {
    let base = env_of(ALPHA);
    let renamed = env_of(&ALPHA.replace("\"str\":\"x\"", "\"str\":\"z\""));
    assert_ne!(hash::hash_env(&base).root, hash::hash_env(&renamed).root);
    assert_eq!(hash::hash_env_alpha(&base).root, hash::hash_env_alpha(&renamed).root);
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

const META: &str = r#"{"meta":{"exporter":{"name":"handcrafted","version":"0.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0000000000000000000000000000000000000000","version":"4.29.1"}}}"#;

fn with_meta(lines: &[&str]) -> String {
    let mut s = format!("{META}\n");
    for l in lines {
        s.push_str(l);
        s.push('\n');
    }
    s
}

#[test]
fn accepts_sparse_ids() {
    // Arena `other/sparse-name-index`.
    let env = env_of(&with_meta(&[
        r#"{"in":2,"str":{"pre":0,"str":"foo"}}"#,
        r#"{"ie":4,"sort":0}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":4}}"#,
    ]));
    assert_eq!(env.find_decl("foo"), Some(0));
    assert_eq!(env.names.len(), 2);
    assert_eq!(env.exprs.len(), 1);
    // Declarations refer to the internal (dense) ids.
    assert_eq!(env.decls[0].roots(), [0]);
}

#[test]
fn accepts_out_of_order_ids() {
    // Arena `other/level-index-out-of-order`: level 1 = succ (level 2) = succ (succ zero).
    let env = env_of(&with_meta(&[
        r#"{"in":1,"str":{"pre":0,"str":"foo"}}"#,
        r#"{"il":2,"succ":0}"#,
        r#"{"il":1,"succ":2}"#,
        r#"{"ie":0,"sort":1}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}"#,
    ]));
    use certus_core::export::{Expr, Level};
    let Expr::Sort(l) = env.exprs[0] else { panic!("expected a sort") };
    let Level::Succ(inner) = env.levels[l as usize] else { panic!("expected succ") };
    assert_eq!(env.levels[inner as usize], Level::Succ(0));
    // Reordering the ids of an ordinary export changes nothing but the ids.
    let shuffled = TINY.replace("{\"in\":2,", "{\"in\":7,").replace("\"name\":2,", "\"name\":7,");
    assert_eq!(hash::hash_env(&env_of(&shuffled)).root, hash::hash_env(&env_of(TINY)).root);
}

#[test]
fn rejects_ids_never_defined() {
    let bad = TINY.replace("{\"in\":2,", "{\"in\":7,");
    assert!(err_of(&bad).contains("undefined name 2"));
    let bad = with_meta(&[r#"{"il":1,"succ":2}"#, r#"{"il":2,"succ":0}"#]);
    assert!(err_of(&bad).contains("undefined level 2"));
    let bad = with_meta(&[r#"{"ie":3,"app":{"fn":5,"arg":5}}"#, r#"{"ie":5,"sort":0}"#]);
    assert!(err_of(&bad).contains("undefined expression 5"));
}

#[test]
fn rejects_self_reference() {
    // A record may not refer to its own id, so no cycle can be built.
    assert!(err_of(&with_meta(&[r#"{"in":3,"str":{"pre":3,"str":"x"}}"#])).contains("undefined name 3"));
    assert!(err_of(&with_meta(&[r#"{"il":4,"succ":4}"#])).contains("undefined level 4"));
    assert!(err_of(&with_meta(&[r#"{"ie":9,"app":{"fn":9,"arg":9}}"#])).contains("undefined expression 9"));
}

#[test]
fn rejects_duplicate_ids() {
    for lines in [
        [r#"{"in":3,"str":{"pre":0,"str":"x"}}"#, r#"{"in":3,"str":{"pre":0,"str":"y"}}"#],
        [r#"{"in":0,"str":{"pre":0,"str":"x"}}"#, r#"{"in":1,"str":{"pre":0,"str":"y"}}"#],
        [r#"{"il":5,"succ":0}"#, r#"{"il":5,"succ":0}"#],
        [r#"{"il":1,"succ":0}"#, r#"{"il":0,"succ":0}"#],
        [r#"{"ie":7,"sort":0}"#, r#"{"ie":7,"sort":0}"#],
        [r#"{"ie":0,"sort":0}"#, r#"{"ie":0,"sort":0}"#],
    ] {
        assert!(err_of(&with_meta(&lines)).contains("defined twice"), "{lines:?}");
    }
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

/// Real lean4export 3.1.0 output (Lean 4.36) for
/// `theorem alphaT1 : ∀ (a : Nat), a = a := fun a => rfl` and
/// `theorem alphaT2 : ∀ {b : Nat}, b = b := fun {b} => rfl`, exported in both orders.
/// lean4export shares terms up to alpha *and binder info*, so whichever theorem is
/// exported first decides the binder name and info both theorems carry.
const ORDER_12: &str = include_str!("fixtures/alpha_order_12.ndjson");
const ORDER_21: &str = include_str!("fixtures/alpha_order_21.ndjson");

#[test]
fn alpha_hash_does_not_depend_on_export_order() {
    let decl_hash = |src: &str, name: &str, alpha: bool| {
        let env = env_of(src);
        let h = if alpha { hash::hash_env_alpha(&env) } else { hash::hash_env(&env) };
        h.decls[env.find_decl(name).unwrap()]
    };
    for name in ["alphaT1", "alphaT2"] {
        assert_ne!(decl_hash(ORDER_12, name, false), decl_hash(ORDER_21, name, false), "{name} v0");
        assert_eq!(decl_hash(ORDER_12, name, true), decl_hash(ORDER_21, name, true), "{name} alpha");
    }
}

#[test]
fn lazy_hashes_match_full_hashes() {
    for src in [TINY, ALPHA, ORDER_12] {
        let env = env_of(src);
        for mode in [hash::Mode::Faithful, hash::Mode::AlphaNormal] {
            let full = hash::hash_env_with(&env, mode);
            let mut lazy = hash::LazyHashes::new(&env, mode);
            for i in (0..env.decls.len()).rev() {
                assert_eq!(lazy.decl(i), full.decls[i]);
            }
        }
    }
}

mod verdict_cache {
    use super::*;
    use certus_core::cache;

    const CHECKER: [u8; 32] = [7; 32];

    fn keys(src: &str) -> (Env, Vec<Option<hash::Hash>>) {
        let env = env_of(src);
        let k = cache::keys(&env, &CHECKER);
        (env, k)
    }

    fn key(src: &str, name: &str) -> Option<hash::Hash> {
        let (env, k) = keys(src);
        k[env.find_decl(name).unwrap()]
    }

    #[test]
    fn changing_a_declaration_changes_exactly_it_and_its_dependents() {
        // TINY: P; myAx : P; myThm : P := myAx; unused := P.
        // Changing myAx's unsafe flag changes myAx and myThm, not P or unused.
        let changed = TINY.replacen(
            "\"isUnsafe\":false,\"levelParams\":[],\"name\":2",
            "\"isUnsafe\":true,\"levelParams\":[],\"name\":2",
            1,
        );
        assert_ne!(changed, TINY);
        for (name, same) in [("P", true), ("unused", true), ("myAx", false), ("myThm", false)] {
            assert_eq!(key(TINY, name) == key(&changed, name), same, "{name}");
        }
        assert!(keys(TINY).1.iter().all(Option::is_some));
    }

    #[test]
    fn keys_ignore_binder_names_and_export_order() {
        let renamed = ALPHA.replace("\"str\":\"x\"", "\"str\":\"z\"");
        assert_eq!(key(ALPHA, "ax1"), key(&renamed, "ax1"));
        for name in ["alphaT1", "alphaT2"] {
            assert_eq!(key(ORDER_12, name), key(ORDER_21, name), "{name}");
        }
    }

    #[test]
    fn keys_depend_on_the_checker() {
        let env = env_of(TINY);
        assert_ne!(cache::keys(&env, &[1; 32]), cache::keys(&env, &[2; 32]));
    }

    #[test]
    fn a_reference_to_a_later_declaration_has_no_key() {
        // Move P's axiom to the end: myAx now refers forward, so neither it
        // nor myThm (which depends on it) can be cached.
        let mut lines: Vec<&str> = TINY.lines().collect();
        let p = lines.iter().position(|l| l.starts_with("{\"axiom\"") && l.contains("\"name\":1,")).unwrap();
        let ax = lines.remove(p);
        lines.push(ax);
        let moved: String = lines.iter().map(|l| format!("{l}\n")).collect();
        assert_eq!(key(&moved, "myAx"), None);
        assert_eq!(key(&moved, "myThm"), None);
        assert!(key(&moved, "P").is_some());
    }

    #[test]
    fn string_literals_depend_on_the_expansion_function_only() {
        // In Lean 4.36 `String.mk` is a deprecated alias declared after the
        // first string literals; only `String.ofList` is an implicit dependency.
        let src = include_str!("../../certus-kernel/tests/fixtures/string_literals.ndjson");
        let (env, k) = keys(src);
        for (i, key) in k.iter().enumerate() {
            assert!(key.is_some(), "{} has no key", env.name_str(env.decls[i].primary_name()));
        }
    }

    #[test]
    fn entries_are_checked() {
        let k = [42u8; 32];
        let e = cache::entry(&k);
        assert_eq!(cache::parse_entry(&e), Some(k));
        let mut bad = e.clone();
        bad.replace_range(0..1, if e.starts_with('0') { "1" } else { "0" });
        assert_eq!(cache::parse_entry(&bad), None, "changed key");
        assert_eq!(cache::parse_entry(&e[..e.len() - 1]), None, "truncated");
        assert_eq!(cache::parse_entry("garbage"), None);
    }
}
