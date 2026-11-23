//! Parsing on several threads gives exactly the environment, or exactly the
//! first error, that parsing on one thread gives.

use certus_core::export::{parse_batched, parse_jobs, set_fast_path_for_tests};

fn fixtures() -> Vec<(String, Vec<u8>)> {
    let mut out = Vec::new();
    for dir in ["tests/fixtures", "../certus-kernel/tests/fixtures"] {
        for e in std::fs::read_dir(dir).unwrap() {
            let p = e.unwrap().path();
            if p.extension().is_some_and(|x| x == "ndjson") {
                out.push((p.display().to_string(), std::fs::read(&p).unwrap()));
            }
        }
    }
    out
}

fn outcome(text: &[u8], jobs: usize) -> String {
    show(parse_jobs(text, jobs))
}

fn show(r: Result<certus_core::Env, certus_core::export::ParseError>) -> String {
    match r {
        Ok(env) => {
            // `decl_of_name` is a hash map, whose order differs between runs.
            let mut by_name: Vec<_> = env.decl_of_name.iter().collect();
            by_name.sort();
            format!(
                "{:?} {:?} {:?} {:?} {:?} {:?} {by_name:?} {} {}",
                env.meta, env.names, env.name_canon, env.levels, env.exprs, env.decls, env.bytes, env.lines
            )
        }
        Err(e) => format!("error: {e}"),
    }
}

#[test]
fn every_fixture_parses_the_same_on_any_number_of_threads() {
    for (name, text) in fixtures() {
        let one = outcome(&text, 1);
        for jobs in [2, 3, 8, 64] {
            assert_eq!(one, outcome(&text, jobs), "{name} with {jobs} threads");
        }
    }
}

#[test]
fn the_first_error_is_the_same_on_any_number_of_threads() {
    let (_, text) = fixtures().into_iter().find(|(n, _)| n.ends_with("sum_explicit.cert.ndjson")).unwrap();
    let lines: Vec<&[u8]> = text.split_inclusive(|&c| c == b'\n').collect();
    let n = lines.len();
    // Break the file at several places, in several ways, and twice at once:
    // the earliest problem must be the one reported.
    let breaks: [&[u8]; 5] =
        [b"{not json}\n", b"{\"ie\":999999,\"bvar\":0}\n", b"\xff\xfe\n", b"\n", b"{\"il\":1,\"ie\":2,\"bvar\":0}\n"];
    for (k, bad) in breaks.iter().enumerate() {
        for at in [0, 1, n / 3, n / 2, n - 1] {
            let mut t: Vec<u8> = Vec::new();
            for (i, l) in lines.iter().enumerate() {
                if i == at || (i == n * 2 / 3 && k % 2 == 0) {
                    t.extend_from_slice(bad);
                } else {
                    t.extend_from_slice(l);
                }
            }
            let one = outcome(&t, 1);
            for jobs in [2, 5, 16] {
                assert_eq!(one, outcome(&t, jobs), "break {k} at line {at}, {jobs} threads");
            }
        }
    }
    // A file without a final newline, and an empty file.
    let mut t = text.clone();
    while t.last() == Some(&b'\n') {
        t.pop();
    }
    assert_eq!(outcome(&t, 1), outcome(&t, 4));
    assert_eq!(outcome(b"", 1), outcome(b"", 4));
}

#[test]
fn tiny_batches_split_lines_across_batches_and_give_the_same_result() {
    for (name, text) in fixtures() {
        let one = outcome(&text, 1);
        // 1 byte per thread: every line is longer than a batch, so batches grow.
        for (jobs, batch) in [(1, 1), (3, 7), (4, 64), (2, 300)] {
            assert_eq!(one, show(parse_batched(&text[..], jobs, batch)), "{name}, {jobs} threads, batch {batch}");
        }
    }
}

#[test]
fn the_fast_path_changes_nothing() {
    for (name, text) in fixtures() {
        let fast = outcome(&text, 3);
        set_fast_path_for_tests(false);
        let slow = outcome(&text, 3);
        set_fast_path_for_tests(true);
        assert_eq!(fast, slow, "{name}");
    }
}
