//! The verdict cache as the `certus check` command uses it: an export that
//! this build accepted is not parsed again, and any change to its bytes, or to
//! the declarations asked for, means a full check again.

use std::path::{Path, PathBuf};
use std::process::Command;

const GOOD: &str = "../certus-kernel/tests/fixtures/sum_explicit.cert.ndjson";
const BAD: &str = "../certus-kernel/tests/fixtures/string_literals_bad_list.ndjson";

fn check(file: &Path, cache: &Path, names: &[&str]) -> (i32, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_certus"))
        .arg("check")
        .arg(file)
        .args(names)
        .arg("--cache")
        .arg(cache)
        .output()
        .expect("run certus");
    (out.status.code().unwrap_or(-1), String::from_utf8_lossy(&out.stdout).into_owned())
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("certus-cache-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

const UNCHANGED: &str = "export unchanged since this build accepted it";

#[test]
fn an_accepted_export_is_not_checked_again_until_its_bytes_change() {
    let dir = scratch("bytes");
    let (file, cache) = (dir.join("export.ndjson"), dir.join("cache"));
    std::fs::copy(GOOD, &file).unwrap();

    let (code, out) = check(&file, &cache, &[]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("type-checked in"), "first run checks: {out}");
    let (code, out) = check(&file, &cache, &[]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains(UNCHANGED), "second run is served whole: {out}");

    // Same path, different bytes: the whole-export entry must not apply.
    std::fs::copy(BAD, &file).unwrap();
    let (code, out) = check(&file, &cache, &[]);
    assert_eq!(code, 1, "a changed export is checked again and rejected: {out}");
    assert!(!out.contains("OK"), "{out}");

    // One extra byte: not served whole, but every declaration is still known.
    let mut text = std::fs::read(GOOD).unwrap();
    text.push(b'\n');
    std::fs::write(&file, &text).unwrap();
    let (code, out) = check(&file, &cache, &[]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("all known good"), "{out}");
    let (code, out) = check(&file, &cache, &[]);
    assert!(code == 0 && out.contains(UNCHANGED), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn the_whole_export_entry_is_per_set_of_targets() {
    let dir = scratch("names");
    let (file, cache) = (dir.join("export.ndjson"), dir.join("cache"));
    std::fs::copy(GOOD, &file).unwrap();

    let (code, out) = check(&file, &cache, &["Nat.add_comm"]);
    assert_eq!(code, 0, "{out}");
    assert!(!out.contains(UNCHANGED), "{out}");
    let (code, out) = check(&file, &cache, &["Nat.add_comm", "Nat.add_comm"]);
    assert!(code == 0 && out.contains(UNCHANGED), "the same set of targets: {out}");
    // Everything was never accepted as a whole, so it is not served whole.
    let (code, out) = check(&file, &cache, &[]);
    assert_eq!(code, 0, "{out}");
    assert!(!out.contains(UNCHANGED), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}
