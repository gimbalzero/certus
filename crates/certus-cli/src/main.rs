//! `certus`: inspect Lean 4 kernel exports produced by `lean4export`.

use certus_core::{Decl, Env, deps, hash, parse, pretty, report};
use std::collections::{BTreeMap, HashSet};
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::process::ExitCode;
use std::time::Instant;

const USAGE: &str = "\
certus 0.0.1: fast, verifiable proof checking for Lean (Phase 0)

USAGE:
    certus stats <export.ndjson>
        Parse the export, then report counts, throughput and how much
        content is repeated.
    certus hash  <export.ndjson> [--manifest <out.tsv>]
        Content-hash every declaration (spec v0) and print the root hash.
        With --manifest, write one line per declaration: hash, kind, name.
    certus deps  <export.ndjson> <Decl.Name> [--list]
        Everything <Decl.Name> depends on, and the axioms it rests on.
        With --list, print every declaration in the closure.
    certus show  <export.ndjson> <Decl.Name> [--raw]
        Print the kind, name, universe parameters and exact statement (type)
        of a constant. --raw shows every argument, instance and universe level
        instead of notation such as `a + b`.

    certus check <export.ndjson> [<Decl.Name>...] [--jobs N]
        Type-check declarations with the Certus kernel. With names, check
        exactly what those declarations depend on; without, check everything.
        --jobs N: use N threads (default: all cores); the verdict is the same
        for every N.
        Accepted declarations are remembered in a verdict cache, keyed on
        their content and everything they depend on, so an unchanged
        declaration is not checked again, and an export accepted before, byte
        for byte, is not even parsed again (see docs/CACHE.md).
        --cache DIR: keep the cache in DIR (default: $XDG_CACHE_HOME/certus
        or ~/.cache/certus); --no-cache: neither read nor write it.
        --report FILE: write an audit report (JSON): the checker build, the
        export's hash, the verdict, and for each named declaration its exact
        statement, a hash of it, and the axioms and unsafe or partial
        declarations it rests on. The same build checking the same export
        writes the same report, byte for byte (docs/AUDIT.md).
        Exit code 0: all accepted; 1: REJECTED (invalid) or other error;
        2: DECLINED (ran out of work budget or stack before a verdict).
    certus extract <export.ndjson> <out.ndjson> <Decl.Name>...
        Write a minimal certificate: the named declarations plus everything
        they depend on, as a standalone export file.

Exports come from lean4export (format 3.x).";

use certus_core::report::STANDARD_AXIOMS;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("stats") if args.len() == 2 => stats(&args[1]),
        Some("hash") if args.len() == 2 => hash_cmd(&args[1], None),
        Some("hash") if args.len() == 4 && args[2] == "--manifest" => hash_cmd(&args[1], Some(&args[3])),
        Some("deps") if args.len() == 3 => deps_cmd(&args[1], &args[2], false),
        Some("deps") if args.len() == 4 && args[3] == "--list" => deps_cmd(&args[1], &args[2], true),
        Some("show") if args.len() == 3 => show_cmd(&args[1], &args[2], false),
        Some("show") if args.len() == 4 && args[3] == "--raw" => show_cmd(&args[1], &args[2], true),
        Some("check") if args.len() >= 2 => {
            return match with_big_stack(move || check_cmd(&args[1], &args[2..])) {
                Ok(Ok(())) => ExitCode::SUCCESS,
                Ok(Err(declined)) => {
                    eprintln!("error: {declined}");
                    ExitCode::from(2)
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    ExitCode::FAILURE
                }
            };
        }
        Some("extract") if args.len() >= 4 => extract_cmd(&args[1], &args[2], &args[3..]),
        Some("-h" | "--help" | "help") => {
            println!("{USAGE}");
            Ok(())
        }
        _ => Err(USAGE.to_string()),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn load(path: &str) -> Result<Env, String> {
    let t = Instant::now();
    let f = File::open(path).map_err(|e| format!("{path}: {e}"))?;
    let env = parse(BufReader::with_capacity(1 << 20, f)).map_err(|e| format!("{path}: {e}"))?;
    let secs = t.elapsed().as_secs_f64();
    eprintln!(
        "parsed {} lines ({:.1} MB) in {:.2} s: {:.0} MB/s, {:.2}M records/s",
        env.lines,
        env.bytes as f64 / 1e6,
        secs,
        env.bytes as f64 / 1e6 / secs,
        env.lines as f64 / 1e6 / secs
    );
    Ok(env)
}

/// Like `load`, and also the BLAKE3 hash of exactly the bytes that were
/// parsed (hashed as they are read, so a file that changes meanwhile cannot
/// pair one content's hash with another's verdict).
fn load_hashed(path: &str) -> Result<(Env, hash::Hash), String> {
    let t = Instant::now();
    let f = File::open(path).map_err(|e| format!("{path}: {e}"))?;
    // The bytes are hashed on their own thread, as they are read.
    let (tx, rx) = std::sync::mpsc::sync_channel::<Vec<u8>>(64);
    let hasher = std::thread::spawn(move || {
        let mut h = blake3::Hasher::new();
        for chunk in rx {
            h.update(&chunk);
        }
        *h.finalize().as_bytes()
    });
    let mut r = BufReader::with_capacity(1 << 20, Tee { inner: f, tx });
    let env = parse(&mut r).map_err(|e| format!("{path}: {e}"));
    // Hash whatever the parser did not need to read, too.
    let rest = std::io::copy(&mut r, &mut std::io::sink()).map_err(|e| format!("{path}: {e}"));
    drop(r);
    let bytes = hasher.join().map_err(|_| "the hashing thread panicked".to_string())?;
    let (env, _) = (env?, rest?);
    let secs = t.elapsed().as_secs_f64();
    eprintln!(
        "parsed {} lines ({:.1} MB) in {:.2} s: {:.0} MB/s, {:.2}M records/s",
        env.lines,
        env.bytes as f64 / 1e6,
        secs,
        env.bytes as f64 / 1e6 / secs,
        env.lines as f64 / 1e6 / secs
    );
    Ok((env, bytes))
}

/// A reader that sends a copy of everything read through it to a hasher.
struct Tee<R> {
    inner: R,
    tx: std::sync::mpsc::SyncSender<Vec<u8>>,
}

impl<R: Read> Read for Tee<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = self.inner.read(buf)?;
        if n > 0 {
            self.tx.send(buf[..n].to_vec()).map_err(|_| std::io::Error::other("the hashing thread stopped"))?;
        }
        Ok(n)
    }
}

/// BLAKE3 hash of a file's bytes.
fn hash_file(path: &str) -> std::io::Result<hash::Hash> {
    let mut h = blake3::Hasher::new();
    h.update_reader(File::open(path)?)?;
    Ok(*h.finalize().as_bytes())
}

fn timed_hash(env: &Env) -> hash::Hashes {
    let t = Instant::now();
    let h = hash::hash_env(env);
    let secs = t.elapsed().as_secs_f64();
    let nodes = env.names.len() + env.levels.len() + env.exprs.len() + env.decls.len();
    eprintln!("hashed {nodes} nodes in {secs:.2} s: {:.2}M nodes/s", nodes as f64 / 1e6 / secs);
    h
}

fn stats(path: &str) -> Result<(), String> {
    let env = load(path)?;
    let m = &env.meta;
    println!(
        "export      {} {} (format {}), Lean {}",
        m.exporter.name, m.exporter.version, m.format.version, m.lean.version
    );
    println!("names       {}", env.names.len());
    println!("levels      {}", env.levels.len());
    println!("expressions {}", env.exprs.len());

    let mut by_kind: BTreeMap<&str, usize> = BTreeMap::new();
    for d in &env.decls {
        *by_kind.entry(d.kind()).or_default() += 1;
    }
    let kinds: Vec<String> = by_kind.iter().map(|(k, n)| format!("{n} {k}")).collect();
    println!("decls       {} ({})", env.decls.len(), kinds.join(", "));
    println!("constants   {}", env.decl_of_name.len());

    let h = timed_hash(&env);
    let unique: HashSet<&hash::Hash> = h.exprs.iter().collect();
    println!(
        "unique expressions by content: {} of {} ({:.2}% are repeats the exporter did not share)",
        unique.len(),
        h.exprs.len(),
        100.0 * (1.0 - unique.len() as f64 / h.exprs.len().max(1) as f64)
    );
    let alpha = hash::hash_env_alpha(&env);
    let unique_alpha: HashSet<&hash::Hash> = alpha.exprs.iter().collect();
    println!(
        "unique expressions up to alpha (spec v1 draft): {} of {} ({:.2}% fewer than by exact content)",
        unique_alpha.len(),
        h.exprs.len(),
        100.0 * (1.0 - unique_alpha.len() as f64 / unique.len().max(1) as f64)
    );
    let dup_names = env.name_canon.iter().enumerate().filter(|(i, c)| *i as u32 != **c).count();
    println!("duplicate name records: {dup_names}");
    println!("root {}", hash::hex(&h.root));
    Ok(())
}

fn hash_cmd(path: &str, manifest: Option<&str>) -> Result<(), String> {
    let env = load(path)?;
    let h = timed_hash(&env);
    if let Some(out) = manifest {
        let f = File::create(out).map_err(|e| format!("{out}: {e}"))?;
        let mut w = BufWriter::new(f);
        for (d, dh) in env.decls.iter().zip(&h.decls) {
            writeln!(w, "{}\t{}\t{}", hash::hex(dh), d.kind(), env.name_str(d.primary_name()))
                .map_err(|e| format!("{out}: {e}"))?;
        }
        w.flush().map_err(|e| format!("{out}: {e}"))?;
        eprintln!("wrote {} declarations to {out}", env.decls.len());
    }
    println!("{}", hash::hex(&h.root));
    Ok(())
}

fn deps_cmd(path: &str, name: &str, list: bool) -> Result<(), String> {
    let env = load(path)?;
    let idx = env.find_decl(name).ok_or_else(|| format!("no declaration named {name} in {path}"))?;
    let t = Instant::now();
    let c = deps::closure(&env, &[idx]);
    let secs = t.elapsed().as_secs_f64();

    let d = &env.decls[idx];
    println!("{} {}", d.kind(), env.name_str(d.primary_name()));
    if let Some(c) = pretty::const_info(&env, d.primary_name()) {
        println!("statement: {}", pretty::statement(&env, &c, pretty::Options::NOTATION));
    }
    println!(
        "depends on {} of {} declarations ({:.1}%) and {} of {} expression nodes ({:.1}%); computed in {:.3} s",
        c.decls.len(),
        env.decls.len(),
        100.0 * c.decls.len() as f64 / env.decls.len() as f64,
        c.exprs_visited,
        env.exprs.len(),
        100.0 * c.exprs_visited as f64 / env.exprs.len().max(1) as f64,
        secs
    );
    println!("axioms:");
    if c.axioms.is_empty() {
        println!("  (none)");
    }
    for &a in &c.axioms {
        let n = env.name_str(env.decls[a].primary_name());
        let note = if STANDARD_AXIOMS.contains(&n.as_str()) {
            "standard"
        } else if n == "sorryAx" {
            "SORRY: the proof is incomplete"
        } else {
            "NON-STANDARD: review this"
        };
        println!("  {n}  ({note})");
    }
    if !c.unsafe_or_partial.is_empty() {
        println!("unsafe or partial declarations in the closure: {}", c.unsafe_or_partial.len());
        for &u in c.unsafe_or_partial.iter().take(20) {
            println!("  {} {}", env.decls[u].kind(), env.name_str(env.decls[u].primary_name()));
        }
    }
    if !c.missing.is_empty() {
        println!("WARNING: {} referenced constants are not defined in this export:", c.missing.len());
        for &n in c.missing.iter().take(20) {
            println!("  {}", env.name_str(n));
        }
    }
    if list {
        for &i in &c.decls {
            println!("{}\t{}", env.decls[i].kind(), env.name_str(env.decls[i].primary_name()));
        }
    }
    Ok(())
}

fn show_cmd(path: &str, name: &str, raw: bool) -> Result<(), String> {
    let env = load(path)?;
    let c = pretty::find_const(&env, name).ok_or_else(|| format!("no declaration named {name} in {path}"))?;
    let opts = if raw { pretty::Options::RAW } else { pretty::Options::NOTATION };
    let params: Vec<String> = c.level_params.iter().map(|&p| pretty::name_to_string(&env, p)).collect();
    println!("kind: {}", c.kind);
    println!("name: {}", pretty::name_to_string(&env, c.name));
    println!("universe params: {}", if params.is_empty() { "(none)".to_string() } else { params.join(" ") });
    println!("type: {}", pretty::statement(&env, &c, opts));
    Ok(())
}

/// Deeply nested proof terms need a deep stack.
fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> Result<T, String> + Send + 'static) -> Result<T, String> {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .map_err(|e| e.to_string())?
        .join()
        .map_err(|_| "checker thread panicked".to_string())?
}

fn resolve(env: &Env, names: &[String]) -> Result<Vec<usize>, String> {
    if names.len() <= 2 {
        return names.iter().map(|n| env.find_decl(n).ok_or_else(|| format!("no declaration named {n}"))).collect();
    }
    let index: std::collections::HashMap<String, usize> =
        env.decl_of_name.iter().map(|(&n, &i)| (env.name_str(n), i)).collect();
    names.iter().map(|n| index.get(n).copied().ok_or_else(|| format!("no declaration named {n}"))).collect()
}

/// `Err` is a failure (including `REJECTED`); `Ok(Err(_))` means the kernel
/// declined: it ran out of resources before reaching a verdict.
fn check_cmd(path: &str, args: &[String]) -> Result<Result<(), String>, String> {
    let mut names: Vec<String> = Vec::new();
    let mut jobs = std::thread::available_parallelism().map_or(1, |n| n.get());
    let mut cache_dir = default_cache_dir();
    let mut report: Option<String> = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--report" {
            report = Some(it.next().ok_or("--report needs a file")?.clone());
        } else if a == "--jobs" || a == "-j" {
            let n = it.next().ok_or("--jobs needs a number")?;
            jobs = n
                .parse()
                .ok()
                .filter(|&n: &usize| n > 0)
                .ok_or_else(|| format!("--jobs: not a positive number: {n}"))?;
        } else if a == "--cache" {
            cache_dir = Some(it.next().ok_or("--cache needs a directory")?.into());
        } else if a == "--no-cache" {
            cache_dir = None;
        } else {
            names.push(a.clone());
        }
    }
    let names = &names[..];
    let mut cache = cache_dir.and_then(VerdictCache::open);
    // A report needs the parsed export, so it skips the whole-export shortcut.
    if let Some(c) = cache.as_ref().filter(|_| report.is_none()) {
        // An export accepted before, byte for byte, by this same build and for
        // the same targets: nothing to parse or check.
        let t = Instant::now();
        if let Ok(bytes) = hash_file(path)
            && c.known.contains(&certus_core::cache::export_key(&c.checker, &bytes, names))
        {
            println!(
                "OK: export unchanged since this build accepted it (verdict cache, {:.3} s)",
                t.elapsed().as_secs_f64()
            );
            return Ok(Ok(()));
        }
    }
    let (env, bytes) = load_hashed(path)?;
    let roots = resolve(&env, names)?;
    let decls: Vec<usize> =
        if names.is_empty() { (0..env.decls.len()).collect() } else { deps::closure(&env, &roots).decls };
    let write_report = |verdict: report::Verdict, from_cache: usize| -> Result<(), String> {
        let Some(out) = &report else { return Ok(()) };
        let checker = checker_id().ok_or("--report: cannot read the certus executable to identify the build")?;
        let r = report::build(&env, &roots, &checker, &bytes, verdict, from_cache);
        std::fs::write(out, report::to_json(&r)).map_err(|e| format!("{out}: {e}"))
    };
    if let Some(c) = &mut cache {
        c.keys = certus_core::cache::keys(&env, &c.checker);
        c.export = Some(certus_core::cache::export_key(&c.checker, &bytes, names));
    }
    let known: Vec<bool> = match &cache {
        Some(c) => decls.iter().map(|&i| c.is_known(i)).collect(),
        None => Vec::new(),
    };
    if !known.is_empty() && known.iter().all(|&k| k) {
        // Every declaration, inductive types included, was accepted before
        // with exactly this content and these dependencies.
        println!("OK: {} declarations type-checked (all known good from the verdict cache)", decls.len());
        let admitted = decls.iter().filter(|&&i| !matches!(env.decls[i], Decl::Inductive(_) | Decl::Quot(_))).count();
        write_report(report::Verdict::Accepted, admitted)?;
        if let Some(c) = &cache
            && let Err(e) = c.remember(&[])
        {
            eprintln!("warning: could not write the verdict cache: {e}");
        }
        return Ok(Ok(()));
    }
    let r = match certus_kernel::check_with(&env, &decls, jobs, &known) {
        Ok(r) => r,
        Err(e) if e.resource => {
            write_report(report::Verdict::Declined(e.to_string()), 0)?;
            return Ok(Err(format!("DECLINED {e} (no verdict: out of resources)")));
        }
        Err(e) => {
            write_report(report::Verdict::Rejected(e.to_string()), 0)?;
            return Err(format!("REJECTED {e}"));
        }
    };
    write_report(report::Verdict::Accepted, r.from_cache)?;
    if let Some(c) = &cache
        && let Err(e) = c.remember(&decls)
    {
        eprintln!("warning: could not write the verdict cache: {e}");
    }
    let kinds: Vec<String> = r.by_kind.iter().map(|(k, n)| format!("{n} {k}")).collect();
    println!(
        "OK: {} declarations type-checked in {:.3} s on {} thread{} ({})",
        r.checked,
        r.time.as_secs_f64(),
        r.threads,
        if r.threads == 1 { "" } else { "s" },
        kinds.join(", ")
    );
    if r.from_cache > 0 {
        println!("{} of them known good from the verdict cache", r.from_cache);
    }
    println!("term nodes: {}; Nat operations verified for native arithmetic: {}", r.term_nodes, r.native_nat_ops);
    for (n, t) in &r.slowest {
        println!("  {:>9.3} ms  {n}", t.as_secs_f64() * 1e3);
    }
    Ok(Ok(()))
}

fn default_cache_dir() -> Option<std::path::PathBuf> {
    let base = std::env::var_os("XDG_CACHE_HOME")
        .filter(|s| !s.is_empty())
        .map(std::path::PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| std::path::Path::new(&h).join(".cache")))?;
    Some(base.join("certus"))
}

/// The per-declaration verdict cache (issue #9, docs/CACHE.md): one line per
/// accepted declaration in `verdicts-v1.log`, each holding the declaration's
/// key (`certus_core::cache`) and a check value. Unreadable, malformed or
/// mismatching lines are ignored: they can only cause a re-check.
struct VerdictCache {
    file: std::path::PathBuf,
    checker: hash::Hash,
    /// Key of every declaration, and of the whole check (set once parsed).
    keys: Vec<Option<hash::Hash>>,
    export: Option<hash::Hash>,
    known: HashSet<hash::Hash>,
}

impl VerdictCache {
    fn open(dir: std::path::PathBuf) -> Option<Self> {
        let file = dir.join("verdicts-v1.log");
        let checker = checker_id()?;
        let known = std::fs::read_to_string(&file)
            .map(|s| s.lines().filter_map(certus_core::cache::parse_entry).collect())
            .unwrap_or_default();
        Some(VerdictCache { file, checker, keys: Vec::new(), export: None, known })
    }

    fn is_known(&self, decl: usize) -> bool {
        self.keys[decl].is_some_and(|k| self.known.contains(&k))
    }

    /// Record that every declaration in `decls` was accepted, and so was
    /// the whole check.
    fn remember(&self, decls: &[usize]) -> std::io::Result<()> {
        let mut new = String::new();
        for k in decls.iter().filter_map(|&i| self.keys[i].as_ref()).chain(&self.export) {
            if !self.known.contains(k) {
                new.push_str(&certus_core::cache::entry(k));
                new.push('\n');
            }
        }
        if new.is_empty() {
            return Ok(());
        }
        if let Some(dir) = self.file.parent() {
            std::fs::create_dir_all(dir)?;
        }
        // One append of whole lines; a torn write only produces lines that
        // fail their check and are ignored.
        let mut f = std::fs::OpenOptions::new().create(true).append(true).open(&self.file)?;
        f.write_all(new.as_bytes())
    }
}

/// Identifies this exact checker build: the hash of the running executable,
/// so a rebuilt checker never reuses verdicts from another build. `None` if
/// the executable cannot be read (then the cache is not used).
fn checker_id() -> Option<hash::Hash> {
    let bytes = std::env::current_exe().and_then(std::fs::read).ok()?;
    Some(*blake3::Hasher::new_derive_key("certus verdict cache v1 checker id").update(&bytes).finalize().as_bytes())
}

fn extract_cmd(path: &str, out: &str, names: &[String]) -> Result<(), String> {
    let env = load(path)?;
    let roots = resolve(&env, names)?;
    let c = deps::closure(&env, &roots);
    let f = File::create(out).map_err(|e| format!("{out}: {e}"))?;
    certus_core::write::write_subset(&env, &c.decls, BufWriter::new(f)).map_err(|e| format!("{out}: {e}"))?;
    let size = std::fs::metadata(out).map(|m| m.len()).unwrap_or(0);
    println!("wrote {} declarations to {out} ({:.1} KB)", c.decls.len(), size as f64 / 1e3);
    Ok(())
}
