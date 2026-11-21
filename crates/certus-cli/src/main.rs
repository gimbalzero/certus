//! `certus`: inspect Lean 4 kernel exports produced by `lean4export`.

use certus_core::{Env, deps, hash, parse};
use std::collections::{BTreeMap, HashSet};
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
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

    certus check <export.ndjson> [<Decl.Name>...]
        Type-check declarations with the Certus kernel. With names, check
        exactly what those declarations depend on; without, check everything.
    certus extract <export.ndjson> <out.ndjson> <Decl.Name>...
        Write a minimal certificate: the named declarations plus everything
        they depend on, as a standalone export file.

Exports come from lean4export (format 3.x).";

/// The axioms accepted by Mathlib and by Lean's own checkers.
const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("stats") if args.len() == 2 => stats(&args[1]),
        Some("hash") if args.len() == 2 => hash_cmd(&args[1], None),
        Some("hash") if args.len() == 4 && args[2] == "--manifest" => hash_cmd(&args[1], Some(&args[3])),
        Some("deps") if args.len() == 3 => deps_cmd(&args[1], &args[2], false),
        Some("deps") if args.len() == 4 && args[3] == "--list" => deps_cmd(&args[1], &args[2], true),
        Some("check") if args.len() >= 2 => with_big_stack(move || check_cmd(&args[1], &args[2..])),
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

/// Deeply nested proof terms need a deep stack.
fn with_big_stack(f: impl FnOnce() -> Result<(), String> + Send + 'static) -> Result<(), String> {
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

fn check_cmd(path: &str, names: &[String]) -> Result<(), String> {
    let env = load(path)?;
    let decls: Vec<usize> = if names.is_empty() {
        (0..env.decls.len()).collect()
    } else {
        let roots = resolve(&env, names)?;
        deps::closure(&env, &roots).decls
    };
    let r = certus_kernel::check(&env, &decls).map_err(|e| format!("REJECTED {e}"))?;
    let kinds: Vec<String> = r.by_kind.iter().map(|(k, n)| format!("{n} {k}")).collect();
    println!("OK: {} declarations type-checked in {:.3} s ({})", r.checked, r.time.as_secs_f64(), kinds.join(", "));
    println!("term nodes: {}; Nat operations verified for native arithmetic: {}", r.term_nodes, r.native_nat_ops);
    for (n, t) in &r.slowest {
        println!("  {:>9.3} ms  {n}", t.as_secs_f64() * 1e3);
    }
    Ok(())
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
