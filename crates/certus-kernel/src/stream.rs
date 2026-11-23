//! Checking an export too large to hold in memory.
//!
//! The Riemann Hypothesis formalisation of November 2026 exports to 61.6 GB:
//! 1.07 billion expression nodes and 1.47 million declarations. Holding all
//! of it, as [`crate::check`] does, takes about 50 GB. Here the export is
//! read twice, as a stream, and never held:
//!
//! 1. **Survey.** Mark every expression that a later declaration's records
//!    refer to (one bit per expression), and note which names the kernel
//!    treats specially are defined, so that builtins are switched on exactly
//!    as for a whole export.
//! 2. **Check.** Convert each record into the term store as it arrives and
//!    admit each declaration as phase 1 of `check_jobs` does (inductive
//!    types and quotients are checked in full). Every few thousand
//!    declarations, type-check the batch on all threads, then forget every
//!    term of the batch except what later declarations can need: the
//!    constants' types, definitions' values, recursor rules, and the marked
//!    expressions (with everything they are built from).
//!
//! **Theorem proofs are forgotten once checked.** A later check that would
//! unfold a theorem gets a resource error (no verdict), never a rejection
//! (see `TC::unfold`).
//!
//! **Verdict:** the same as checking the whole export: declarations are
//! admitted in file order, each is type-checked in the environment of the
//! declarations before it, and the failure at the earliest position wins.

use crate::check::{
    CheckError, ExprSource, Report, Shared, Todo, activate_nat, activate_string, admit_decl, run_worker, spawn_checker,
};
use crate::env::{Builtins, ConstTable, KEnv, Kind};
use crate::tc::{DROPPED, KError, R};
use crate::term::{E, L, Level, Node, Store};
use certus_core::export::{self as ex, Decl, Env, Expr, Item, NameId, Streamed};
use num_bigint::BigUint;
use rustc_hash::FxHashMap;
use std::collections::HashMap;
use std::io::BufRead;
use std::sync::Arc;
use std::sync::atomic::AtomicUsize;
use std::time::{Duration, Instant};

/// Type-check a batch once it has this many declarations to check, or once
/// it holds this many new terms.
const BATCH_TODOS: usize = 1 << 14;
const BATCH_NODES: usize = 1 << 24;

/// The prelude zone: expressions and declarations are also kept as an
/// export (`Env`) until the genuine `Nat` operations are recognised, which
/// needs their dependency closures by content (see `check::activate_nat`).
/// They are all in Lean's prelude, near the start of the file.
const ZONE_MAX_EXPRS: usize = 1 << 24;

/// Opens the export, once per pass.
pub type Open<'a> = dyn Fn() -> Result<Box<dyn BufRead + Send>, String> + 'a;

/// What the survey (pass 1) found.
struct Survey {
    /// Bit `i`: expression `i` is referred to by a later declaration's records.
    reused: Vec<u64>,
    /// The specially treated names the export defines, by printed name.
    special: HashMap<String, NameId>,
}

fn bit(v: &[u64], i: u32) -> bool {
    v.get(i as usize / 64).is_some_and(|w| w >> (i % 64) & 1 == 1)
}

fn name_string(names: &[ex::Name], mut id: NameId) -> String {
    let mut parts = Vec::new();
    loop {
        match &names[id as usize] {
            ex::Name::Anon => break,
            ex::Name::Str { pre, s } => {
                parts.push(s.clone());
                id = *pre;
            }
            ex::Name::Num { pre, n } => {
                parts.push(n.to_string());
                id = *pre;
            }
        }
    }
    parts.reverse();
    parts.join(".")
}

fn children(e: &Expr, mut f: impl FnMut(u32)) {
    match e {
        Expr::App { f: g, a } => {
            f(*g);
            f(*a)
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            f(*ty);
            f(*body)
        }
        Expr::Let { ty, val, body, .. } => {
            f(*ty);
            f(*val);
            f(*body)
        }
        Expr::Proj { structure, .. } => f(*structure),
        Expr::BVar(_) | Expr::Sort(_) | Expr::Const { .. } | Expr::NatLit(_) | Expr::StrLit(_) => {}
    }
}

/// The printed names `Builtins::resolve` asks for, and those of
/// `KEEP_PROOFS_OF`.
fn special_names() -> Vec<String> {
    let asked = std::cell::RefCell::new(Vec::new());
    Builtins::resolve(|s| {
        asked.borrow_mut().push(s.to_string());
        None
    });
    let mut v = asked.into_inner();
    v.extend(KEEP_PROOFS_OF.iter().map(|s| s.to_string()));
    v
}

/// Proofs of theorems concluding one of these are kept: well-founded
/// recursion computes with them (`Acc.rec` needs its major premise to reduce
/// to `Acc.intro`), so later checks may unfold them. Other proofs are only
/// ever needed as proofs, which proof irrelevance makes interchangeable.
/// (If one is needed after all, the check declines; it never rejects.)
const KEEP_PROOFS_OF: [&str; 2] = ["Acc", "WellFounded"];

fn survey(open: &Open, jobs: usize) -> Result<Survey, CheckError> {
    let wanted = special_names();
    let mut reused: Vec<u64> = Vec::new();
    let mut special = HashMap::new();
    let mut next: u32 = 0; // expressions seen
    let mut seg_start: u32 = 0; // first expression of the current declaration's records
    let reader = open().map_err(|e| err("", e, false))?;
    let mark = |reused: &mut Vec<u64>, c: u32, seg_start: u32| {
        if c < seg_start {
            reused[c as usize / 64] |= 1 << (c % 64);
        }
    };
    ex::stream(reader, jobs, &mut |seen: &Streamed, items: Vec<Item>| {
        if reused.len() * 64 < seen.exprs + 64 {
            reused.resize(seen.exprs / 64 + (1 << 16), 0);
        }
        for it in items {
            match it {
                Item::Expr(id, e) => {
                    debug_assert_eq!(id, next);
                    children(&e, |c| mark(&mut reused, c, seg_start));
                    next += 1;
                }
                Item::Decl(d) => {
                    for r in d.roots() {
                        mark(&mut reused, r, seg_start);
                    }
                    for n in d.defined_names() {
                        let s = name_string(seen.names, n);
                        if wanted.contains(&s) {
                            special.insert(s, n);
                        }
                    }
                    seg_start = next;
                }
            }
        }
        Ok(())
    })
    .map_err(|e| err("", e.to_string(), false))?;
    Ok(Survey { reused, special })
}

/// Does a theorem of type `ty` conclude one of `heads` (`Acc …`, `WellFounded …`)?
fn concludes(st: &Store, heads: &[NameId], mut ty: E) -> bool {
    while let Node::Pi(_, b) = st.node(ty) {
        ty = b;
    }
    matches!(st.node(st.head(ty)), Node::Const(n, _) if heads.contains(&n))
}

fn err(decl: &str, msg: String, resource: bool) -> CheckError {
    CheckError { decl: decl.to_string(), msg, resource }
}

/// The state of pass 2.
struct Checker<'s> {
    jobs: usize,
    survey: &'s Survey,
    cand: Builtins,
    st: Store,
    /// Terms below this id are kept for good; the current batch's are above.
    persist: usize,
    /// Theorems concluding one of these keep their proofs (see `KEEP_PROOFS_OF`).
    keep_proofs_of: Vec<NameId>,
    consts: Arc<ConstTable>,
    builtins: Builtins,
    history: Vec<(usize, Builtins)>,
    /// Term of each marked expression of an earlier batch, by export id.
    kept: FxHashMap<u32, E>,
    /// Term of each expression of the current batch, from `batch_first` on.
    batch_first: u32,
    batch_map: Vec<E>,
    levels: Vec<Option<L>>,
    /// The current batch: its first position, what is left to check, and the
    /// constants it added.
    batch_pos: usize,
    todo: Vec<Option<Todo>>,
    batch_names: Vec<NameId>,
    /// Declarations admitted so far (the next position).
    pos: usize,
    zone: Option<Env>,
    failure: Option<(usize, CheckError)>,
    kinds: FxHashMap<&'static str, usize>,
    peak_nodes: usize,
    batches: usize,
    times: Vec<(String, Duration)>,
    progress: bool,
    started: Instant,
}

/// Looks up the term of an export expression for `admit_decl`.
struct Src<'a, 'b> {
    c: &'a mut Checker<'b>,
}

impl ExprSource for Src<'_, '_> {
    fn expr(&mut self, _st: &mut Store, id: u32) -> R<E> {
        self.c.get(id)
    }
}

impl<'s> Checker<'s> {
    fn get(&self, id: u32) -> R<E> {
        if id >= self.batch_first {
            return self
                .batch_map
                .get((id - self.batch_first) as usize)
                .copied()
                .ok_or_else(|| "undefined expression".into());
        }
        self.kept.get(&id).copied().ok_or_else(|| {
            KError::Resource(format!("internal: expression {id} was not kept (the survey missed a reference)"))
        })
    }

    fn level(&mut self, levels: &[ex::Level], id: u32) -> L {
        if self.levels.len() <= id as usize {
            self.levels.resize(levels.len().max(id as usize + 1), None);
        }
        if let Some(l) = self.levels[id as usize] {
            return l;
        }
        let l = match levels[id as usize] {
            ex::Level::Zero => Level::Zero,
            ex::Level::Succ(a) => Level::Succ(self.level(levels, a)),
            ex::Level::Max(a, b) => Level::Max(self.level(levels, a), self.level(levels, b)),
            ex::Level::IMax(a, b) => Level::IMax(self.level(levels, a), self.level(levels, b)),
            ex::Level::Param(p) => Level::Param(p),
        };
        let l = self.st.level(l);
        self.levels[id as usize] = Some(l);
        l
    }

    fn expr(&mut self, levels: &[ex::Level], e: &Expr) -> R<E> {
        let n = match e {
            Expr::BVar(i) => Node::BVar(u32::try_from(*i).map_err(|_| "bound variable index too large")?),
            Expr::Sort(l) => Node::Sort(self.level(levels, *l)),
            Expr::Const { name, levels: ls } => {
                let ls: Vec<L> = ls.iter().map(|&l| self.level(levels, l)).collect();
                Node::Const(*name, self.st.list(&ls))
            }
            Expr::App { f, a } => Node::App(self.get(*f)?, self.get(*a)?),
            Expr::Lam { ty, body, .. } => Node::Lam(self.get(*ty)?, self.get(*body)?),
            Expr::Pi { ty, body, .. } => Node::Pi(self.get(*ty)?, self.get(*body)?),
            Expr::Let { ty, val, body, .. } => Node::Let(self.get(*ty)?, self.get(*val)?, self.get(*body)?),
            Expr::NatLit(s) => {
                let v: BigUint = s.parse().map_err(|_| "malformed natural-number literal")?;
                return Ok(self.st.nat(v));
            }
            Expr::StrLit(s) => return Ok(self.st.str_lit(s)),
            Expr::Proj { type_name, idx, structure } => Node::Proj(
                *type_name,
                u32::try_from(*idx).map_err(|_| "projection index too large")?,
                self.get(*structure)?,
            ),
        };
        Ok(self.st.mk(n))
    }

    fn kenv(&self, visible: usize) -> KEnv {
        KEnv { consts: self.consts.clone(), visible, builtins: self.builtins.clone() }
    }

    /// Admit the declaration at position `self.pos`.
    fn admit(&mut self, seen: &Streamed, d: Decl) -> Result<(), ()> {
        let pos = self.pos;
        let kenv = self.kenv(pos);
        let mut st = std::mem::take(&mut self.st);
        crate::tc::MISSED_PROOF.with(|m| m.set(None));
        let r = crate::tc::unless_missed_proof(admit_decl(&mut st, &kenv, &mut Src { c: self }, seen.names, &d));
        self.st = st;
        drop(kenv);
        let (new, todo) = match r {
            Ok(x) => x,
            Err(e) => {
                self.failure = Some((pos, CheckError::new(name_string(seen.names, d.primary_name()), e)));
                return Err(());
            }
        };
        if let Some(z) = &mut self.zone {
            z.decls.push(d.clone());
            for n in d.defined_names() {
                z.decl_of_name.insert(n, pos);
            }
        }
        let table = Arc::get_mut(&mut self.consts).expect("the constant table is not shared between batches");
        for (n, info) in new.iter().cloned() {
            if table.insert(n, (pos, info)).is_some() {
                self.failure = Some((
                    pos,
                    err(&name_string(seen.names, d.primary_name()), "constant declared twice".into(), false),
                ));
                return Err(());
            }
            self.batch_names.push(n);
        }
        self.todo.push(todo.map(|t| Todo { decl: pos, ..t }));
        *self.kinds.entry(d.kind()).or_default() += 1;
        self.pos = pos + 1;
        // Builtins switch on once the constants they need are present.
        let mut kenv = self.kenv(pos + 1);
        let cand = self.cand.clone();
        for (n, _) in &new {
            let is_nat = Some(*n) == cand.nat || cand.nat_ops.iter().any(|(m, _)| m == n);
            if is_nat && let Some(z) = &mut self.zone {
                z.names = seen.names.to_vec();
                z.name_canon = seen.name_canon.to_vec();
                z.levels = seen.levels.to_vec();
                let mut hashes = None;
                activate_nat(&mut self.st, &mut kenv, &cand, *n, &|m| name_string(seen.names, m), z, &mut hashes);
            }
            activate_string(&mut self.st, &mut kenv, &cand, *n);
        }
        if kenv.builtins != self.builtins {
            self.builtins = kenv.builtins.clone();
            self.history.push((pos + 1, self.builtins.clone()));
        }
        if self.zone.as_ref().is_some_and(|z| z.exprs.len() > ZONE_MAX_EXPRS)
            || (!cand.nat_ops.is_empty() && self.builtins.nat_ops.len() == cand.nat_ops.len())
        {
            self.zone = None;
        }
        Ok(())
    }

    /// Type-check the current batch on all threads, then keep only what later
    /// declarations can need.
    fn flush(&mut self, seen: &Streamed) {
        self.batches += 1;
        self.peak_nodes = self.peak_nodes.max(self.st.num_nodes());
        let todo = std::mem::take(&mut self.todo);
        let n_todo = todo.iter().filter(|t| t.is_some()).count();
        let first_failure = self.failure.as_ref().map_or(usize::MAX, |(p, _)| *p);
        let name_of = |n: NameId| name_string(seen.names, n);
        let decl_names: Vec<(usize, NameId)> = todo.iter().flatten().map(|t| (t.decl, t.decl_name)).collect();
        let skip = self.st.num_nodes();
        let base = std::mem::take(&mut self.st).freeze();
        let shared = Shared {
            name: &name_of,
            offset: self.batch_pos,
            todo,
            consts: self.consts.clone(),
            builtins: self.history.clone(),
            next: AtomicUsize::new(self.batch_pos),
            first_failure: AtomicUsize::new(first_failure),
            running: Default::default(),
        };
        let todo_names: FxHashMap<usize, NameId> = decl_names.iter().copied().collect();
        let progress = self.progress;
        let done = std::sync::atomic::AtomicBool::new(false);
        let jobs = self.jobs.clamp(1, n_todo.max(1));
        let outs = std::thread::scope(|s| {
            let shared = &shared;
            if progress {
                let (done, todo_names, name_of) = (&done, &todo_names, &name_of);
                s.spawn(move || {
                    let mut ticks = 0u32;
                    while !done.load(std::sync::atomic::Ordering::Relaxed) {
                        std::thread::sleep(Duration::from_millis(500));
                        ticks += 1;
                        if ticks % 30 != 0 {
                            continue;
                        }
                        if let Ok(r) = shared.running.lock() {
                            for (pos, since) in r.values() {
                                let secs = since.elapsed().as_secs_f64();
                                if secs > 60.0 {
                                    let n = todo_names.get(pos).map(|n| name_of(*n)).unwrap_or_default();
                                    eprintln!("certus:   still checking #{pos} {n} after {secs:.0} s");
                                }
                            }
                        }
                    }
                });
            }
            let mut hs = Vec::new();
            if n_todo > 0 {
                for w in 0..jobs {
                    let st = Store::on(&base);
                    if let Ok(h) = spawn_checker(s, format!("certus-stream-{w}"), move || run_worker(shared, st, skip))
                    {
                        hs.push(h);
                    }
                }
            }
            let outs =
                hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect::<Vec<_>>();
            done.store(true, std::sync::atomic::Ordering::Relaxed);
            outs
        });
        drop(shared);
        for w in &outs {
            if let Some((p, e)) = &w.failure
                && self.failure.as_ref().is_none_or(|(q, _)| p < q)
            {
                let mut e = e.clone();
                // Name the theorem whose proof was missing.
                if let Some(i) = e.msg.find("theorem #")
                    && let Ok(id) = e.msg[i + 9..].trim_end_matches(')').parse::<NameId>()
                {
                    e.msg = format!("{}theorem {})", &e.msg[..i], name_of(id));
                }
                self.failure = Some((*p, e));
            }
            for &(i, t) in &w.times {
                if let Some((_, n)) = decl_names.iter().find(|(p, _)| *p == i) {
                    self.times.push((name_of(*n), t));
                }
            }
        }
        self.times.sort_by_key(|(_, t)| std::cmp::Reverse(*t));
        self.times.truncate(5);
        self.st = Store::unfreeze(base).unwrap_or_else(|_| panic!("the workers have finished"));
        self.compact();
        self.batch_pos = self.pos;
        if self.progress {
            eprintln!(
                "certus: batch {}: {} declarations checked, {} terms kept, {:.1} s",
                self.batches,
                self.pos,
                self.persist,
                self.started.elapsed().as_secs_f64()
            );
        }
    }

    /// Forget the current batch's terms except those later declarations can
    /// need, and renumber the rest.
    fn compact(&mut self) {
        let w = E(self.persist as u32);
        let table = Arc::get_mut(&mut self.consts).expect("the constant table is not shared between batches");
        let mut roots: Vec<E> = Vec::new();
        let mut keep_proof: Vec<NameId> = Vec::new();
        for n in &self.batch_names {
            let (_, c) = &table[n];
            roots.push(c.ty);
            match &c.kind {
                Kind::Def { val, .. } => roots.push(*val),
                Kind::Thm { val } if concludes(&self.st, &self.keep_proofs_of, c.ty) => {
                    roots.push(*val);
                    keep_proof.push(*n);
                }
                Kind::Rec { rules, .. } => roots.extend(rules.iter().map(|r| r.rhs)),
                _ => {}
            }
        }
        let marked: Vec<(u32, E)> = (0..self.batch_map.len())
            .map(|i| (self.batch_first + i as u32, self.batch_map[i]))
            .filter(|&(id, _)| bit(&self.survey.reused, id))
            .collect();
        roots.extend(marked.iter().map(|&(_, e)| e));
        let moved = self.st.collect(w, &roots);
        let fix = |e: E| if e < w { e } else { moved[&e] };
        for n in &self.batch_names {
            let (_, c) = table.get_mut(n).expect("added in this batch");
            c.ty = fix(c.ty);
            match &mut c.kind {
                Kind::Def { val, .. } => *val = fix(*val),
                Kind::Thm { val } if keep_proof.contains(n) => *val = fix(*val),
                Kind::Thm { val } => *val = DROPPED,
                Kind::Rec { rules, .. } => {
                    for r in rules {
                        r.rhs = fix(r.rhs);
                    }
                }
                _ => {}
            }
        }
        for (id, e) in marked {
            self.kept.insert(id, fix(e));
        }
        self.batch_names.clear();
        self.batch_first += self.batch_map.len() as u32;
        self.batch_map.clear();
        self.persist = self.st.num_nodes();
    }
}

/// Check every declaration of the export `open` reads, without holding it
/// (see the module documentation). `jobs` threads parse and type-check.
pub fn check_stream(open: &Open, jobs: usize) -> Result<Report, CheckError> {
    let start = Instant::now();
    let survey = survey(open, jobs)?;
    let surveyed = start.elapsed();
    if std::env::var_os("CERTUS_PROGRESS").is_some() {
        let marked: u64 = survey.reused.iter().map(|w| w.count_ones() as u64).sum();
        eprintln!("certus: survey done in {:.1} s: {marked} expressions are used again later", surveyed.as_secs_f64());
    }
    let mut cand = Builtins::resolve(|s| survey.special.get(s).copied());
    // As `check::Prep::new`: string literals expand with `String.ofList`
    // wherever the export defines it.
    if cand.string_of_list.is_some() {
        cand.string_mk = cand.string_of_list;
    }
    let empty = Builtins {
        nat: None,
        nat_zero: None,
        nat_succ: None,
        nat_ops: Vec::new(),
        string: None,
        string_mk: None,
        string_of_list: None,
        char: None,
        char_of_nat: None,
        list_nil: None,
        list_cons: None,
        ..cand.clone()
    };
    let mut c = Checker {
        jobs,
        survey: &survey,
        cand,
        st: Store::new(),
        persist: 0,
        keep_proofs_of: KEEP_PROOFS_OF.iter().filter_map(|s| survey.special.get(*s).copied()).collect(),
        consts: Arc::default(),
        builtins: empty.clone(),
        history: vec![(0, empty)],
        kept: FxHashMap::default(),
        batch_first: 0,
        batch_map: Vec::new(),
        levels: Vec::new(),
        batch_pos: 0,
        todo: Vec::new(),
        batch_names: Vec::new(),
        pos: 0,
        zone: None,
        failure: None,
        kinds: FxHashMap::default(),
        peak_nodes: 0,
        batches: 0,
        times: Vec::new(),
        progress: std::env::var_os("CERTUS_PROGRESS").is_some(),
        started: start,
    };
    c.persist = c.st.num_nodes();
    // Tests set a tiny batch (1: compact after every declaration).
    let batch_todos = std::env::var("CERTUS_STREAM_BATCH").ok().and_then(|s| s.parse().ok()).unwrap_or(BATCH_TODOS);
    let reader = open().map_err(|e| err("", e, false))?;
    let mut zone_meta = None;
    let res = ex::stream(reader, jobs, &mut |seen: &Streamed, items: Vec<Item>| {
        if c.zone.is_none() && c.pos == 0 && c.batches == 0 {
            c.zone = Some(Env {
                meta: zone_meta.take().unwrap_or_else(placeholder_meta),
                names: Vec::new(),
                name_canon: Vec::new(),
                levels: Vec::new(),
                exprs: Vec::new(),
                decls: Vec::new(),
                decl_of_name: HashMap::new(),
                bytes: 0,
                lines: 0,
            });
        }
        for it in items {
            match it {
                Item::Expr(id, e) => {
                    debug_assert_eq!(id, c.batch_first + c.batch_map.len() as u32);
                    match c.expr(seen.levels, &e) {
                        Ok(t) => c.batch_map.push(t),
                        Err(k) => {
                            c.failure = Some((c.pos, CheckError::new(String::new(), k)));
                            // Earlier declarations of the batch may fail first.
                            c.flush(seen);
                            return Err("stop".into());
                        }
                    }
                    if let Some(z) = &mut c.zone {
                        z.exprs.push(e);
                    }
                }
                Item::Decl(d) => {
                    if c.admit(seen, d).is_err() {
                        // Earlier declarations of the batch may fail first.
                        c.flush(seen);
                        return Err("stop".into());
                    }
                    let todos = c.todo.iter().filter(|t| t.is_some()).count();
                    if todos >= batch_todos || c.st.num_nodes() - c.persist >= BATCH_NODES {
                        c.flush(seen);
                        if c.failure.is_some() {
                            return Err("stop".into());
                        }
                    }
                }
            }
        }
        Ok(())
    });
    let end = match res {
        Ok(end) => Some(end),
        Err(e) if c.failure.is_some() && e.msg == "stop" => None,
        Err(e) => return Err(err("", e.to_string(), false)),
    };
    // Check what is left of the last batch (also before reporting a failure
    // found while admitting, so that an earlier one wins).
    if !c.todo.is_empty() || !c.batch_names.is_empty() {
        let names = end.as_ref().map(|e| e.names.clone()).unwrap_or_default();
        let seen =
            Streamed { names: &names, name_canon: &[], levels: &[], decl_of_name: &HashMap::new(), exprs: 0, decls: 0 };
        if end.is_some() {
            c.flush(&seen);
        }
    }
    if let Some((_, e)) = c.failure {
        return Err(e);
    }
    let mut by_kind: Vec<(&'static str, usize)> = c.kinds.into_iter().collect();
    by_kind.sort();
    let _ = surveyed;
    Ok(Report {
        checked: c.pos,
        by_kind,
        time: start.elapsed(),
        slowest: c.times,
        term_nodes: c.peak_nodes,
        native_nat_ops: c.builtins.nat_ops.len(),
        threads: jobs,
        from_cache: 0,
    })
}

fn placeholder_meta() -> ex::Meta {
    serde_json::from_str(r#"{"exporter":{"name":"stream","version":"0"},"format":{"version":"3.1.0"},"lean":{"githash":"","version":""}}"#)
        .expect("a valid meta record")
}
