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
    /// Proofs of theorems admitted before this position are kept (the
    /// prelude zone: `Nat` fingerprints cover their closures).
    zone_end: usize,
    /// `CERTUS_EXTRACT=name:path`: write that declaration's dependency
    /// closure as a standalone export, and stop.
    extract: Option<(String, String)>,
    decls_meta: Vec<Decl>,
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
        if self.extract.is_some() {
            self.decls_meta.push(d.clone());
        }
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
        if let Some((target, path)) = self.extract.clone()
            && name_string(seen.names, d.primary_name()) == target
        {
            let msg = match self.write_closure(seen, d.primary_name(), &path) {
                Ok(n) => format!("extracted {target} and the {n} declarations it depends on to {path}"),
                Err(e) => format!("could not write {path}: {e}"),
            };
            self.failure = Some((pos, err(&target, msg, true)));
            return Err(());
        }
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
        if self.zone.is_some()
            && (self.zone.as_ref().is_some_and(|z| z.exprs.len() > ZONE_MAX_EXPRS)
                || (!cand.nat_ops.is_empty() && self.builtins.nat_ops.len() == cand.nat_ops.len()))
        {
            self.zone = None;
            self.zone_end = pos + 1;
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
                Kind::Thm { val } if table[n].0 < self.zone_end || concludes(&self.st, &self.keep_proofs_of, c.ty) => {
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

impl Checker<'_> {
    /// Write the dependency closure of constant `target` (just admitted) as a
    /// standalone export: names and declaration metadata as in the original,
    /// expressions re-emitted from the kernel's terms (binder names and
    /// binder info are lost; the kernel ignores them). A theorem whose proof
    /// was not kept becomes an axiom, and an opaque one too (the kernel does
    /// not keep opaque values). Returns how many declarations were written.
    fn write_closure(&self, seen: &Streamed, target: NameId, path: &str) -> std::io::Result<usize> {
        use std::io::Write;
        let table = &self.consts;
        let st = &self.st;
        let mut todo: Vec<NameId> = vec![target];
        let c = &self.cand;
        todo.extend(
            [
                c.nat,
                c.nat_zero,
                c.nat_succ,
                c.bool_true,
                c.bool_false,
                c.string,
                c.string_mk,
                c.string_of_list,
                c.char,
                c.char_of_nat,
                c.list_nil,
                c.list_cons,
                c.eq,
                c.eq_refl,
                c.quot,
            ]
            .into_iter()
            .flatten(),
        );
        todo.extend(c.nat_ops.iter().map(|(n, _)| *n));
        let mut seen_names: rustc_hash::FxHashSet<NameId> = Default::default();
        let mut positions: std::collections::BTreeSet<usize> = Default::default();
        let mut seen_e: rustc_hash::FxHashSet<E> = Default::default();
        let mut stack: Vec<E> = Vec::new();
        while let Some(n) = todo.pop() {
            if !seen_names.insert(n) {
                continue;
            }
            let Some((pos, info)) = table.get(&n) else { continue };
            if positions.insert(*pos) {
                todo.extend(self.decls_meta[*pos].defined_names());
            }
            stack.push(info.ty);
            match &info.kind {
                Kind::Def { val, .. } => stack.push(*val),
                Kind::Thm { val } if *val != DROPPED => stack.push(*val),
                Kind::Rec { rules, .. } => stack.extend(rules.iter().map(|r| r.rhs)),
                _ => {}
            }
            while let Some(e) = stack.pop() {
                if !seen_e.insert(e) {
                    continue;
                }
                match st.node(e) {
                    Node::Const(m, _) => todo.push(m),
                    Node::Proj(s, _, x) => {
                        todo.push(s);
                        stack.push(x);
                    }
                    Node::App(a, b) | Node::Lam(a, b) | Node::Pi(a, b) => stack.extend([a, b]),
                    Node::Let(a, b, x) => stack.extend([a, b, x]),
                    _ => {}
                }
            }
        }
        // Emit expressions children first: kernel ids increase from parts to wholes.
        let mut es: Vec<E> = seen_e.into_iter().collect();
        es.sort_unstable();
        let mut used_names: std::collections::BTreeSet<NameId> = Default::default();
        let mut lv: FxHashMap<L, usize> = FxHashMap::default();
        lv.insert(st.zero, 0);
        let mut level_lines: Vec<String> = Vec::new();
        fn level(
            st: &Store,
            l: L,
            lv: &mut FxHashMap<L, usize>,
            out: &mut Vec<String>,
            names: &mut std::collections::BTreeSet<NameId>,
        ) -> usize {
            if let Some(&i) = lv.get(&l) {
                return i;
            }
            let body = match st.lnode(l) {
                Level::Zero => unreachable!("level zero is id 0"),
                Level::Succ(a) => format!("\"succ\":{}", level(st, a, lv, out, names)),
                Level::Max(a, b) => {
                    format!("\"max\":[{},{}]", level(st, a, lv, out, names), level(st, b, lv, out, names))
                }
                Level::IMax(a, b) => {
                    format!("\"imax\":[{},{}]", level(st, a, lv, out, names), level(st, b, lv, out, names))
                }
                Level::Param(p) => {
                    names.insert(p);
                    format!("\"param\":{p}")
                }
            };
            let i = lv.len();
            lv.insert(l, i);
            out.push(format!("{{\"il\":{i},{body}}}"));
            i
        }
        let mut ids: FxHashMap<E, usize> = FxHashMap::default();
        let mut expr_lines: Vec<String> = Vec::with_capacity(es.len());
        for &e in &es {
            let k = ids.len();
            let id = |x: E| ids[&x];
            let line = match st.node(e) {
                Node::BVar(i) => format!("{{\"bvar\":{i},\"ie\":{k}}}"),
                Node::FVar(_) => continue,
                Node::Sort(l) => {
                    format!("{{\"ie\":{k},\"sort\":{}}}", level(st, l, &mut lv, &mut level_lines, &mut used_names))
                }
                Node::Const(n, ls) => {
                    used_names.insert(n);
                    let us: Vec<String> = st
                        .list_of(ls)
                        .to_vec()
                        .into_iter()
                        .map(|l| level(st, l, &mut lv, &mut level_lines, &mut used_names).to_string())
                        .collect();
                    format!("{{\"const\":{{\"name\":{n},\"us\":[{}]}},\"ie\":{k}}}", us.join(","))
                }
                Node::App(f, a) => format!("{{\"app\":{{\"arg\":{},\"fn\":{}}},\"ie\":{k}}}", id(a), id(f)),
                Node::Lam(d, b) => format!(
                    "{{\"ie\":{k},\"lam\":{{\"binderInfo\":\"default\",\"body\":{},\"name\":0,\"type\":{}}}}}",
                    id(b),
                    id(d)
                ),
                Node::Pi(d, b) => format!(
                    "{{\"forallE\":{{\"binderInfo\":\"default\",\"body\":{},\"name\":0,\"type\":{}}},\"ie\":{k}}}",
                    id(b),
                    id(d)
                ),
                Node::Let(t, v, b) => format!(
                    "{{\"ie\":{k},\"letE\":{{\"body\":{},\"name\":0,\"nondep\":false,\"type\":{},\"value\":{}}}}}",
                    id(b),
                    id(t),
                    id(v)
                ),
                Node::Nat(i) => format!("{{\"ie\":{k},\"natVal\":\"{}\"}}", st.nat_val(i)),
                Node::Str(i) => {
                    format!("{{\"ie\":{k},\"strVal\":{}}}", serde_json::to_string(st.str_val(i)).unwrap_or_default())
                }
                Node::Proj(s, i, x) => {
                    used_names.insert(s);
                    format!("{{\"ie\":{k},\"proj\":{{\"idx\":{i},\"struct\":{},\"typeName\":{s}}}}}", id(x))
                }
            };
            ids.insert(e, k);
            expr_lines.push(line);
        }
        // Declarations, with their expressions renumbered.
        let ty = |n: NameId| table.get(&n).map(|(_, c)| ids[&c.ty]);
        let mut decl_lines: Vec<String> = Vec::new();
        for &pos in &positions {
            let d = &self.decls_meta[pos];
            for n in d.defined_names() {
                used_names.insert(n);
            }
            let line = match d {
                Decl::Axiom(a) => {
                    let mut a = a.clone();
                    a.r#type = ty(a.name).unwrap_or(0) as u32;
                    used_names.extend(a.level_params.iter());
                    serde_json::json!({ "axiom": a })
                }
                Decl::Quot(a) => {
                    let mut a = a.clone();
                    a.r#type = ty(a.name).unwrap_or(0) as u32;
                    used_names.extend(a.level_params.iter());
                    serde_json::json!({ "quot": a })
                }
                Decl::Def(a) => {
                    let mut a = a.clone();
                    a.r#type = ty(a.name).unwrap_or(0) as u32;
                    if let Some((_, crate::env::ConstInfo { kind: Kind::Def { val, .. }, .. })) = table.get(&a.name) {
                        a.value = ids[val] as u32;
                    }
                    used_names.extend(a.level_params.iter().chain(a.all.iter()));
                    serde_json::json!({ "def": a })
                }
                Decl::Thm(a) => {
                    used_names.extend(a.level_params.iter().chain(a.all.iter()));
                    match table.get(&a.name).map(|(_, c)| &c.kind) {
                        Some(Kind::Thm { val }) if *val != DROPPED => {
                            let mut a = a.clone();
                            a.r#type = ty(a.name).unwrap_or(0) as u32;
                            a.value = ids[val] as u32;
                            serde_json::json!({ "thm": a })
                        }
                        _ => serde_json::json!({ "axiom": ex::AxiomVal {
                            name: a.name, level_params: a.level_params.clone(), r#type: ty(a.name).unwrap_or(0) as u32, is_unsafe: false } }),
                    }
                }
                Decl::Opaque(a) => {
                    used_names.extend(a.level_params.iter());
                    serde_json::json!({ "axiom": ex::AxiomVal {
                        name: a.name, level_params: a.level_params.clone(), r#type: ty(a.name).unwrap_or(0) as u32, is_unsafe: false } })
                }
                Decl::Inductive(b) => {
                    let mut b = b.clone();
                    for t in &mut b.types {
                        t.r#type = ty(t.name).unwrap_or(0) as u32;
                        used_names.extend(t.level_params.iter().chain(t.all.iter()).chain(t.ctors.iter()));
                    }
                    for c in &mut b.ctors {
                        c.r#type = ty(c.name).unwrap_or(0) as u32;
                        used_names.insert(c.induct);
                        used_names.extend(c.level_params.iter());
                    }
                    for r in &mut b.recs {
                        r.r#type = ty(r.name).unwrap_or(0) as u32;
                        used_names.extend(r.level_params.iter().chain(r.all.iter()));
                        if let Some((_, crate::env::ConstInfo { kind: Kind::Rec { rules, .. }, .. })) =
                            table.get(&r.name)
                        {
                            for rule in &mut r.rules {
                                used_names.insert(rule.ctor);
                                if let Some(k) = rules.iter().find(|x| x.ctor == rule.ctor) {
                                    rule.rhs = ids[&k.rhs] as u32;
                                }
                            }
                        }
                    }
                    serde_json::json!({ "inductive": b })
                }
            };
            decl_lines.push(line.to_string());
        }
        // Names, prefixes first, with their original ids.
        let mut all_names: std::collections::BTreeSet<NameId> = Default::default();
        for &n in &used_names {
            let mut m = n;
            while m != 0 && all_names.insert(m) {
                m = match &seen.names[m as usize] {
                    ex::Name::Str { pre, .. } | ex::Name::Num { pre, .. } => *pre,
                    ex::Name::Anon => 0,
                };
            }
        }
        let mut f = std::io::BufWriter::new(std::fs::File::create(path)?);
        writeln!(
            f,
            r#"{{"meta":{{"exporter":{{"name":"certus-extract","version":"0"}},"format":{{"version":"3.1.0"}},"lean":{{"githash":"","version":"4.33.1"}}}}}}"#
        )?;
        for &n in &all_names {
            match &seen.names[n as usize] {
                ex::Name::Str { pre, s } => writeln!(
                    f,
                    r#"{{"in":{n},"str":{{"pre":{pre},"str":{}}}}}"#,
                    serde_json::to_string(s).unwrap_or_default()
                )?,
                ex::Name::Num { pre, n: i } => writeln!(f, r#"{{"in":{n},"num":{{"i":{i},"pre":{pre}}}}}"#)?,
                ex::Name::Anon => {}
            }
        }
        for l in level_lines.iter().chain(&expr_lines).chain(&decl_lines) {
            writeln!(f, "{l}")?;
        }
        f.flush()?;
        Ok(positions.len())
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
        zone_end: usize::MAX,
        extract: std::env::var("CERTUS_EXTRACT")
            .ok()
            .and_then(|s| s.split_once(':').map(|(a, b)| (a.to_string(), b.to_string()))),
        decls_meta: Vec::new(),
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
