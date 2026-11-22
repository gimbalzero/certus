//! Driver: convert exported declarations to kernel terms and check them in
//! dependency order, adding each to the environment only once it passes.

use crate::env::{Builtins, ConstInfo, ConstTable, Hints, KEnv, Kind, QuotKind, RecRule};
use crate::inductive::{self, Block};
use crate::quot::check_quot;
use crate::tc::{KError, R, STACK_SIZE, TC};
use crate::term::{E, L, Level, Node, Store};
use certus_core::export::{self as ex, Decl, Env, NameId};
use certus_core::{deps, hash};
use num_bigint::BigUint;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

#[derive(Debug)]
pub struct CheckError {
    pub decl: String,
    pub msg: String,
    /// `true` if checking ran out of resources (work budget or stack) before
    /// reaching a verdict, `false` if the declaration is invalid. Either way
    /// nothing is accepted.
    pub resource: bool,
}

impl CheckError {
    fn new(decl: String, e: KError) -> Self {
        CheckError { decl, resource: e.is_resource(), msg: e.msg().to_string() }
    }
}

impl std::fmt::Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.decl, self.msg)
    }
}

impl std::error::Error for CheckError {}

#[derive(Debug, Default)]
pub struct Report {
    pub checked: usize,
    pub by_kind: Vec<(&'static str, usize)>,
    pub time: Duration,
    pub slowest: Vec<(String, Duration)>,
    pub term_nodes: usize,
    /// Nat operations verified as genuine and computed natively.
    pub native_nat_ops: usize,
    /// Worker threads used.
    pub threads: usize,
    /// Declarations admitted as known good (from the verdict cache), not type-checked.
    pub from_cache: usize,
}

struct Conv<'x> {
    ex: &'x Env,
    exprs: Vec<Option<E>>,
    levels: Vec<Option<L>>,
}

impl Conv<'_> {
    fn level(&mut self, st: &mut Store, id: u32) -> L {
        if let Some(l) = self.levels[id as usize] {
            return l;
        }
        let l = match self.ex.levels[id as usize] {
            ex::Level::Zero => Level::Zero,
            ex::Level::Succ(a) => Level::Succ(self.level(st, a)),
            ex::Level::Max(a, b) => Level::Max(self.level(st, a), self.level(st, b)),
            ex::Level::IMax(a, b) => Level::IMax(self.level(st, a), self.level(st, b)),
            ex::Level::Param(p) => Level::Param(p),
        };
        let l = st.level(l);
        self.levels[id as usize] = Some(l);
        l
    }

    fn expr(&mut self, st: &mut Store, id: u32) -> R<E> {
        if let Some(e) = self.exprs[id as usize] {
            return Ok(e);
        }
        let n = match &self.ex.exprs[id as usize] {
            ex::Expr::BVar(i) => Node::BVar(u32::try_from(*i).map_err(|_| "bound variable index too large")?),
            ex::Expr::Sort(l) => Node::Sort(self.level(st, *l)),
            ex::Expr::Const { name, levels } => {
                let ls: Vec<L> = levels.iter().map(|&l| self.level(st, l)).collect();
                Node::Const(*name, st.list(&ls))
            }
            ex::Expr::App { f, a } => Node::App(self.expr(st, *f)?, self.expr(st, *a)?),
            ex::Expr::Lam { ty, body, .. } => Node::Lam(self.expr(st, *ty)?, self.expr(st, *body)?),
            ex::Expr::Pi { ty, body, .. } => Node::Pi(self.expr(st, *ty)?, self.expr(st, *body)?),
            ex::Expr::Let { ty, val, body, .. } => {
                Node::Let(self.expr(st, *ty)?, self.expr(st, *val)?, self.expr(st, *body)?)
            }
            ex::Expr::NatLit(s) => {
                let v: BigUint = s.parse().map_err(|_| "malformed natural-number literal")?;
                let e = st.nat(v);
                self.exprs[id as usize] = Some(e);
                return Ok(e);
            }
            ex::Expr::StrLit(s) => {
                let e = st.str_lit(s);
                self.exprs[id as usize] = Some(e);
                return Ok(e);
            }
            ex::Expr::Proj { type_name, idx, structure } => Node::Proj(
                *type_name,
                u32::try_from(*idx).map_err(|_| "projection index too large")?,
                self.expr(st, *structure)?,
            ),
        };
        let e = st.mk(n);
        self.exprs[id as usize] = Some(e);
        Ok(e)
    }
}

/// Check the declarations at indices `decls` (ascending file order) on one
/// thread. Every dependency must be in the list: anything missing is reported
/// as an unknown constant, never assumed.
///
/// Checking runs on a dedicated thread with a large stack (`STACK_SIZE`), so
/// deeply nested terms and definitional-equality checks work the same for
/// every caller. Running short of that stack is a resource error, not a crash.
pub fn check(env: &Env, decls: &[usize]) -> Result<Report, CheckError> {
    check_jobs(env, decls, 1)
}

/// [`check`] on `jobs` threads, with exactly the same verdict.
///
/// Checking runs in two phases, on any number of threads.
///
/// 1. One thread walks the declarations in file order. It converts every term
///    once, into one term store, runs every check that does not need the type
///    checker (safety, universe parameters, duplicate names), checks
///    inductive types and quotients in full (they are cheap, and their
///    recursors and rules are needed by everything after them), and records
///    every constant together with the position of the declaration that added
///    it. It stops at the first declaration that fails.
/// 2. That store is frozen and shared read-only by `jobs` threads, together
///    with the table of constants. The threads take the remaining
///    definitions, theorems, opaques and axioms in file order, each from a
///    shared counter, so each is type-checked exactly once. A declaration at
///    position `p` is checked in the environment of the constants added
///    before `p` (see `KEnv::visible`): exactly the environment the
///    sequential checker would build, apart from the builtins (`Nat`
///    arithmetic and string literals), which are also taken as they were at
///    `p`. Terms the type checker creates go into each thread's own store, on
///    top of the shared one, and are forgotten once the checks that made them
///    are over (see `forget_check_terms`). With one thread, phase 2 runs on
///    the store of phase 1 itself, unfrozen.
///
/// Verdict: the failure at the earliest position, as in sequential checking.
/// Everything before the first failure passes, so its checker sees the same
/// environment as the sequential checker would, and reaches the same
/// verdict. Declarations before `p` may still be unchecked when `p` is
/// checked, but a failure at a later position is never reported ahead of an
/// earlier one. Once a failure is known, threads stop at that position.
pub fn check_jobs(env: &Env, decls: &[usize], jobs: usize) -> Result<Report, CheckError> {
    check_with(env, decls, jobs, &[])
}

/// [`check_jobs`], except that the definitions, theorems, opaques and axioms
/// at the positions `p` with `known_good[p]` are admitted without being
/// type-checked, because an earlier run already accepted exactly that
/// declaration with exactly these dependencies (the verdict cache keys them
/// so, see `certus_core::cache`). Inductive types and quotients are always
/// checked: each run needs their recursors and rules. An empty `known_good`
/// means none.
pub fn check_with(env: &Env, decls: &[usize], jobs: usize, known_good: &[bool]) -> Result<Report, CheckError> {
    let start = Instant::now();
    if !known_good.is_empty() && known_good.len() != decls.len() {
        return Err(CheckError {
            decl: String::new(),
            msg: "internal: known_good has the wrong length".into(),
            resource: false,
        });
    }
    let known = |p: usize| known_good.get(p).copied().unwrap_or(false);
    let prep = Prep::new(env);
    let mut pre = std::thread::scope(|s| {
        let h = spawn_checker(s, "certus-check".into(), || prepare(env, decls, &prep, &known))?;
        Ok(h.join().unwrap_or_else(|p| std::panic::resume_unwind(p)))
    })?;
    let todo = pre.todo.iter().filter(|t| t.is_some()).count();
    let jobs = if todo == 0 { 0 } else { jobs.clamp(1, todo) };
    let shared = Shared {
        strs: &prep.strs,
        todo: std::mem::take(&mut pre.todo),
        consts: std::mem::take(&mut pre.consts),
        builtins: std::mem::take(&mut pre.builtins),
        next: AtomicUsize::new(0),
        first_failure: AtomicUsize::new(pre.failure.as_ref().map_or(usize::MAX, |(p, _)| *p)),
    };
    let skip = pre.term_nodes;
    let store = std::mem::take(&mut pre.store);
    let outs: Vec<Worker> = std::thread::scope(|s| {
        let shared = &shared;
        let mut handles = Vec::new();
        if jobs == 0 {
            // Nothing to do.
        } else if jobs == 1 {
            // One thread: keep using the store of phase 1, without freezing it.
            handles.push(spawn_checker(s, "certus-check-0".into(), move || run_worker(shared, store, skip))?);
        } else {
            let base = store.freeze();
            for w in 0..jobs {
                let st = Store::on(&base);
                match spawn_checker(s, format!("certus-check-{w}"), move || run_worker(shared, st, skip)) {
                    Ok(h) => handles.push(h),
                    // Fewer threads are fine (every declaration is still checked
                    // by someone), but at least one is needed.
                    Err(e) if handles.is_empty() => return Err(e),
                    Err(_) => break,
                }
            }
        }
        Ok(handles.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect())
    })?;

    let failures = pre.failure.iter().chain(outs.iter().filter_map(|w| w.failure.as_ref()));
    if let Some((_, e)) = failures.min_by_key(|(pos, _)| *pos) {
        return Err(CheckError { decl: e.decl.clone(), msg: e.msg.clone(), resource: e.resource });
    }
    let mut times: Vec<(usize, Duration)> =
        pre.times.iter().chain(outs.iter().flat_map(|w| w.times.iter())).copied().collect();
    times.sort_by_key(|a| std::cmp::Reverse(a.1));
    Ok(Report {
        checked: decls.len(),
        by_kind: pre.by_kind,
        time: start.elapsed(),
        slowest: times
            .iter()
            .take(5)
            .map(|&(i, t)| (prep.strs[env.decls[i].primary_name() as usize].clone(), t))
            .collect(),
        term_nodes: pre.term_nodes + outs.iter().map(|w| w.term_nodes).sum::<usize>(),
        native_nat_ops: pre.native_nat_ops,
        threads: outs.len().max(1),
        from_cache: decls
            .iter()
            .enumerate()
            .filter(|&(p, &i)| known(p) && !matches!(env.decls[i], Decl::Inductive(_) | Decl::Quot(_)))
            .count(),
    })
}

/// Run `f` on a new thread with the checker's stack (`STACK_SIZE`).
fn spawn_checker<'s, 'e, T: Send + 's>(
    s: &'s std::thread::Scope<'s, 'e>,
    name: String,
    f: impl FnOnce() -> T + Send + 's,
) -> Result<std::thread::ScopedJoinHandle<'s, T>, CheckError> {
    std::thread::Builder::new()
        .name(name)
        .stack_size(STACK_SIZE)
        .spawn_scoped(s, move || {
            crate::tc::set_stack_base();
            f()
        })
        .map_err(|e| CheckError {
            decl: String::new(),
            msg: format!("cannot start the checker thread: {e}"),
            resource: true,
        })
}

/// Name strings and builtin candidates, computed once.
struct Prep {
    strs: Vec<String>,
    candidates: Builtins,
}

impl Prep {
    fn new(env: &Env) -> Self {
        // Resolve the names the kernel treats specially.
        let mut strs: Vec<String> = Vec::with_capacity(env.names.len());
        for n in &env.names {
            let s = match n {
                ex::Name::Anon => String::new(),
                ex::Name::Str { pre, s } => join(&strs[*pre as usize], s),
                ex::Name::Num { pre, n } => join(&strs[*pre as usize], &n.to_string()),
            };
            strs.push(s);
        }
        let mut by_str: FxHashMap<&str, NameId> = FxHashMap::default();
        for (i, s) in strs.iter().enumerate() {
            if env.name_canon[i] as usize == i {
                by_str.entry(s.as_str()).or_insert(i as NameId);
            }
        }
        // Native Nat arithmetic is only switched on once `Nat` and each operation
        // have been checked to be the genuine ones (see `activate_nat`).
        let mut candidates = Builtins::resolve(|s| by_str.get(s).copied());
        // Lean 4.22 on expands string literals with `String.ofList` (`String.mk`
        // became a deprecated alias); earlier versions with the constructor `String.mk`.
        if let Some(n) = candidates.string_of_list
            && env.decl_of_name.contains_key(&n)
        {
            candidates.string_mk = Some(n);
        }
        drop(by_str);
        Prep { strs, candidates }
    }
}

/// What the type checker still has to check for one declaration: that `ty`
/// is a type (a proposition, if `thm`) and that `val`, if any, has type `ty`.
struct Todo {
    /// Index of the declaration in `env.decls`, and its name.
    decl: usize,
    decl_name: NameId,
    lparams: Vec<NameId>,
    ty: E,
    val: Option<E>,
    thm: bool,
}

/// The result of phase 1 (see `check_jobs`).
struct Prepared {
    store: Store,
    consts: Arc<ConstTable>,
    /// `(p, b)`: the builtins are `b` for the declarations from position `p`
    /// on (until the next entry). Starts at position 0.
    builtins: Vec<(usize, Builtins)>,
    /// `todo[p]`: what is left to check of the declaration at position `p`.
    todo: Vec<Option<Todo>>,
    /// Position and error of the first declaration that failed.
    failure: Option<(usize, CheckError)>,
    times: Vec<(usize, Duration)>,
    by_kind: Vec<(&'static str, usize)>,
    term_nodes: usize,
    native_nat_ops: usize,
}

/// Phase 1 of `check_jobs`.
fn prepare(env: &Env, decls: &[usize], prep: &Prep, known: &dyn Fn(usize) -> bool) -> Prepared {
    let strs = &prep.strs;
    let candidates = &prep.candidates;
    let mut st = Store::new();
    // Nat arithmetic and string literals are only switched on once the
    // constants they rely on have been checked (see `activate_nat` and
    // `activate_string`).
    let builtins = Builtins {
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
        ..candidates.clone()
    };
    let mut kenv = KEnv { builtins: builtins.clone(), ..KEnv::default() };
    let mut history = vec![(0, builtins)];

    let mut conv = Conv { ex: env, exprs: vec![None; env.exprs.len()], levels: vec![None; env.levels.len()] };
    let mut counts: FxHashMap<&'static str, usize> = FxHashMap::default();
    let mut hashes: Option<hash::LazyHashes> = None;
    let mut times: Vec<(usize, Duration)> = Vec::new();
    let mut todo: Vec<Option<Todo>> = Vec::with_capacity(decls.len());
    let mut failure = None;

    for (pos, &i) in decls.iter().enumerate() {
        let d = &env.decls[i];
        kenv.visible = pos;
        let t0 = Instant::now();
        let name = || strs[d.primary_name() as usize].clone();
        let (new, t) = match admit_decl(&mut st, &kenv, &mut conv, env, d) {
            Ok(x) => x,
            Err(e) => {
                failure = Some((pos, CheckError::new(name(), e)));
                break;
            }
        };
        let t = t.filter(|_| !known(pos));
        if t.is_none() {
            times.push((i, t0.elapsed()));
            todo.push(None);
        } else {
            todo.push(t.map(|t| Todo { decl: i, ..t }));
        }
        let added: Vec<NameId> = new.iter().map(|(n, _)| *n).collect();
        let mut twice = false;
        let table = Arc::get_mut(&mut kenv.consts).expect("the constant table is not shared yet");
        for (n, info) in new {
            twice |= table.insert(n, (pos, info)).is_some();
        }
        if twice {
            failure = Some((pos, CheckError { decl: name(), msg: "constant declared twice".into(), resource: false }));
            break;
        }
        kenv.visible = pos + 1;
        for n in added {
            activate_nat(&mut st, &mut kenv, candidates, n, strs, env, &mut hashes);
            activate_string(&mut st, &mut kenv, candidates, n);
        }
        if history.last().is_some_and(|(_, b)| *b != kenv.builtins) {
            history.push((pos + 1, kenv.builtins.clone()));
        }
        *counts.entry(d.kind()).or_default() += 1;
    }

    let mut by_kind: Vec<(&'static str, usize)> = counts.into_iter().collect();
    by_kind.sort();
    Prepared {
        term_nodes: st.num_nodes(),
        native_nat_ops: kenv.builtins.nat_ops.len(),
        store: st,
        consts: kenv.consts,
        builtins: history,
        todo,
        failure,
        times,
        by_kind,
    }
}

/// State shared by the threads of phase 2.
struct Shared<'a> {
    strs: &'a [String],
    todo: Vec<Option<Todo>>,
    consts: Arc<ConstTable>,
    builtins: Vec<(usize, Builtins)>,
    /// The next position to take.
    next: AtomicUsize,
    /// Earliest position known to fail (`usize::MAX`: none yet).
    first_failure: AtomicUsize,
}

/// What one thread of phase 2 found.
struct Worker {
    /// Position in `decls` and error of the first failure this worker met.
    failure: Option<(usize, CheckError)>,
    /// Time spent on each declaration this worker type-checked.
    times: Vec<(usize, Duration)>,
    /// Terms created by this worker.
    term_nodes: usize,
}

/// Phase 2 of `check_jobs`, on store `st`, which holds the `skip` terms of
/// phase 1.
fn run_worker(shared: &Shared, mut st: Store, skip: usize) -> Worker {
    let mut kenv = KEnv { consts: shared.consts.clone(), visible: 0, builtins: Builtins::default() };
    let mut era = usize::MAX;
    let mut times: Vec<(usize, Duration)> = Vec::new();
    let mut failure = None;
    let mut peak = st.num_nodes();
    loop {
        // Positions are taken in increasing order, so every position before
        // a failure is taken (and checked) by some worker.
        let pos = shared.next.fetch_add(1, Ordering::Relaxed);
        if pos >= shared.todo.len() || pos >= shared.first_failure.load(Ordering::Relaxed) {
            break;
        }
        let Some(t) = &shared.todo[pos] else { continue };
        let e = shared.builtins.partition_point(|(p, _)| *p <= pos) - 1;
        if e != era {
            kenv.builtins = shared.builtins[e].1.clone();
            era = e;
        }
        kenv.visible = pos;
        let t0 = Instant::now();
        let r = check_todo(&mut TC::new(&mut st, &kenv, t.lparams.clone()), t);
        if let Err(e) = r {
            failure = Some((pos, CheckError::new(shared.strs[t.decl_name as usize].clone(), e)));
            break;
        }
        // Everything in this worker's own store was made by checks that are
        // over: the shared base holds every converted term.
        peak = peak.max(st.num_nodes());
        forget_check_terms(&mut st, skip);
        times.push((t.decl, t0.elapsed()));
    }
    if let Some((pos, _)) = &failure {
        shared.first_failure.fetch_min(*pos, Ordering::Relaxed);
    }
    Worker { failure, times, term_nodes: peak.max(st.num_nodes()) - skip }
}

/// Fingerprints of the genuine `Nat` operations the kernel computes natively,
/// one table per supported Lean release (see [`closure_fingerprint`]).
///
/// Soundness: a fingerprint covers the operation's definition *and* its whole
/// dependency closure (every constant its type or value mentions,
/// transitively, by content), so a match means the export contains exactly
/// Lean's own definitions of the operation, of `Nat`, `Bool` and of every
/// helper (`Nat.add.match_1`, `Nat.brecOn`, `WellFounded.fix`, ...). Those
/// definitions compute what the native code computes, so native evaluation
/// cannot prove anything plain unfolding would not. Anything else, including
/// a release not listed here, is checked by plain unfolding: slower, never
/// unsound.
///
/// To add a release, check one of its exports that uses the operations
/// (e.g. the Arena's `init-prelude`) with `CERTUS_PRINT_FINGERPRINTS=1` and
/// paste the printed lines here.
const GENUINE_NAT_OPS: &[(&str, &[(&str, &str)])] = &[
    // From the Arena round 2026-09 exports (`init-prelude`, `grind-ring-5`,
    // `magma-list-deep-n21`). The other operations appear in none of them, so
    // in 4.29 exports they are unfolded until someone pins them.
    (
        "4.29.1",
        &[
            ("Nat.add", "5a7c173a0ef55a6c20c18f4134cf8a044b2a498a7e87a05991972ac8ab65bfe2"),
            ("Nat.sub", "286103e79ab8e57b87e2cd94aa561643bf34680024e58ea45730913556f621f9"),
            ("Nat.mul", "9f47cfc0e7e12a16d63fe1c1ef0fe0e7f413a17edda9737a4138936553e3c222"),
            ("Nat.div", "6c3e73937c8ab8efb3235a0c007f4d49cdd755a9fda8f1e57761451e43eb145d"),
            ("Nat.mod", "b0c74bc7b02fd6d7d8b089ddb38164a2990c922ae85af49f5ca02c2fdcbba87a"),
            ("Nat.beq", "ed417e90b6a77a347d879d605ef9416a712d29f4ed22fed691ee7df6b3ca5ce0"),
            ("Nat.ble", "23583a3f40d1206cdf8badda9c992906d382326be53fcff7fdec35ff5cbba93a"),
            ("Nat.land", "a8ac2d209146e080e190045b3a7e411c3f224034a592d02160d42b12afbbd4d9"),
            ("Nat.shiftRight", "70549bca8ad52a720ed98eb067acd50c6e83ac883d8e80cf951e8314eecbaad6"),
            ("Nat.pow", "c594a43937f7c2b1b392748209c03145c56b9cb3d53dc75767690b9445bcc826"),
        ],
    ),
    // From `leanexport` of `theorem t : Nat.<op> .. = .. := rfl` for every
    // operation (identical in the Arena live exports and `sum_explicit.cert`).
    (
        "4.36.0",
        &[
            ("Nat.add", "f8ef476856ad3603f71be6defdc47a8fe84e89168f558ab70ab10fbd47fa6196"),
            ("Nat.sub", "ffcb51b009dbf289d364bb885865c42daed866f79bb9330fb387998506ab84ed"),
            ("Nat.mul", "ad719d942f5cbd7b67f78c701a84cf8d26fb3dea917f592abe6a53528b13c09d"),
            ("Nat.div", "e5da2ba5bb0e1a6990e0dfe92606fc4f77203f59cbc91f385f266ee484cd539b"),
            ("Nat.mod", "0d9f53827d8b945045310354688bd368fc7d9f204cb6c619dd7f8e0acdfc0498"),
            ("Nat.gcd", "1fa7a7606ed99e6bda63f82d01f4843efea5175f17c0820b59272d6068b990f1"),
            ("Nat.beq", "6fe74250c23139bd43e4804a7bb4fbcf042accb06252329683c33e37e6fb2db4"),
            ("Nat.ble", "100b9da55221cb1691f37b545928402dc81d629c049b65176de2e0a89116d508"),
            ("Nat.land", "30370380f3846328114b4fed245068a8a9264becefafa6e2de57bf9c9cde9bbf"),
            ("Nat.lor", "8a8aff47600abd699279e4dd00afee5fb36ba8f3b1372d23b679a1f57afcffe4"),
            ("Nat.xor", "dc02a85b47b89d8aaf7802826541575f9da98c987f7dffa00f2cf6a96f1b922a"),
            ("Nat.shiftLeft", "5fb4c94d70a84775689546fc75340265c0e8bfcafc77d8e295ad3fdb6d152f52"),
            ("Nat.shiftRight", "92c75d99ad7940a20744a0cf22467dda16d156eb685ca172d892a73cb51dfe40"),
            ("Nat.pow", "11c1ab2525a089ebb908656fefe5916dfbf38390bcd040231abf2ab3c1a3a700"),
            ("Nat.log2", "1980f5a8b660285ca3cddaab6ddfe9b7c9d332e31749e76cbdb33025b188f3d2"),
        ],
    ),
];

/// Domain separation for [`closure_fingerprint`].
const CLOSURE_FP_CONTEXT: &str = "certus genuine Nat operation closure 2026-11-21";

/// Fingerprint of declaration `decl` together with everything it depends on:
/// the alpha-normal (spec v1) hashes of all declarations in its dependency
/// closure, sorted, so the result depends neither on the export order nor on
/// binder names, only on content. `None` if the closure is incomplete or
/// contains anything unsafe or partial.
fn closure_fingerprint(env: &Env, hashes: &mut hash::LazyHashes, decl: usize) -> Option<String> {
    let c = deps::closure(env, &[decl]);
    if !c.missing.is_empty() || !c.unsafe_or_partial.is_empty() {
        return None;
    }
    let mut hs: Vec<hash::Hash> = c.decls.iter().map(|&j| hashes.decl(j)).collect();
    hs.sort_unstable();
    let mut h = blake3::Hasher::new_derive_key(CLOSURE_FP_CONTEXT);
    h.update(&(hs.len() as u64).to_le_bytes());
    for x in &hs {
        h.update(x);
    }
    Some(hash::hex(h.finalize().as_bytes()))
}

fn activate_nat<'e>(
    st: &mut Store,
    kenv: &mut KEnv,
    cand: &Builtins,
    n: NameId,
    strs: &[String],
    env: &'e Env,
    hashes: &mut Option<hash::LazyHashes<'e>>,
) {
    fn get(kenv: &KEnv, n: Option<NameId>) -> Option<&ConstInfo> {
        n.and_then(|n| kenv.get(n))
    }
    if Some(n) == cand.nat {
        // `Nat : Type` with exactly `zero : Nat` and `succ : Nat → Nat`.
        let (Some(nat), Some(z), Some(s)) = (get(kenv, cand.nat), get(kenv, cand.nat_zero), get(kenv, cand.nat_succ))
        else {
            return;
        };
        let (nat_n, z_n, s_n) = (cand.nat.unwrap(), cand.nat_zero.unwrap(), cand.nat_succ.unwrap());
        let one = st.succ(st.zero);
        let type0 = st.sort(one);
        let nat_c = st.cnst(nat_n, &[]);
        let nat_to_nat = st.mk(Node::Pi(nat_c, nat_c));
        let standard = matches!(&nat.kind, Kind::Induct { num_params: 0, num_indices: 0, ctors, .. } if ctors.as_slice() == [z_n, s_n])
            && nat.lparams.is_empty()
            && nat.ty == type0
            && z.ty == nat_c
            && s.ty == nat_to_nat;
        if standard {
            kenv.builtins.nat = cand.nat;
            kenv.builtins.nat_zero = cand.nat_zero;
            kenv.builtins.nat_succ = cand.nat_succ;
        }
        return;
    }
    let Some(&(_, op)) = cand.nat_ops.iter().find(|(m, _)| *m == n) else { return };
    if kenv.builtins.nat.is_none() || !matches!(kenv.get(n).map(|c| c.kind.clone()), Some(Kind::Def { .. })) {
        return;
    }
    let Some(&decl) = env.decl_of_name.get(&n) else { return };
    let hashes = hashes.get_or_insert_with(|| hash::LazyHashes::new(env, hash::Mode::AlphaNormal));
    let Some(fp) = closure_fingerprint(env, hashes, decl) else { return };
    let name = &strs[n as usize];
    if std::env::var_os("CERTUS_PRINT_FINGERPRINTS").is_some() {
        eprintln!("(\"{name}\", \"{fp}\"),");
    }
    let genuine = GENUINE_NAT_OPS.iter().flat_map(|(_, ops)| ops.iter()).any(|(s, f)| s == name && *f == fp);
    if genuine {
        kenv.builtins.nat_ops.push((n, op));
    }
}

/// Switch on string literals once all the constants their expansion
/// `String.ofList [Char.ofNat c₁, …]` uses are present with their standard
/// shapes, so that a literal's expansion is well typed and has type `String`:
///
/// - `List.{u} : Type u → Type u`, an inductive type whose constructors are
///   exactly `List.nil.{u} : {α : Type u} → List α` and
///   `List.cons.{u} : {α : Type u} → α → List α → List α`;
/// - `Char : Type` and `String : Type`, inductive types without parameters or
///   indices;
/// - `Char.ofNat : Nat → Char`, a definition (requires the verified `Nat`);
/// - the expansion function `String.ofList : List Char → String`, a definition
///   (Lean 4.22 on, where `String` wraps a `ByteArray`), or before that
///   `String.mk : List Char → String`, the constructor of `String`.
///
/// Until then, string literals are rejected.
fn activate_string(st: &mut Store, kenv: &mut KEnv, cand: &Builtins, n: NameId) {
    let names = [cand.string, cand.string_mk, cand.char, cand.char_of_nat, cand.list_nil, cand.list_cons];
    if kenv.builtins.string.is_some() || !names.contains(&Some(n)) {
        return;
    }
    let (Some(string_n), Some(mk_n), Some(char_n), Some(of_nat_n), Some(nil_n), Some(cons_n), Some(nat_n)) =
        (cand.string, cand.string_mk, cand.char, cand.char_of_nat, cand.list_nil, cand.list_cons, kenv.builtins.nat)
    else {
        return;
    };
    let get = |n: NameId| kenv.get(n);
    let (Some(string), Some(mk), Some(chr), Some(of_nat), Some(nil), Some(cons)) =
        (get(string_n), get(mk_n), get(char_n), get(of_nat_n), get(nil_n), get(cons_n))
    else {
        return;
    };
    // `List`: the inductive type of both constructors.
    let Kind::Ctor { induct: list_n, cidx: 0, num_params: 1, num_fields: 0 } = nil.kind else { return };
    if !matches!(cons.kind, Kind::Ctor { induct, cidx: 1, num_params: 1, num_fields: 2 } if induct == list_n) {
        return;
    }
    let Some(list) = kenv.get(list_n) else { return };
    let Kind::Induct { num_params: 1, num_indices: 0, ctors, .. } = &list.kind else { return };
    let ([u_n], true) = (list.lparams.as_slice(), nil.lparams == list.lparams && cons.lparams == list.lparams) else {
        return;
    };
    if ctors.as_slice() != [nil_n, cons_n] {
        return;
    }
    let u = st.level(Level::Param(*u_n));
    let type_u = {
        let su = st.succ(u);
        st.sort(su)
    };
    let list_u = st.cnst(list_n, &[u]);
    let list_ty = st.mk(Node::Pi(type_u, type_u));
    // {α : Type u} → List α
    let b0 = st.bvar(0);
    let list_b0 = st.app(list_u, b0);
    let nil_ty = st.mk(Node::Pi(type_u, list_b0));
    // {α : Type u} → α → List α → List α
    let b1 = st.bvar(1);
    let b2 = st.bvar(2);
    let list_b1 = st.app(list_u, b1);
    let list_b2 = st.app(list_u, b2);
    let tail = st.mk(Node::Pi(list_b1, list_b2));
    let head = st.mk(Node::Pi(b0, tail));
    let cons_ty = st.mk(Node::Pi(type_u, head));
    if list.ty != list_ty || nil.ty != nil_ty || cons.ty != cons_ty {
        return;
    }
    // `Char` and `String`: types without parameters or indices.
    let type0 = {
        let one = st.succ(st.zero);
        st.sort(one)
    };
    for t in [&chr, &string] {
        if !t.lparams.is_empty()
            || t.ty != type0
            || !matches!(t.kind, Kind::Induct { num_params: 0, num_indices: 0, .. })
        {
            return;
        }
    }
    // `Char.ofNat : Nat → Char` and `String.mk : List Char → String`.
    let nat_c = st.cnst(nat_n, &[]);
    let char_c = st.cnst(char_n, &[]);
    let string_c = st.cnst(string_n, &[]);
    let list0 = st.cnst(list_n, &[st.zero]);
    let list_char = st.app(list0, char_c);
    let of_nat_ty = st.mk(Node::Pi(nat_c, char_c));
    let mk_ty = st.mk(Node::Pi(list_char, string_c));
    if !of_nat.lparams.is_empty() || of_nat.ty != of_nat_ty || !matches!(of_nat.kind, Kind::Def { .. }) {
        return;
    }
    let mk_ok = match mk.kind {
        Kind::Def { .. } => true,
        Kind::Ctor { induct, num_params: 0, num_fields: 1, .. } => induct == string_n,
        _ => false,
    };
    if !mk.lparams.is_empty() || mk.ty != mk_ty || !mk_ok {
        return;
    }
    let b = &mut kenv.builtins;
    (b.string, b.string_mk, b.char, b.char_of_nat, b.list_nil, b.list_cons) =
        (cand.string, cand.string_mk, cand.char, cand.char_of_nat, cand.list_nil, cand.list_cons);
}

fn join(pre: &str, s: &str) -> String {
    if pre.is_empty() { s.to_string() } else { format!("{pre}.{s}") }
}

fn distinct(ps: &[NameId]) -> R<()> {
    for (i, p) in ps.iter().enumerate() {
        if ps[..i].contains(p) {
            return Err("duplicate universe parameter".into());
        }
    }
    Ok(())
}

fn hints_of(v: &serde_json::Value) -> R<Hints> {
    match v {
        serde_json::Value::String(s) if s == "opaque" => Ok(Hints::Opaque),
        serde_json::Value::String(s) if s == "abbrev" => Ok(Hints::Abbrev),
        serde_json::Value::Object(m) if m.len() == 1 => match m.get("regular").and_then(|h| h.as_u64()) {
            Some(h) => Ok(Hints::Regular(u32::try_from(h).unwrap_or(u32::MAX))),
            None => Err("malformed reducibility hints".into()),
        },
        _ => Err("malformed reducibility hints".into()),
    }
}

/// Check that `ty` is a type, under fresh universe parameters.
/// A finished check leaves nothing that refers to the terms it created: the
/// type checker and its caches are gone, and the declaration's own terms (and
/// everything else outside the type checker: constants, converted terms, the
/// remaining todo) were made before the check started. So every term from
/// `mark` on can be forgotten once the checks that made them are over
/// (`Store::collect` with no roots also drops the store's cached
/// instantiations of them). Each collection scans those cached instantiations,
/// so it waits until there are this many such terms.
const ROLLBACK_MIN: usize = 1 << 16;

fn forget_check_terms(st: &mut Store, mark: usize) {
    if st.num_nodes() - mark >= crate::tc::collect_threshold(ROLLBACK_MIN) {
        st.collect(E(mark as u32), &[]);
    }
}

fn check_type(tc: &mut TC, ty: E) -> R<L> {
    if tc.st.info(ty).lbr != 0 {
        return Err("type has loose bound variables".into());
    }
    let s = tc.infer(ty, true)?;
    tc.ensure_sort(s)
}

fn check_value(tc: &mut TC, val: E, ty: E) -> R<()> {
    if tc.st.info(val).lbr != 0 {
        return Err("value has loose bound variables".into());
    }
    let vt = tc.infer(val, true)?;
    if !tc.is_def_eq(vt, ty)? {
        return Err("value does not have the declared type".into());
    }
    Ok(())
}

/// The type checker's part of checking a definition, theorem, opaque or axiom.
fn check_todo(tc: &mut TC, t: &Todo) -> R<()> {
    let l = check_type(tc, t.ty)?;
    if t.thm && !tc.st.is_zero(l) {
        return Err("theorem type is not a proposition".into());
    }
    if let Some(val) = t.val {
        check_value(tc, val, t.ty)?;
    }
    Ok(())
}

/// The constants a declaration adds, and what is left for the type checker.
type Admitted = (Vec<(NameId, ConstInfo)>, Option<Todo>);

/// Phase 1 of checking one declaration (see `check_jobs`): convert its terms
/// and run every check that does not need the type checker; check inductive
/// types and quotients in full. Returns the constants it adds and, for a
/// definition, theorem, opaque or axiom, what is left for the type checker.
fn admit_decl(st: &mut Store, kenv: &KEnv, conv: &mut Conv, env: &Env, d: &Decl) -> R<Admitted> {
    for n in d.defined_names() {
        if kenv.contains(n) {
            return Err("constant declared twice".into());
        }
    }
    let info = |lparams: &Vec<NameId>, ty, kind| ConstInfo { lparams: lparams.clone(), ty, kind };
    let todo = |lparams: &Vec<NameId>, ty, val, thm| {
        Some(Todo { decl: 0, decl_name: d.primary_name(), lparams: lparams.clone(), ty, val, thm })
    };
    let (new, t) = match d {
        Decl::Axiom(a) => {
            if a.is_unsafe {
                return Err("unsafe axioms are not accepted".into());
            }
            distinct(&a.level_params)?;
            let ty = conv.expr(st, a.r#type)?;
            (vec![(a.name, info(&a.level_params, ty, Kind::Axiom))], todo(&a.level_params, ty, None, false))
        }
        Decl::Def(a) => {
            if a.safety != "safe" {
                return Err(format!("{} definitions are not accepted", a.safety).into());
            }
            distinct(&a.level_params)?;
            let hints = hints_of(&a.hints)?;
            let ty = conv.expr(st, a.r#type)?;
            let val = conv.expr(st, a.value)?;
            (
                vec![(a.name, info(&a.level_params, ty, Kind::Def { val, hints }))],
                todo(&a.level_params, ty, Some(val), false),
            )
        }
        Decl::Thm(a) => {
            distinct(&a.level_params)?;
            let ty = conv.expr(st, a.r#type)?;
            let val = conv.expr(st, a.value)?;
            (vec![(a.name, info(&a.level_params, ty, Kind::Thm { val }))], todo(&a.level_params, ty, Some(val), true))
        }
        Decl::Opaque(a) => {
            if a.is_unsafe {
                return Err("unsafe opaque constants are not accepted".into());
            }
            distinct(&a.level_params)?;
            let ty = conv.expr(st, a.r#type)?;
            let val = conv.expr(st, a.value)?;
            (vec![(a.name, info(&a.level_params, ty, Kind::Opaque))], todo(&a.level_params, ty, Some(val), false))
        }
        Decl::Quot(a) => {
            distinct(&a.level_params)?;
            let kind = match a.kind.as_str() {
                "type" => QuotKind::Type,
                "ctor" => QuotKind::Ctor,
                "lift" => QuotKind::Lift,
                "ind" => QuotKind::Ind,
                k => return Err(format!("unknown quotient kind {k:?}").into()),
            };
            let b = &kenv.builtins;
            let expected_name = match kind {
                QuotKind::Type => b.quot,
                QuotKind::Ctor => b.quot_mk,
                QuotKind::Lift => b.quot_lift,
                QuotKind::Ind => b.quot_ind,
            };
            if expected_name != Some(a.name) {
                return Err("quotient constant has the wrong name".into());
            }
            let ty = conv.expr(st, a.r#type)?;
            let mut tc = TC::new(st, kenv, a.level_params.clone());
            check_quot(&mut tc, kind, &a.level_params, ty)?;
            (vec![(a.name, info(&a.level_params, ty, Kind::Quot(kind)))], None)
        }
        Decl::Inductive(b) => {
            let mut blk = Block { types: Vec::new(), ctors: Vec::new(), recs: Vec::new() };
            for t in &b.types {
                blk.types.push(inductive::IndType {
                    name: t.name,
                    lparams: t.level_params.clone(),
                    ty: conv.expr(st, t.r#type)?,
                    num_params: small(t.num_params)?,
                    num_indices: small(t.num_indices)?,
                    all: t.all.clone(),
                    ctors: t.ctors.clone(),
                    num_nested: small(t.num_nested)?,
                    is_rec: t.is_rec,
                    is_unsafe: t.is_unsafe,
                    is_reflexive: t.is_reflexive,
                });
            }
            for c in &b.ctors {
                blk.ctors.push(inductive::Ctor {
                    name: c.name,
                    lparams: c.level_params.clone(),
                    ty: conv.expr(st, c.r#type)?,
                    induct: c.induct,
                    cidx: small(c.cidx)?,
                    num_params: small(c.num_params)?,
                    num_fields: small(c.num_fields)?,
                    is_unsafe: c.is_unsafe,
                });
            }
            for r in &b.recs {
                let mut rules = Vec::new();
                for rule in &r.rules {
                    rules.push(RecRule {
                        ctor: rule.ctor,
                        nfields: small(rule.nfields)?,
                        rhs: conv.expr(st, rule.rhs)?,
                    });
                }
                blk.recs.push(inductive::Rec {
                    name: r.name,
                    lparams: r.level_params.clone(),
                    ty: conv.expr(st, r.r#type)?,
                    all: r.all.clone(),
                    num_params: small(r.num_params)?,
                    num_indices: small(r.num_indices)?,
                    num_motives: small(r.num_motives)?,
                    num_minors: small(r.num_minors)?,
                    rules,
                    k: r.k,
                    is_unsafe: r.is_unsafe,
                });
            }
            let mut tc = TC::new(st, kenv, Vec::new());
            (inductive::check_block(&mut tc, &env.names, &blk)?, None)
        }
    };
    Ok((new, t))
}

fn small(v: u64) -> R<u32> {
    u32::try_from(v).map_err(|_| "number too large".into())
}
