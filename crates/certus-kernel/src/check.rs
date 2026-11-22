//! Driver: convert exported declarations to kernel terms and check them in
//! dependency order, adding each to the environment only once it passes.

use crate::env::{Builtins, ConstInfo, Hints, KEnv, Kind, QuotKind, RecRule};
use crate::inductive::{self, Block};
use crate::quot::check_quot;
use crate::tc::{R, TC};
use crate::term::{E, L, Level, Node, Store};
use certus_core::export::{self as ex, Decl, Env, NameId};
use num_bigint::BigUint;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

#[derive(Debug)]
pub struct CheckError {
    pub decl: String,
    pub msg: String,
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

/// Check the declarations at indices `decls` (ascending file order). Every
/// dependency must be in the list: anything missing is reported as an
/// unknown constant, never assumed.
pub fn check(env: &Env, decls: &[usize]) -> Result<Report, CheckError> {
    let start = Instant::now();
    let mut st = Store::new();
    let mut kenv = KEnv::default();

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
    // Likewise string literals are only typed and expanded once `String`,
    // `String.mk`, `Char`, `Char.ofNat`, `List.nil` and `List.cons` have been
    // checked to have their standard shapes (see `activate_string`).
    kenv.builtins = Builtins {
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

    let mut conv = Conv { ex: env, exprs: vec![None; env.exprs.len()], levels: vec![None; env.levels.len()] };
    let mut counts: FxHashMap<&'static str, usize> = FxHashMap::default();
    let mut times: Vec<(usize, Duration)> = Vec::new();

    for &i in decls {
        let d = &env.decls[i];
        let t0 = Instant::now();
        let name = || strs[d.primary_name() as usize].clone();
        let new = check_decl(&mut st, &kenv, &mut conv, env, d).map_err(|msg| CheckError { decl: name(), msg })?;
        let added: Vec<NameId> = new.iter().map(|(n, _)| *n).collect();
        for (n, info) in new {
            if kenv.consts.insert(n, Arc::new(info)).is_some() {
                return Err(CheckError { decl: name(), msg: "constant declared twice".into() });
            }
        }
        for n in added {
            activate_nat(&mut st, &mut kenv, &candidates, n, &strs);
            activate_string(&mut st, &mut kenv, &candidates, n);
        }
        *counts.entry(d.kind()).or_default() += 1;
        times.push((i, t0.elapsed()));
    }

    times.sort_by_key(|a| std::cmp::Reverse(a.1));
    let mut by_kind: Vec<(&'static str, usize)> = counts.into_iter().collect();
    by_kind.sort();
    Ok(Report {
        checked: decls.len(),
        by_kind,
        time: start.elapsed(),
        slowest: times.iter().take(5).map(|&(i, t)| (strs[env.decls[i].primary_name() as usize].clone(), t)).collect(),
        term_nodes: st.num_nodes(),
        native_nat_ops: kenv.builtins.nat_ops.len(),
    })
}

/// Fingerprints of the genuine definitions (type and value) of the `Nat`
/// operations the kernel computes natively, as exported by Lean 4.36.
/// A definition with any other fingerprint is checked by plain unfolding.
const GENUINE_NAT_OPS: &[(&str, &str)] = &[
    ("Nat.add", "c68c7439421c1283ba8c14ab743cc505364d05085debacf408613fd4503c68e6"),
    ("Nat.sub", "a7d8706199deff5e03df340f359c8ee81c32934cf077e60ddeebecff5e340bb5"),
    ("Nat.mul", "86c7588a6d697790d91d4e14871e4c6db69ddd7e8e30e0db28916787c593be47"),
    ("Nat.div", "e1c5b205a36cbe96e5ea5ffea352639d5b6f90d2b065773da7d1fcd4e68736eb"),
    ("Nat.mod", "b2b31b3348dc57e5959961d5b0c78d4ca93775966d3828f7be723e8a61d66bb6"),
    ("Nat.gcd", "ff6bfed41eee27a12b5f0152b8c5ef08849ecd3258a80746141021709d1046a2"),
    ("Nat.beq", "d95a94a6f826e8e39cb1ed5ac185226b6dd7329a9ea66680826814d3ca173fdf"),
    ("Nat.ble", "df488cf053ffc6a5312f8d5e2cfb73aabbdf1ac65e785c7e608104b080f41116"),
    ("Nat.land", "9702e161e31b7a814cb8d557c08f74171627e25089c3fe89d435e3f2d905abc1"),
    ("Nat.lor", "034c52eb295749a016a7e0800541ad1f076dfcbb057cde9f70703d79a896493b"),
    ("Nat.xor", "92f61f733666d5039cad909dd9153f97f0a060d5b2edfdddfba972c773fd4d94"),
    ("Nat.shiftLeft", "330a5645b7295feb9495421985d7ffb6c446c44bd0e3a7283ee0f36a173c0b98"),
    ("Nat.shiftRight", "9f80dec2f26c52f6928b2b119e2919d94e08de0a1a7b6e3c5fd4143fcedc069d"),
    ("Nat.pow", "993d5719ad127a229165d370790118f80d020f7dce2de97e0af3a9d81249af12"),
    ("Nat.log2", "a55606bcd21cb68a9965bd1049a165d831b7a0fc5137438b3fe35f073cb0f597"),
];

fn activate_nat(st: &mut Store, kenv: &mut KEnv, cand: &Builtins, n: NameId, strs: &[String]) {
    let get = |kenv: &KEnv, n: Option<NameId>| n.and_then(|n| kenv.get(n));
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
    if kenv.builtins.nat.is_none() {
        return;
    }
    let Some(c) = kenv.get(n) else { return };
    let Kind::Def { val, .. } = c.kind else { return };
    let name = |i: NameId| strs[i as usize].clone();
    let mut h = blake3::Hasher::new();
    h.update(&st.fingerprint(c.ty, &name)).update(&st.fingerprint(val, &name));
    let fp: String = h.finalize().as_bytes().iter().map(|b| format!("{b:02x}")).collect();
    if std::env::var_os("CERTUS_PRINT_FINGERPRINTS").is_some() {
        eprintln!("(\"{}\", \"{fp}\"),", strs[n as usize]);
    }
    if GENUINE_NAT_OPS.iter().any(|(s, f)| *s == strs[n as usize] && *f == fp) {
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

fn check_decl(st: &mut Store, kenv: &KEnv, conv: &mut Conv, env: &Env, d: &Decl) -> R<Vec<(NameId, ConstInfo)>> {
    for n in d.defined_names() {
        if kenv.consts.contains_key(&n) {
            return Err("constant declared twice".into());
        }
    }
    let info = |lparams: &Vec<NameId>, ty, kind| ConstInfo { lparams: lparams.clone(), ty, kind };
    Ok(match d {
        Decl::Axiom(a) => {
            if a.is_unsafe {
                return Err("unsafe axioms are not accepted".into());
            }
            distinct(&a.level_params)?;
            let ty = conv.expr(st, a.r#type)?;
            let mut tc = TC::new(st, kenv, a.level_params.clone());
            check_type(&mut tc, ty)?;
            vec![(a.name, info(&a.level_params, ty, Kind::Axiom))]
        }
        Decl::Def(a) => {
            if a.safety != "safe" {
                return Err(format!("{} definitions are not accepted", a.safety));
            }
            distinct(&a.level_params)?;
            let hints = hints_of(&a.hints)?;
            let ty = conv.expr(st, a.r#type)?;
            let val = conv.expr(st, a.value)?;
            let mut tc = TC::new(st, kenv, a.level_params.clone());
            check_type(&mut tc, ty)?;
            check_value(&mut tc, val, ty)?;
            vec![(a.name, info(&a.level_params, ty, Kind::Def { val, hints }))]
        }
        Decl::Thm(a) => {
            distinct(&a.level_params)?;
            let ty = conv.expr(st, a.r#type)?;
            let val = conv.expr(st, a.value)?;
            let mut tc = TC::new(st, kenv, a.level_params.clone());
            let l = check_type(&mut tc, ty)?;
            if !tc.st.is_zero(l) {
                return Err("theorem type is not a proposition".into());
            }
            check_value(&mut tc, val, ty)?;
            vec![(a.name, info(&a.level_params, ty, Kind::Thm { val }))]
        }
        Decl::Opaque(a) => {
            if a.is_unsafe {
                return Err("unsafe opaque constants are not accepted".into());
            }
            distinct(&a.level_params)?;
            let ty = conv.expr(st, a.r#type)?;
            let val = conv.expr(st, a.value)?;
            let mut tc = TC::new(st, kenv, a.level_params.clone());
            check_type(&mut tc, ty)?;
            check_value(&mut tc, val, ty)?;
            vec![(a.name, info(&a.level_params, ty, Kind::Opaque))]
        }
        Decl::Quot(a) => {
            distinct(&a.level_params)?;
            let kind = match a.kind.as_str() {
                "type" => QuotKind::Type,
                "ctor" => QuotKind::Ctor,
                "lift" => QuotKind::Lift,
                "ind" => QuotKind::Ind,
                k => return Err(format!("unknown quotient kind {k:?}")),
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
            vec![(a.name, info(&a.level_params, ty, Kind::Quot(kind)))]
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
            inductive::check_block(&mut tc, &env.names, &blk)?
        }
    })
}

fn small(v: u64) -> R<u32> {
    u32::try_from(v).map_err(|_| "number too large".into())
}
