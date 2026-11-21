use certus_core::pretty::{Options, Printer, expr_to_string, find_const, level_to_string, statement};
use certus_core::{Env, parse};
use serde_json::{Value, json};
use std::collections::HashMap;

const TINY: &str = include_str!("fixtures/tiny.ndjson");
const SUM: &str = include_str!("../../certus-kernel/tests/fixtures/sum_explicit.cert.ndjson");

fn env_of(s: &str) -> Env {
    parse(s.as_bytes()).expect("fixture parses")
}

fn show(env: &Env, name: &str, opts: Options) -> String {
    let c = find_const(env, name).unwrap_or_else(|| panic!("{name} not found"));
    statement(env, &c, opts)
}

// ---- Real exports ----

#[test]
fn sum_formula_statement() {
    let env = env_of(SUM);
    assert_eq!(show(&env, "sum_formula_explicit", Options::NOTATION), "∀ (n : Nat), 2 * sumTo n = n * (n + 1)");
    assert_eq!(
        show(&env, "sum_formula_explicit", Options::RAW),
        "∀ (n : Nat), Eq.{1} Nat \
         (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (sumTo n)) \
         (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n \
         (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))"
    );
}

#[test]
fn real_export_statements() {
    let env = env_of(SUM);
    let n = Options::NOTATION;
    assert_eq!(show(&env, "Nat.add_assoc", n), "∀ (n : Nat) (m : Nat) (k : Nat), n + m + k = n + (m + k)");
    assert_eq!(show(&env, "Nat.right_distrib", n), "∀ (n : Nat) (m : Nat) (k : Nat), (n + m) * k = n * k + m * k");
    assert_eq!(show(&env, "sumTo", n), "Nat → Nat");
    assert_eq!(show(&env, "propext", n), "∀ {a : Prop} {b : Prop}, (a ↔ b) → a = b");
    assert_eq!(show(&env, "eq_self", n), "∀ {α : Sort u_1} (a : α), (a = a) = True");
    assert_eq!(show(&env, "instHAdd", n), "∀ {α : Type u_1} [Add α], HAdd α α α");
    assert_eq!(
        show(&env, "HAdd.hAdd", n),
        "∀ {α : Type u} {β : Type v} {γ : outParam (Type w)} [self : HAdd α β γ], α → β → γ"
    );
    // Constructors and recursors of inductive blocks are found by name.
    assert_eq!(show(&env, "Iff.intro", n), "∀ {a : Prop} {b : Prop}, (a → b) → (b → a) → (a ↔ b)");
    assert_eq!(find_const(&env, "Iff.intro").unwrap().kind, "ctor");
    // Shadowed hygienic binders stay distinguishable.
    assert_eq!(
        show(&env, "Eq.rec", n),
        "∀ {α : Sort u_1} {a✝ : α} {motive : ∀ (a✝ : α), a✝¹ = a✝ → Sort u}, \
         motive a✝ (Eq.refl a✝) → ∀ {a✝ : α} (t : a✝¹ = a✝), motive a✝ t"
    );
}

#[test]
fn tiny_fixture() {
    let env = env_of(TINY);
    for o in [Options::RAW, Options::NOTATION] {
        assert_eq!(show(&env, "myThm", o), "P");
        assert_eq!(show(&env, "P", o), "Prop");
    }
    assert_eq!(find_const(&env, "myThm").unwrap().kind, "thm");
    assert!(find_const(&env, "nope").is_none());
}

#[test]
fn printing_is_deterministic() {
    let a: Vec<String> = (0..2)
        .map(|_| {
            let env = env_of(SUM);
            let mut p = Printer::new(&env, Options::NOTATION);
            env.decls.iter().flat_map(|d| d.roots()).map(|e| p.expr(e)).collect::<Vec<_>>().join("\n")
        })
        .collect();
    assert_eq!(a[0], a[1]);
}

// ---- Synthetic exports ----

/// Builds a small export, line by line.
#[derive(Default)]
struct B {
    lines: Vec<Value>,
    names: HashMap<String, u32>,
    nnames: u32,
    nlevels: u32,
    nexprs: u32,
}

impl B {
    fn new() -> Self {
        let mut b = B { nnames: 1, nlevels: 1, ..B::default() };
        b.lines.push(json!({"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},
            "format":{"version":"3.1.0"},"lean":{"githash":"0","version":"4.0.0"}}}));
        b
    }

    fn name(&mut self, s: &str) -> u32 {
        if s.is_empty() {
            return 0;
        }
        if let Some(&id) = self.names.get(s) {
            return id;
        }
        let (pre, last) = s.rsplit_once('.').unwrap_or(("", s));
        let pre = self.name(pre);
        let id = self.nnames;
        self.nnames += 1;
        self.lines.push(json!({"in": id, "str": {"pre": pre, "str": last}}));
        self.names.insert(s.to_string(), id);
        id
    }

    fn level(&mut self, v: Value) -> u32 {
        let id = self.nlevels;
        self.nlevels += 1;
        let mut obj = v.as_object().unwrap().clone();
        obj.insert("il".into(), json!(id));
        self.lines.push(Value::Object(obj));
        id
    }
    fn param(&mut self, n: &str) -> u32 {
        let n = self.name(n);
        self.level(json!({ "param": n }))
    }
    fn succ(&mut self, l: u32) -> u32 {
        self.level(json!({ "succ": l }))
    }
    fn max(&mut self, a: u32, b: u32) -> u32 {
        self.level(json!({ "max": [a, b] }))
    }
    fn imax(&mut self, a: u32, b: u32) -> u32 {
        self.level(json!({ "imax": [a, b] }))
    }

    fn expr(&mut self, v: Value) -> u32 {
        let id = self.nexprs;
        self.nexprs += 1;
        let mut obj = v.as_object().unwrap().clone();
        obj.insert("ie".into(), json!(id));
        self.lines.push(Value::Object(obj));
        id
    }
    fn bvar(&mut self, i: u64) -> u32 {
        self.expr(json!({ "bvar": i }))
    }
    fn sort(&mut self, l: u32) -> u32 {
        self.expr(json!({ "sort": l }))
    }
    fn cnst(&mut self, n: &str, us: &[u32]) -> u32 {
        let n = self.name(n);
        self.expr(json!({"const": {"name": n, "us": us}}))
    }
    fn c(&mut self, n: &str) -> u32 {
        self.cnst(n, &[])
    }
    fn app(&mut self, f: u32, args: &[u32]) -> u32 {
        args.iter().fold(f, |f, &a| self.expr(json!({"app": {"fn": f, "arg": a}})))
    }
    fn capp(&mut self, n: &str, args: &[u32]) -> u32 {
        let f = self.c(n);
        self.app(f, args)
    }
    fn binder(&mut self, kind: &str, n: &str, bi: &str, ty: u32, body: u32) -> u32 {
        let n = self.name(n);
        self.expr(json!({ kind: {"name": n, "type": ty, "body": body, "binderInfo": bi} }))
    }
    fn pi(&mut self, n: &str, bi: &str, ty: u32, body: u32) -> u32 {
        self.binder("forallE", n, bi, ty, body)
    }
    fn lam(&mut self, n: &str, bi: &str, ty: u32, body: u32) -> u32 {
        self.binder("lam", n, bi, ty, body)
    }
    fn nat(&mut self, n: &str) -> u32 {
        self.expr(json!({ "natVal": n }))
    }

    fn axiom(&mut self, n: &str, lps: &[&str], ty: u32) {
        let n = self.name(n);
        let lps: Vec<u32> = lps.iter().map(|p| self.name(p)).collect();
        self.lines.push(json!({"axiom": {"isUnsafe": false, "levelParams": lps, "name": n, "type": ty}}));
    }

    fn build(&self) -> Env {
        let text: Vec<String> = self.lines.iter().map(Value::to_string).collect();
        env_of(&(text.join("\n") + "\n"))
    }
}

/// Operator applications, with dummy type and instance arguments.
fn op(b: &mut B, head: &str, x: u32, y: u32) -> u32 {
    let nat = b.c("Nat");
    let inst = b.c("inst");
    match head {
        "Eq" => b.capp(head, &[nat, x, y]),
        "LE.le" | "LT.lt" => b.capp(head, &[nat, inst, x, y]),
        "And" | "Or" | "Iff" => b.capp(head, &[x, y]),
        _ => b.capp(head, &[nat, nat, nat, inst, x, y]),
    }
}

#[test]
fn operators_and_parentheses() {
    let mut b = B::new();
    let (a, c, d) = (b.c("a"), b.c("c"), b.c("d"));
    let x = op(&mut b, "HSub.hSub", a, c);
    let sub_l = op(&mut b, "HSub.hSub", x, d);
    let x = op(&mut b, "HSub.hSub", c, d);
    let sub_r = op(&mut b, "HSub.hSub", a, x);
    let x = op(&mut b, "HMul.hMul", c, d);
    let div = op(&mut b, "HDiv.hDiv", a, x);
    let x = op(&mut b, "HAdd.hAdd", a, c);
    let mul = op(&mut b, "HMul.hMul", x, d);
    let fapp = b.capp("f", &[x, d]);
    let (p, q) = (b.c("P"), b.c("Q"));
    let not_p = b.capp("Not", &[p]);
    let x = op(&mut b, "Or", q, not_p);
    let and_or = op(&mut b, "And", p, x);
    let pq = op(&mut b, "And", p, q);
    let or_and = op(&mut b, "Or", pq, p);
    let eq = op(&mut b, "Eq", a, c);
    let ne = b.capp("Not", &[eq]);
    let le = op(&mut b, "LE.le", a, c);
    let lt = op(&mut b, "LT.lt", c, d);
    let or = op(&mut b, "Or", le, lt);
    let iff = op(&mut b, "Iff", ne, or);
    let not_pq = b.capp("Not", &[pq]);
    let not_not = b.capp("Not", &[not_pq]);
    // `Not` applied to two arguments has no notation: a plain application.
    let over = b.capp("Not", &[p, q]);
    let env = b.build();
    let n = |e| expr_to_string(&env, e, Options::NOTATION);
    let r = |e| expr_to_string(&env, e, Options::RAW);

    assert_eq!(n(sub_l), "a - c - d");
    assert_eq!(n(sub_r), "a - (c - d)");
    assert_eq!(n(div), "a / (c * d)");
    assert_eq!(n(mul), "(a + c) * d");
    assert_eq!(n(fapp), "f (a + c) d");
    assert_eq!(n(and_or), "P ∧ (Q ∨ ¬P)");
    assert_eq!(n(or_and), "P ∧ Q ∨ P");
    assert_eq!(n(iff), "¬a = c ↔ a ≤ c ∨ c < d");
    assert_eq!(n(not_not), "¬¬(P ∧ Q)");
    assert_eq!(n(over), "Not P Q");
    assert_eq!(r(sub_l), "HSub.hSub Nat Nat Nat inst (HSub.hSub Nat Nat Nat inst a c) d");
    assert_eq!(r(iff), "Iff (Not (Eq Nat a c)) (Or (LE.le Nat inst a c) (LT.lt Nat inst c d))");
}

#[test]
fn binders_arrows_and_shadowing() {
    let mut b = B::new();
    let u = b.param("u");
    let sort_u = b.sort(u);
    let nat = b.c("Nat");
    let (p, q) = (b.c("P"), b.c("Q"));
    let prop = b.sort(0);
    let one = b.succ(0);

    // ∀ {α : Sort u} [inst : Add α] [inst✝ : Add α] ⦃x : α⦄, x = x
    let (x0, a1, a2, a3) = (b.bvar(0), b.bvar(1), b.bvar(2), b.bvar(3));
    let eq = b.capp("Eq", &[a3, x0, x0]);
    let body = b.pi("x", "strictImplicit", a2, eq);
    let add1 = b.capp("Add", &[a1]);
    let body = b.pi("inst._@.Foo._hyg.12", "instImplicit", add1, body);
    let add0 = b.capp("Add", &[x0]);
    let body = b.pi("inst", "instImplicit", add0, body);
    let implicit = b.pi("α", "implicit", sort_u, body);

    let pq = b.pi("h", "default", p, q);
    let arrow_l = b.pi("h", "default", pq, p);
    let qp = b.pi("h", "default", q, p);
    let arrow_r = b.pi("h", "default", p, qp);

    let eq = b.capp("Eq", &[nat, x0, x0]);
    let x_eq_x = b.pi("x", "default", nat, eq);
    let forall_right = b.pi("h", "default", p, x_eq_x);
    let forall_left = b.pi("h", "default", x_eq_x, p);

    let eq = b.capp("Eq", &[nat, a1, x0]);
    let inner = b.pi("x", "default", nat, eq);
    let shadow = b.pi("x", "default", nat, inner);

    let body = b.capp("f", &[a2, a1, x0]);
    let l = b.lam("x", "default", nat, body);
    let l = b.lam("x", "default", nat, l);
    let shadow3 = b.lam("x", "default", nat, l);

    let pp = b.c("P");
    let body = b.pi("h", "default", x0, pp);
    let root = b.pi("P", "default", prop, body);

    let lam = b.lam("x", "default", nat, x0);
    let id = b.cnst("id", &[one]);
    let nn = b.pi("a", "default", nat, nat);
    let lambda = b.app(id, &[nn, lam]);
    let partial = b.app(id, &[nat]);

    let add = b.capp("Add", &[x0]);
    let l = b.lam("inst", "instImplicit", add, a1);
    let implicit_lam = b.lam("α", "implicit", sort_u, l);
    let loose = b.bvar(7);

    // `id.{u} : ∀ {α : Sort u}, α → α`, so that notation mode knows α is implicit.
    let body = b.pi("a", "default", x0, a1);
    let id_ty = b.pi("α", "implicit", sort_u, body);
    b.axiom("id", &["u"], id_ty);
    let env = b.build();
    let n = |e| expr_to_string(&env, e, Options::NOTATION);
    let r = |e| expr_to_string(&env, e, Options::RAW);

    assert_eq!(n(implicit), "∀ {α : Sort u} [inst : Add α] [Add α] ⦃x : α⦄, x = x");
    assert_eq!(n(arrow_l), "(P → Q) → P");
    assert_eq!(n(arrow_r), "P → Q → P");
    assert_eq!(n(forall_right), "P → ∀ (x : Nat), x = x");
    assert_eq!(n(forall_left), "(∀ (x : Nat), x = x) → P");
    assert_eq!(n(shadow), "∀ (x : Nat) (x : Nat), x✝ = x");
    assert_eq!(n(shadow3), "fun x x x => f x✝² x✝ x");
    assert_eq!(r(shadow3), "fun (x : Nat) (x : Nat) (x : Nat) => f x✝² x✝ x");
    assert_eq!(n(root), "∀ (P : Prop), P → _root_.P");
    assert_eq!(n(lambda), "id (fun x => x)");
    assert_eq!(r(lambda), "id.{1} (Nat → Nat) (fun (x : Nat) => x)");
    assert_eq!(n(partial), "@id Nat");
    assert_eq!(r(partial), "id.{1} Nat");
    assert_eq!(n(implicit_lam), "fun {α} [inst] => α");
    assert_eq!(r(implicit_lam), "fun {α : Sort u} [inst : Add α] => α");
    assert_eq!(n(loose), "#7");
}

#[test]
fn levels_literals_projections_and_lets() {
    let mut b = B::new();
    let (u, v) = (b.param("u"), b.param("v"));
    let v1 = b.succ(v);
    let mx = b.max(u, v1);
    let imx = b.imax(u, v);
    let one = b.succ(0);
    let two = b.succ(one);
    let u1 = b.succ(u);
    let u2 = b.succ(u1);
    let sorts: Vec<u32> = [0, one, two, u, u1, u2, mx, imx].iter().map(|&l| b.sort(l)).collect();
    let foo = b.cnst("Foo", &[u, mx, two]);
    let s = b.expr(json!({ "strVal": "a\"b\\\n" }));
    let five = b.nat("5");
    let nat = b.c("Nat");
    let inst = b.c("inst");
    let three = b.nat("3");
    let ofnat = b.capp("OfNat.ofNat", &[nat, three, inst]);
    let k = b.c("k");
    let ofnat_var = b.capp("OfNat.ofNat", &[nat, k, inst]);
    let prod = b.name("Prod");
    let pc = b.c("p");
    let proj = b.expr(json!({"proj": {"typeName": prod, "idx": 0, "struct": pc}}));
    let (a, c) = (b.c("a"), b.c("c"));
    let mk = b.capp("Prod.mk", &[a, c]);
    let proj_app = b.expr(json!({"proj": {"typeName": prod, "idx": 1, "struct": mk}}));
    let lit = b.nat("2");
    let proj_lit = b.expr(json!({"proj": {"typeName": prod, "idx": 0, "struct": lit}}));
    let y = b.name("y");
    let lit1 = b.nat("1");
    let x0 = b.bvar(0);
    let let_ = b.expr(json!({"letE": {"name": y, "type": nat, "value": lit1, "body": x0, "nondep": false}}));
    let eq = b.capp("Eq", &[nat, x0, x0]);
    let l = b.lam("x", "default", nat, eq);
    let exists = b.capp("Exists", &[nat, l]);
    let env = b.build();
    let n = |e| expr_to_string(&env, e, Options::NOTATION);
    let r = |e| expr_to_string(&env, e, Options::RAW);

    let shown: Vec<String> = sorts.iter().map(|&e| n(e)).collect();
    assert_eq!(
        shown,
        ["Prop", "Type", "Type 1", "Sort u", "Type u", "Type (u+1)", "Sort (max u (v+1))", "Sort (imax u v)"]
    );
    assert_eq!(level_to_string(&env, u2), "u+2");
    assert_eq!(r(foo), "Foo.{u, max u (v+1), 2}");
    assert_eq!(n(foo), "Foo");
    assert_eq!(n(s), r#""a\"b\\\n""#);
    assert_eq!(n(five), "5");
    assert_eq!(n(ofnat), "3");
    assert_eq!(r(ofnat), "OfNat.ofNat Nat 3 inst");
    assert_eq!(n(ofnat_var), "OfNat.ofNat Nat k inst");
    assert_eq!(n(proj), "p.1");
    assert_eq!(n(proj_app), "(Prod.mk a c).2");
    assert_eq!(n(proj_lit), "(2).1");
    assert_eq!(n(let_), "let y : Nat := 1; y");
    assert_eq!(n(exists), "∃ x, x = x");
    assert_eq!(r(exists), "Exists Nat (fun (x : Nat) => Eq Nat x x)");
}
