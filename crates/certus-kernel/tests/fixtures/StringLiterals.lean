prelude
/-! A minimal environment with string literals, for the Certus kernel tests
(`string_literals.ndjson`, exported with lean4export 3.1.0 from Lean 4.36:
`lean -o StringLiterals.olean StringLiterals.lean`, then
`leanexport StringLiterals -- lit_eq lit_proj lit_rec`).

String literals need `String`, `String.ofList`, `Char`, `Char.ofNat`,
`List.nil` and `List.cons` (and `Nat`) with their standard types.

The `string_literals_bad_*.ndjson` fixtures come from copies of this file
without the three theorems, plus `theorem lit_trivial : Eq "\x01" "\x01" :=
Eq.refl`, and with one change each:
- `bad_char_of_nat`: `def Char.ofNat (n : Nat) : Nat := n`;
- `bad_of_list`: `def String.ofList (data : List Nat) : String := String.mk List.nil`;
- `bad_list`: the constructors of `List` in the order `cons`, `nil`. -/
set_option genCtorIdx false
set_option genInjectivity false
set_option genSizeOf false
set_option bootstrap.genMatcherCode false
noncomputable section
-- Needed by the code generator, which runs on every inductive type.
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcProof {α : Prop} : α
unsafe axiom lcUnreachable {α : Sort u} : α

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

structure Char where
  val : Nat

def Char.ofNat (n : Nat) : Char := Char.mk n

structure String where
  data : List Char

def String.ofList (data : List Char) : String := String.mk data

/-- A literal is definitionally its expansion `String.ofList [Char.ofNat 1, Char.ofNat 2]`. -/
theorem lit_eq : Eq "\x01\x02"
    (String.ofList (List.cons (Char.ofNat (Nat.succ Nat.zero))
      (List.cons (Char.ofNat (Nat.succ (Nat.succ Nat.zero))) List.nil))) :=
  Eq.refl

/-- Projection out of a literal. -/
theorem lit_proj : Eq (String.data "\x01") (List.cons (Char.mk (Nat.succ Nat.zero)) List.nil) := Eq.refl

/-- Iota reduction with a literal as the major premise. -/
theorem lit_rec : Eq (@String.rec (fun _ => Nat) (fun _ => Nat.zero) "ab") Nat.zero := Eq.refl
