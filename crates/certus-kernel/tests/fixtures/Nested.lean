/-! Nested inductive types, for the Certus kernel tests. -/

/-- Nested through `List`, with a universe-polymorphic parameter. -/
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | node : List (Tree α) → Tree α

/-- Two levels of nesting (`Array (List _)`), two nested occurrences, a structure (`Array`). -/
inductive Rose where
  | mk : Array (List Rose) → Option Rose → Rose

/-- Nesting through `Prod` inside `List`. -/
inductive Term where
  | var : Nat → Term
  | app : Nat → List (Prod Term Term) → Term

-- A mutual block with nested occurrences.
mutual
inductive A where
  | a : List B → A
inductive B where
  | b : Option A → Prod A B → B
  | nil : B
end

/-- An indexed type, then nesting through it (the index is a field). -/
inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

inductive VTree where
  | mk : (n : Nat) → Vect VTree n → VTree

-- A mutual block of parameterised types, then nesting through it.
mutual
inductive Ev (α : Type) where
  | nil : Ev α
  | cons : α → Od α → Ev α
inductive Od (α : Type) where
  | cons : α → Ev α → Od α
end

inductive UsesEv where
  | mk : Ev UsesEv → UsesEv

/-- Structural recursion through the nested occurrence, then computation by `rfl`,
which reduces `Tree.rec_1`. -/
def Tree.size {α : Type u} : Tree α → Nat
  | .leaf _ => 1
  | .node ts => sizeList ts + 1
where sizeList : List (Tree α) → Nat
  | [] => 0
  | t :: ts => t.size + sizeList ts

theorem Tree.size_example : (Tree.node [.leaf 1, .node [.leaf 2, .leaf 3]]).size = 5 := rfl

def Rose.count : Rose → Nat
  | .mk xs o => xs.size + (match o with | none => 0 | some r => r.count)

theorem Rose.count_example : (Rose.mk #[[], []] (some (.mk #[[]] none))).count = 3 := by decide
