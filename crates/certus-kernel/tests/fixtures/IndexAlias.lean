/-! Inductive types whose type reaches its indices through a definition, for
the Certus kernel tests (issue #29; Mathlib's `CategoryTheory.Presieve.map`). -/

/-- Like Mathlib's `Presieve X := ∀ ⦃Y⦄, (Y ⟶ X) → Prop`: a definition that unfolds to a Pi. -/
def Pred (α : Type) : Type := α → Prop

/-- Two levels of definitions. -/
def Rel (α : Type) : Type := α → Pred α

/-- The image of a predicate: its type `Pred β` has one index, after unfolding. -/
inductive Image {α β : Type} (f : α → β) (s : Pred α) : Pred β where
  | mk (a : α) (h : s a) : Image f s (f a)

/-- Two indices, both behind definitions. -/
inductive Step : Rel Nat where
  | succ (n : Nat) : Step n (n + 1)

theorem image_elim {α β : Type} (f : α → β) (s : Pred α) (b : β) (h : Image f s b) : ∃ a, f a = b :=
  match h with
  | .mk a _ => ⟨a, rfl⟩

theorem step_elim (m n : Nat) (h : Step m n) : n = m + 1 := by
  cases h; rfl
