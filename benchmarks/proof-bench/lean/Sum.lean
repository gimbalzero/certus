/-! Sum of the first n natural numbers, from scratch (no Mathlib). -/

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- Tactic-heavy proof: let automation (simp + omega) find the steps. -/
theorem sum_formula_auto (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumTo, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
    omega

/-- Explicit proof: every rewrite named, no search. -/
theorem sum_formula_explicit (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show 2 * (sumTo k + (k + 1)) = (k + 1) * (k + 1 + 1)
    rw [Nat.mul_add, ih, Nat.mul_comm (k + 1) (k + 1 + 1), Nat.add_mul (k+1) 1, Nat.add_mul k 1,
        Nat.one_mul, Nat.mul_comm k (k + 1), Nat.two_mul, Nat.add_assoc, ← Nat.add_assoc k 1]
    exact (Nat.add_assoc _ _ _).symm
