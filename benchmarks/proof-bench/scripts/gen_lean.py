"""Generate N independent copies of the sum-formula proof (auto or explicit style)."""
import sys
n, style = int(sys.argv[1]), sys.argv[2]
out = ["set_option profiler true", "set_option profiler.threshold 0", ""]
for i in range(n):
    out.append(f"def sumTo{i} : Nat → Nat\n  | 0 => 0\n  | n + 1 => sumTo{i} n + (n + 1)\n")
    if style == "auto":
        out.append(f"""theorem t{i} (n : Nat) : 2 * sumTo{i} n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumTo{i}, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
    omega
""")
    else:
        out.append(f"""theorem t{i} (n : Nat) : 2 * sumTo{i} n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show 2 * (sumTo{i} k + (k + 1)) = (k + 1) * (k + 1 + 1)
    rw [Nat.mul_add, ih, Nat.mul_comm (k + 1) (k + 1 + 1), Nat.add_mul (k+1) 1, Nat.add_mul k 1,
        Nat.one_mul, Nat.mul_comm k (k + 1), Nat.two_mul, Nat.add_assoc, ← Nat.add_assoc k 1]
    exact (Nat.add_assoc _ _ _).symm
""")
print("\n".join(out))
