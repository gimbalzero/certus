(* Sum of the first n natural numbers: 2 * (0 + 1 + ... + n) = n * (n + 1). *)

From Stdlib Require Import Lia.

(* COPY *)
Fixpoint sumTo (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => sumTo k + S k
  end.

Theorem sum_formula : forall n : nat, 2 * sumTo n = n * (n + 1).
Proof.
  induction n as [| k IH].
  - reflexivity.
  - cbn [sumTo]. nia.
Qed.
(* END COPY *)
