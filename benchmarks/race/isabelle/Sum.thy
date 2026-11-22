(* Sum of the first n natural numbers: 2 * (0 + 1 + ... + n) = n * (n + 1). *)

theory Sum
  imports Main
begin

(* COPY *)
primrec sumTo :: "nat \<Rightarrow> nat" where
  "sumTo 0 = 0"
| "sumTo (Suc n) = sumTo n + Suc n"

theorem sum_formula: "2 * sumTo n = n * (n + 1)"
  by (induct n) auto
(* END COPY *)

end
