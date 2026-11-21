(* Sum of the first n natural numbers: 2 * (0 + 1 + ... + n) = n * (n + 1). *)

(* COPY *)
let sumTo = define
 `(sumTo 0 = 0) /\ (!n. sumTo (SUC n) = sumTo n + SUC n)`;;

let sum_formula = prove
 (`!n. 2 * sumTo n = n * (n + 1)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[sumTo; LEFT_ADD_DISTRIB] THEN ARITH_TAC);;
(* END COPY *)
