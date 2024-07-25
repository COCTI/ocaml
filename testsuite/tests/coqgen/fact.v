From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.


Definition fact_for63 (n : coq_type ml_int) : M (coq_type ml_int) :=
  do v <- cnew ml_int 1%int63;
  do _ <-
  (do u <- Ret 1%int63;
   do v_1 <- Ret n;
   forloop u v_1
     (fun i =>
        do v_1 <- (do v_1 <- cget ml_int v; Ret (PrimInt63.mul v_1 i));
        cput ml_int v v_1));
  cget ml_int v.

Definition it_1 := Eval compute in Restart it (fact_for63 10%int63).
Print it_1.
