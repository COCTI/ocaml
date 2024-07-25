From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.


Definition x := T0 O.

Eval compute in T2_1 x.

Definition failwith (T_1 : ml_type) (s : coq_type ml_string)
  : M (coq_type T_1) := raise T_1 (Failure s).

Fixpoint length_aux (h : nat) (T_1 : ml_type) (len : coq_type ml_int)
  (param : coq_type (ml_list T_1)) : M (coq_type ml_int) :=
  if h is h.+1 then
    match param with
    | @nil _ => Ret len
    | _ :: l => length_aux h T_1 (PrimInt63.add len 1%int63) l
    end
  else FailGas.

Definition length (h : nat) (T_1 : ml_type) (l : coq_type (ml_list T_1))
  : M (coq_type ml_int) := length_aux h T_1 0%int63 l.

Definition cons_1 (T_1 : ml_type) (a : coq_type T_1)
  (l : coq_type (ml_list T_1)) : coq_type (ml_list T_1) := a :: l.

Definition hd (T_1 : ml_type) (param : coq_type (ml_list T_1))
  : M (coq_type T_1) :=
  match param with | @nil _ => failwith T_1 "hd"%string | a :: _ => Ret a end.

Fixpoint insert (h : nat) (T_1 : ml_type) (a : coq_type T_1)
  (l : coq_type (ml_list T_1)) : M (coq_type (ml_list T_1)) :=
  if h is h.+1 then
    match l with
    | @nil _ => Ret (a :: @nil (coq_type T_1))
    | b :: l' =>
      do v <- ml_le h T_1 a b;
      if v then Ret (a :: l) else
        do v <- insert h T_1 a l'; Ret (@cons (coq_type T_1) b v)
    end
  else FailGas.

Definition l :=
  Restart it
    (insert h ml_int 3%int63
       (1%int63 :: 2%int63 :: 4%int63 :: @nil (coq_type ml_int))).

Fixpoint isort (h : nat) (T_1 : ml_type) (l_1 : coq_type (ml_list T_1))
  : M (coq_type (ml_list T_1)) :=
  if h is h.+1 then
    match l_1 with
    | @nil _ => Ret (@nil (coq_type T_1))
    | a :: l' => do v <- isort h T_1 l'; insert h T_1 a v
    end
  else FailGas.

Fixpoint gcd (h : nat) (m n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_eq h ml_int m 0%int63; if v then Ret n else gcd h (mods n m) m
  else FailGas.

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

