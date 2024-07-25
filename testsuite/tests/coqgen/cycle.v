From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.
Require stdlib.


Definition cycle (T : ml_type) (a b : coq_type T)
  : M (coq_type (ml_ref (ml_Cycle_rlist T))) :=
  do r <- cnew (ml_Cycle_rlist T) (Nil (coq_type T) T);
  do _ <-
  (do v <-
   (do v <- cnew (ml_Cycle_rlist T) (Cons (coq_type T) T b r);
    Ret (Cons (coq_type T) T a v));
   cput (ml_Cycle_rlist T) r v);
  Ret r.

Definition rhd (T : ml_type) (x : coq_type T)
  (r : coq_type (ml_ref (ml_Cycle_rlist T))) : M (coq_type T) :=
  do v <- cget (ml_Cycle_rlist T) r;
  match v with | Nil => Ret x | Cons a _ => Ret a end.

Definition rtl (T : ml_type) (r : coq_type (ml_ref (ml_Cycle_rlist T)))
  : M (coq_type (ml_ref (ml_Cycle_rlist T))) :=
  do v <- cget (ml_Cycle_rlist T) r;
  match v with | Nil => Ret r | Cons _ l => Ret l end.

Fixpoint rdrop (h : nat) (T : ml_type) (n : coq_type ml_int)
  (l : coq_type (ml_ref (ml_Cycle_rlist T)))
  : M (coq_type (ml_ref (ml_Cycle_rlist T))) :=
  if h is h.+1 then
    do v <- ml_le h ml_int n 0%int63; if v then Ret l else rtl T l
  else FailGas.

Fixpoint mkrlist (h : nat) (T : ml_type) (l : coq_type (ml_list T))
  (r : coq_type (ml_ref (ml_Cycle_rlist T)))
  : M (coq_type (ml_ref (ml_Cycle_rlist T))) :=
  if h is h.+1 then
    match l with
    | @nil _ => Ret r
    | a :: l_1 =>
      do v <- (do v <- mkrlist h T l_1 r; Ret (Cons (coq_type T) T a v));
      cnew (ml_Cycle_rlist T) v
    end
  else FailGas.

Definition cyclel (h : nat) (T : ml_type) (a : coq_type T)
  (l : coq_type (ml_list T)) : M (coq_type (ml_ref (ml_Cycle_rlist T))) :=
  do r <- cnew (ml_Cycle_rlist T) (Nil (coq_type T) T);
  do _ <-
  (do v <- (do v <- mkrlist h T l r; Ret (Cons (coq_type T) T a v));
   cput (ml_Cycle_rlist T) r v);
  Ret r.

Fixpoint iappend (h : nat) (T : ml_type)
  (l1 l2 : coq_type (ml_Cycle_rlist T)) : M (coq_type (ml_Cycle_rlist T)) :=
  if h is h.+1 then
    match l1 with
    | Nil => Ret l2
    | Cons a l1' =>
      do _ <-
      (do v <- (do v <- cget (ml_Cycle_rlist T) l1'; iappend h T v l2);
       cput (ml_Cycle_rlist T) l1' v);
      Ret l1
    end
  else FailGas.

Fixpoint nconc_aux (h : nat) (T : ml_type)
  (l1 : coq_type (ml_ref (ml_rlist T))) (l2 : coq_type (ml_rlist T))
  : M (coq_type ml_unit) :=
  if h is h.+1 then
    do v <- cget (ml_rlist T) l1;
    match v with
    | Nil => cput (ml_rlist T) l1 l2
    | Cons a l1' => nconc_aux h T l1' l2
    end
  else FailGas.

Definition nconc (h : nat) (T : ml_type) (l1 l2 : coq_type (ml_rlist T))
  : M (coq_type (ml_rlist T)) :=
  match l1 with
  | Nil => Ret l2
  | Cons _ l1' => do _ <- nconc_aux h T l1' l2; Ret l1
  end.

