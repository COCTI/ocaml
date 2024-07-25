From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.


Definition cycle (T : ml_type) (a b : coq_type T)
  : M (coq_type (ml_Cyclic_rlist T)) :=
  do r <- cnew (ml_Cyclic_rlist T) (Nil (coq_type T) T);
  do l <-
  (do v <- cnew (ml_Cyclic_rlist T) (Cons (coq_type T) T b r);
   Ret (Cons (coq_type T) T a v));
  do _ <- cput (ml_Cyclic_rlist T) r l; Ret l.

Definition l := Restart it (cycle ml_bool true false).

Definition hd (T : ml_type) (def : coq_type T)
  (param : coq_type (ml_Cyclic_rlist T)) : coq_type T :=
  match param with | Nil => def | Cons a _ => a end.

Definition tl (T : ml_type) (param : coq_type (ml_Cyclic_rlist T))
  : M (coq_type (ml_Cyclic_rlist T)) :=
  match param with
  | Nil => Ret (Nil (coq_type T) T)
  | Cons _ t => cget (ml_Cyclic_rlist T) t
  end.

