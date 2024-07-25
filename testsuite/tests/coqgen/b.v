From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.
Require a.


Definition y := A_Point 2%int63 3%int63.

Definition z := B_Point (2.0%float) (3.0%float).

Definition f (T : ml_type) (x : coq_type T) : coq_type T := x.

Definition g (x : coq_type ml_A_point) : coq_type ml_A_point :=
  match x with | A_Point _ _ => f ml_A_point x end.

Definition h (y_1 : coq_type ml_B_point) : coq_type ml_B_point :=
  match y_1 with | B_Point _ _ => f ml_B_point y_1 end.

