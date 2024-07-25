From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.
Require b.
Require a.


Definition x := A_Point 2%int63 3%int63.

Definition y := B_Point (2.0%float) (3.0%float).

Definition z := C_Point (coq_type ml_string) "2"%string "3"%string.

Definition f (T : ml_type) (x_1 : coq_type T) : coq_type T := x_1.

Definition g (x_1 : coq_type ml_A_point) : coq_type ml_A_point :=
  match x_1 with | A_Point _ _ => f ml_A_point x_1 end.

Definition h (y_1 : coq_type ml_B_point) : coq_type ml_B_point :=
  match y_1 with | B_Point _ _ => f ml_B_point y_1 end.

Definition i (T : ml_type) (z_1 : coq_type (ml_C_point T))
  : coq_type (ml_C_point T) :=
  match z_1 with | C_Point _ _ => f (ml_C_point T) z_1 end.

