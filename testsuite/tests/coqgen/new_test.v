From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.


Definition int_of_point (p : coq_type ml_New_test_point) : coq_type ml_int :=
  match p with | Point x => x end.

Definition head (l : coq_type (ml_list ml_string)) : coq_type ml_string :=
  match l with | @nil _ => ""%string | x :: _ => x end.

Definition x := 4%int63.

Definition x_1 := 5%int63.

Definition x_2 := 6%int63.

