From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.
Require stdlib.


Definition make_point (x y : coq_type ml_int)
  : coq_type ml_Test_point_point := Test_point_Point x y.

Definition add_point (v : coq_type ml_Test_point_point) : coq_type ml_int :=
  match v with | Test_point_Point x y => PrimInt63.add x y end.

Eval compute in add_point (Test_point_Point 2%int63 3%int63).
