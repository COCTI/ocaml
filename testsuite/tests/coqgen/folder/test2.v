From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.
Require test1.


Definition g (T : ml_type) (x : coq_type (ml_Test1_t T))
  : coq_type (ml_Test1_t T) := test1.f T x.

