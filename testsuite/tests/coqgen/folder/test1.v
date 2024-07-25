From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs project_lib.


Definition f (a : ml_type) (x : coq_type (ml_Test1_t a))
  : coq_type (ml_Test1_t a) := x.

