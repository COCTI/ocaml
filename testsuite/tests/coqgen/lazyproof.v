From mathcomp Require Import all_ssreflect.
Require Import Sint63 Ascii String Floats cocti_defs test2 example.

Lemma cot_count c n n' n'' : lazy_counter c = Ret n ->
  force ml_int n = Ret n' -> force ml_int n = Ret n'' -> (n' =? n'')%sint63 == true.
Admitted.

Lemma counter_ok c n m n' m' : lazy_counter c = Ret n -> lazy_counter c = Ret m ->
  force ml_int n = Ret n' -> force ml_int m = Ret m' -> (n' + 1 =? m')%sint63 == true.
Admitted.