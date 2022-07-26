From mathcomp Require Import all_ssreflect.
Require Import Sint63 Ascii String Floats cocti_defs test2.

Definition divisible m n := ((mods m n) =? 0%sint63)%sint63.

Eval compute in divisible 2 4.

Lemma happly [A B] [f g : A -> B] x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

(*gcd is greatest*)
Theorem Gcd n m k :
   gcd h n m = Ret k ->
   forall x : int, (divisible n x) && (divisible m x) -> divisible k x.
Proof.
  elim: h => [/(happly empty_env) | h IH H x] //.
  move /andP => [] divn divm.
  
Admitted.

(*gcd is common divisor*)
Theorem gCD n m k : gcd h n m = Ret k -> (divisible n k) && (divisible m k).
Proof.
Admitted.

Lemma gcd_com n m k : gcd h n m = Ret k -> gcd h m n = Ret k.
Proof.
Admitted.
