From mathcomp Require Import all_ssreflect.
Require Import Sint63 cocti_defs test2.

Fixpoint fact_rec_pos (n : nat) : nat :=
  match n with
  | 0 => 1
  | m.+1 => m.+1 * fact_rec_pos m
  end.
Print pos_neg_int63.
Print nat.
Print to_Z.
Print BinNums.Z.
Check Z0.
Check Zneg 1%sint63.

Definition fact_rec (n : int) : nat := 
  match to_Z n with
  | Z0  => 1
  | Zpos m => fact_rec_pos (Pos.to_nat m)
  | Zneg _ => 1
  end.

Theorem fact_ok h n :
  inl_inv(snd(fact_for h (n:>int) empty_env)) = fact_rec n.
Proof.

Qed.
