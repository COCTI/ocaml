From mathcomp Require Import all_ssreflect.
Require Import Sint63 BinNums ZArith cocti_defs test2.

Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.

Lemma happly [A B] [f g : A -> B] x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

Definition nat_to_int := fun n => of_Z (Z.of_nat n).
Definition int_to_nat := fun n => Z.to_nat (to_Z n).

Definition fact_rec_int n : int :=
  match int_to_nat n with
  | 0 => 1
  | m.+1 => nat_to_int (m.+1 * fact_rec m)
  end.

(*Definition fact_rec_int' n : := .*)


Lemma fact_pure h n m env env' : fact_for h n = (Ret m) ->
  (fact_for h n env).2 = (fact_for h n env').2.
Proof. by move=> -> /=. Qed.

(*Lemma fact_for_ok' h n m :
  fact_for h n = Ret m -> fact_for h.+1 n = Ret m.
Proof.

Qed.*)

(*Lemma int_neg n : int_to_nat n = 0 -> (n ?= 0)%sint63 = Lt.
Proof.

Qed.*)

(*Lemma fact_for_neg h n : int_to_nat n = 0 ->
  fact_for h.+1 n = Ret 1%sint63.
Proof.
  move=> Hn.
  elim: h => [/(happly empty_env)|h IH] //.
  apply IH.
  rewrite /fact_for.
Qed.*)

Theorem fact_ok h n m : fact_for h n = Ret m ->
  m = fact_rec_int n.
Proof.
  case Hn : (to_Z n) => [|l|l].
  - have Hn0 : n = 0%sint63.
      by apply to_Z_inj.
    rewrite Hn0 //=.
    destruct h => /(happly empty_env) //=.
  - move/(happly empty_env).
  -
Qed.
