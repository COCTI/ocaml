From mathcomp Require Import all_ssreflect.
Require Import Sint63 BinNums ZArith cocti_defs test2 sortproof.

Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.

Lemma happly [A B] [f g : A -> B] x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

Definition nat_to_int := fun n => of_Z (Z.of_nat n).
Definition int_to_nat := fun n => Z.to_nat (to_Z n).
Print Z.to_nat.

Definition fact_rec_int n : int :=
  nat_to_int (fact_rec (int_to_nat n)).
Print fact_rec.

Lemma bindinl {A} {B} {m : M A} {env} {env'} {a} {e : M B} :
  m env = (env', inl a) -> (m >> e) env = e env'.
Proof. by rewrite /Bind => ->. Qed.

Lemma fact_closed h n m env env' env'' : fact_for h n env = (Ret m) env' ->
  (fact_for h n env).2 = (fact_for h n env'').2.
Proof.
  rewrite /fact_for /=.
  elim: h env env' => [ |h IH] env env'.
  -
  -
Admitted.

(*Lemma fact_for_neg h n : int_to_nat n = 0 ->
  fact_for h.+1 n = Ret 1%sint63.
Proof.
  move=> Hn.
  elim: h => [/(happly empty_env)|h IH] //.
  apply IH.
  rewrite /fact_for.
Qed.*)

Definition at_loc {T} (l : loc T) (x : coq_type T) env :=
  getref T l env = Ret x env.
Locate "=1".
Check eqfun.
Locate eqfun.
Check at_loc.

Lemma forloop_cat h m n p b : (0 <=? m)%sint63 -> (m <=? n + 1)%sint63 ->
  (n <=? p)%sint63 -> int_to_nat (p - m) <= h ->
  forloop h m n b >>= (fun _ => forloop h n p b) = forloop h m p b.
Proof. Admitted.

Lemma int_to_natK n : (0 <=? n)%sint63 -> nat_to_int (int_to_nat n) = n.
Admitted.

Theorem fact_ok h n m env env' : fact_for h n env = Ret m env' ->
  m = fact_rec_int n.
Proof.
  rewrite /fact_for. rewrite {1}/Bind.
  case H : (newref _ _ _) => [env'' [s|e]] //.
  rewrite !bindretf.
  case /boolP : (0 <=? n)%sint63.
  move => Hn.
  rewrite -(int_to_natK _ Hn).
  elim : (int_to_nat n) m env' => [|{n Hn} n IH] m env'. admit.
  rewrite -(forloop_cat h 2 (nat_to_int n)).
  rewrite bindA.
  rewrite {1}/Bind.
  move : IH.
  rewrite {1}/Bind.
  case : (forloop h 2 (nat_to_int n) _ _) => [env''' [s'|e]].
  rewrite
  have -> : 2%sint63 = (k + 1)%sint63. admit.
  have Hat : at_loc s (fact_rec_int k) env''. admit.
  clear H.
  

  case Hn : (to_Z n) => [|l|l].
  - have Hn0 : n = 0%sint63.
      by apply to_Z_inj.
    rewrite Hn0 //=.
    destruct h => /(happly empty_env) //=.
  - move/(happly empty_env).
  -
Admitted.
