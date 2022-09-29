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

Lemma forloop_cat h m n p b : (0 <=? m)%sint63 -> (m <=? n + 1)%sint63 ->
  (n <=? p)%sint63 -> int_to_nat (p - m) <= h ->
  forloop h m n b >> forloop h (n + 1)%sint63 p b = forloop h m p b.
Proof. Admitted.

Lemma int_to_natK n : (0 <=? n)%sint63 -> nat_to_int (int_to_nat n) = n.
Proof. Admitted.

Lemma nat_to_intK n : int_to_nat (nat_to_int n) = n.
Proof.
  rewrite /int_to_nat /nat_to_int.
  Admitted.

Lemma newgetref_int x s env env' :
  newref ml_int x env = (env', inl s) -> getref ml_int s env' = Ret x env'.
Proof. Admitted.

Lemma setgetref {T} x y s env env' :
  setref T x y env = (env', inl s) -> getref T x env' = Ret y env'.
Proof. Admitted.

Lemma nat_to_int_mul m n : (nat_to_int m * nat_to_int n)%sint63 =
  nat_to_int (m * n).
Proof. Admitted.

Lemma nat_to_int_inj m n : m = n -> nat_to_int m = nat_to_int n.
Proof. Admitted.

Theorem fact_ok h n m env env' : fact_for h n env = Ret m env' ->
  m = fact_rec_int n.
Proof.
  rewrite /fact_for. rewrite {1}/Bind.
  case H : (newref _ _ _) => [env'' [s|e]] //.
  rewrite !bindretf.
  case /boolP : (0 <=? n)%sint63.
  - move => Hn.
    rewrite -(int_to_natK _ Hn).
    elim : (int_to_nat n) m env' => [|{n Hn} n IH] m env' /=.
      rewrite /nat_to_int /=.
      destruct h => //=.
      rewrite bindretf.
      move/newgetref_int in H.
      by rewrite H => -[] _ <-.
    destruct n.
      rewrite /nat_to_int /=.
      destruct h => //=.
      rewrite bindretf.
      move/newgetref_int in H.
      by rewrite H => -[] _ <-.
    rewrite -(forloop_cat h 2 (nat_to_int n.+1)).
    rewrite bindA.
    rewrite {1}/Bind.
    move : IH.
    rewrite {1}/Bind.
    case : (forloop h 2 (nat_to_int n.+1) _ _) => [env''' [s'|e]] //.
    move=> H'.
    destruct h => //=.
    have -> : (nat_to_int n.+1 +1 ?= nat_to_int n.+2)%sint63 = Eq. admit.
    rewrite !bindA.
    rewrite {1}/Bind.
    case H'' : (getref _ _ _) => [env4 [s''|e]] //.
    rewrite bindretf.
    rewrite {1}/Bind.
    case H''' : (setref _ _ _) => [env5 [s'''|e]] //.
    destruct h => //=.
    have -> : (nat_to_int n.+1 +1 +1 ?= nat_to_int n.+2)%sint63 = Gt. admit.
    rewrite bindretf.
    move/ setgetref in H'''.
    rewrite H''' => -[] _ <-.
    rewrite H'' in H'.
    rewrite (H' s'' env4) //.
    have -> : (nat_to_int n.+1 + 1 = nat_to_int n.+2)%sint63. admit.
    rewrite /fact_rec_int.
    rewrite nat_to_int_mul.
    rewrite !nat_to_intK.
    rewrite /=.
    congr nat_to_int.
    rewrite [RHS]mulnC. done.
    
Admitted.
