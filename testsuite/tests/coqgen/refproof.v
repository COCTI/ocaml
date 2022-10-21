From mathcomp Require Import all_ssreflect.
Require Import Uint63 BinNums ZArith cocti_defs test2 sortproof Eqdep_dec.

Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.

Lemma happly [A B] [f g : A -> B] x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

Definition nat_to_int := fun n => of_Z (Z.of_nat n).
Definition int_to_nat := fun n => Z.to_nat (to_Z n).

Definition fact_rec_int n : int :=
  nat_to_int (fact_rec (int_to_nat n)).

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
  fact_for h.+1 n = Ret 1%uint63.
Proof.
  move=> Hn.
  elim: h => [/(happly empty_env)|h IH] //.
  apply IH.
  rewrite /fact_for.
Qed.*)

Definition at_loc {T} (l : loc T) (x : coq_type T) env :=
  getref T l env = Ret x env.

Lemma forloop_cat h m n p b : (0 <=? m)%uint63 -> (m <=? n + 1)%uint63 ->
  (n <=? p)%uint63 -> int_to_nat (p - m) <= h ->
  forloop h m n b >> forloop h (n + 1)%uint63 p b = forloop h m p b.
Proof.

Admitted.

Lemma int_to_natK n : nat_to_int (int_to_nat n) = n.
Proof.
  rewrite /nat_to_int /int_to_nat.
  rewrite Z2Nat.id ?of_to_Z //.
  by case : (to_Z_bounded n).
Qed.

Lemma nat_to_intK n : n < expn 2 63 -> int_to_nat (nat_to_int n) = n.
Proof.
  rewrite /int_to_nat /nat_to_int.
Admitted.

Definition RunM {A} (x : M A) env := RunW (x env).

Lemma coerceE T x : coerce T T x = Some x.
Proof.
  rewrite /coerce.
  case: ml_type_eq_dec => // a.
  by rewrite -(eq_rect_eq_dec ml_type_eq_dec).
Qed.

Definition key_eqb (k1 k2 : key) :=
  (key_id k1 =? key_id k2)%uint63 &&
  (ml_type_eq_dec (key_type k1) (key_type k2)).

Definition mem_bindings k :=
  has (fun b => key_eqb k (bind_key M b)).

Definition uniq_bindings env :=
 forall c, count (fun b => key_id (bind_key M b) =? c)%uint63 env <= 1.

Lemma lookup_updateE (k : key) (val : coq_type (key_type k)) env :
  mem_bindings k env -> uniq_bindings env ->
  obind (lookup k) (update (mkbind k val) env) = Some val.
Proof.
  elim: env => //= -[k' v env IH] /=.
  rewrite /key_eqb.
  case H: (key_id k =? key_id k')%uint63 => /=.
  - case: ml_type_eq_dec => a //=.
    + by rewrite Uint63.eqb_refl coerceE.
    + rewrite /mem_bindings /uniq_bindings /key_eqb.
      move => Hmem /(_ (key_id k)).
      apply eqb_correct in H.
      rewrite 1!H /= eqb_refl.
      rewrite has_count in Hmem.
Search nat bool true.
Search count. admit.
  - move=> Hmem Huniq.
    have Huniq' : uniq_bindings env.
      move=> x.
      move: (Huniq x) => /=.
      apply /leq_trans /leq_addl.
    move: {IH} (IH Hmem Huniq').
    case: update => //= env'.
    by rewrite H.
Admitted.

Lemma newref_getE {T} x env :
  RunM (do s <- newref T x; getref T s) env = inl x.
Proof.
  rewrite /RunM /newref /getref /Bind.
  case: env => i l /=.
  by rewrite Uint63.eqb_refl coerceE.
Qed.

Definition mem_env {T} (r : loc T) env :=
  let: mkEnv c refs := env in
  let: mkloc k := r in mem_bindings k refs.

Definition envok env :=
  let: mkEnv c refs := env in uniq_bindings refs.

Lemma updateok k env : mem_bindings (bind_key M k) env -> uniq_bindings env
  -> update k env <> None.
Admitted.

Lemma setref_getE {T} x y env :
  mem_env x env -> envok env ->
  RunM (do _ <- setref T x y; getref T x) env = inl y.
Proof.
  rewrite /RunM /setref /getref /Bind.
  case: env => i l.
  case: x y => k y /= Hmem Huniq.
  case H : update => [s'|] => //=.
  move: (lookup_updateE k y l Hmem Huniq).
  rewrite H /= => -> //.
  by move/(updateok (mkbind k y) l Hmem Huniq) in H.
Qed.

Lemma nat_to_int_mul m n : (nat_to_int m * nat_to_int n)%uint63 =
  nat_to_int (m * n).
Proof. Admitted.

Lemma nat_to_int_inj m n : m = n -> nat_to_int m = nat_to_int n.
Proof. Admitted.

Theorem fact_ok h n m env env' : int_to_nat n < expn 2 61 ->
  fact_for h n env = Ret m env' -> m = fact_rec_int n.
Proof.
  rewrite /fact_for. rewrite {1}/Bind. rewrite [61]lock.
  case H : (newref _ _ _) => [env'' [s|e]] //.
  rewrite !bindretf.
  case /boolP : (lesb 0 n).
  - move => Hn.
    rewrite -{-1}(int_to_natK n).
    elim : (int_to_nat n) m env' => [|{n Hn} n IH] m env' //= => [_ | Hn].
      rewrite /nat_to_int /=.
      destruct h => //=.
      rewrite bindretf.
      move:H. 
      move/newref_getE in H.
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
    have -> : (compares (nat_to_int n.+1 +1) (nat_to_int n.+2))%uint63 = Eq. admit.
    rewrite !bindA.
    rewrite {1}/Bind.
    case H'' : (getref _ _ _) => [env4 [s''|e]] //.
    rewrite bindretf.
    rewrite {1}/Bind.
    case H''' : (setref _ _ _) => [env5 [s'''|e]] //.
    destruct h => //=.
    have -> : compares(nat_to_int n.+1 +1 +1)%uint63 (nat_to_int n.+2) = Gt. admit.
    rewrite bindretf.
    move/ setgetref in H'''.
    rewrite H''' => -[] _ <-.
    rewrite H'' in H'.
    rewrite (H' s'' env4) //.
    have -> : (nat_to_int n.+1 + 1 = nat_to_int n.+2)%uint63. admit.
    rewrite /fact_rec_int.
    rewrite nat_to_int_mul.
    rewrite !nat_to_intK.
    rewrite /=.
    congr nat_to_int.
    rewrite [RHS]mulnC. done.
    all:auto.
    rewrite (leq_trans Hn)//.
    rewrite -lock leq_exp2l //.
    rewrite (ltn_trans (ltnSn _))//.
    rewrite (leq_trans Hn)// -lock leq_exp2l //.
Admitted.
