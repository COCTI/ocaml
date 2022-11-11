From mathcomp Require Import all_ssreflect.
Require Import Uint63 BinNums ZArith Eqdep_dec Ring63.
Require Import cocti_defs test2 sortproof.

Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.

Lemma happly [A B] [f g : A -> B] x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

Definition nat_to_int := fun n => of_Z (Z.of_nat n).
Definition int_to_nat := fun n => Z.to_nat (to_Z n).

Definition fact_rec_int n : int :=
  nat_to_int (fact_rec (int_to_nat n)).

Definition at_loc {T} (l : loc T) (x : coq_type T) env :=
  getref T l env = Ret x env.

Lemma lesb_not_ltsb m n : lesb m n -> ltsb n m = false.
Proof.
  move /Sint63.lebP => lelm.
  exact /Sint63.ltbP /Zle_not_lt.
Qed.

Lemma lesb_to_ltsb m n : lesb m n -> m <> n -> ltsb m n.
Proof.
  move/Sint63.lebP => lemn neqmn.
  apply/Sint63.ltbP /Z.le_neq.
  by split => // /Sint63.to_Z_inj.
Qed.

Lemma lesb_trans l m n : lesb l m -> lesb m n -> lesb l n.
Proof.
  move/Sint63.lebP => lelm.
  move/Sint63.lebP => lemn.
  apply/Sint63.lebP.
  by apply (Z.le_trans _ _ _ lelm).
Qed.

Lemma ltsb_trans l m n : ltsb l m -> ltsb m n -> ltsb l n.
Proof.
  move/Sint63.ltbP => ltlm.
  move/Sint63.ltbP => ltmn.
  apply/Sint63.ltbP.
  by apply (Z.lt_trans _ _ _ ltlm).
Qed.

Lemma le_le_eq m n : lesb m n -> lesb n m -> m = n.
Proof.
  move/Sint63.lebP => lemn /Sint63.lebP lenm.
  by apply /Sint63.to_Z_inj /Z.le_antisymm.
Qed.

Lemma lesb_succ_nmax n : lesb n (n + 1) <-> n <> Sint63.max_int.
Proof.
  split.
  - case H : (n == Sint63.max_int).
    + by move: H => /eqP ->.
    + by move /eqP in H.
  - move=> H'.
    apply /Sint63.lebP.
    rewrite Sint63.to_Z_succ // Z.add_1_r.
    exact (Z.le_succ_diag_r (Sint63.to_Z n)).
Qed.

Lemma ltsb_succ_nmax n : ltsb n (n + 1) <-> n <> Sint63.max_int.
Proof.
  split.
  - case H : (n == Sint63.max_int).
    + by move: H => /eqP ->.
    + by move /eqP in H.
  - move=> H'.
    apply /Sint63.ltbP.
    rewrite Sint63.to_Z_succ // Z.add_1_r.
    exact (Z.lt_succ_diag_r (Sint63.to_Z n)).
Qed.

Lemma ltsb_pred_nmin n : ltsb (n - 1) n <-> n <> Sint63.min_int.
Proof.
  split.
  - case H : (n == Sint63.min_int).
    + by move: H => /eqP ->.
    + by move /eqP in H.
  - move=> H'.
    apply /Sint63.ltbP.
    rewrite Sint63.to_Z_pred // Z.sub_1_r.
    exact (Z.lt_pred_l (Sint63.to_Z n)).
Qed.

Lemma lesb_l_nmax m n : lesb m n -> lesb n (n + 1) -> m <> Sint63.max_int.
Proof.
  case H : (m == Sint63.max_int).
  - move: H => /eqP -> => H.
    move: (Sint63.to_Z_bounded n) => [_] /Sint63.lebP H'.
    by move: (le_le_eq _ _ H H') => <-.
  - by move /eqP in H.
Qed.

Lemma ltsb_nmax m n : ltsb m n -> m <> Sint63.max_int.
Proof.
  case H : (m == Sint63.max_int).
  - move : H => /eqP -> /Sint63.ltbP.
    by move : (Sint63.to_Z_bounded n) => [_] /Zle_not_lt.
  - by move /eqP in H.
Qed.

Lemma ltsb_nmin m n : ltsb m n -> n <> Sint63.min_int.
Proof.
  case H : (n == Sint63.min_int).
  - move : H => /eqP -> /(Sint63.ltbP m).
    move : (Sint63.to_Z_bounded m) => [/Zle_not_gt H _].
    by move/Z.lt_gt.
  - by move /eqP in H.
Qed.

Lemma succ_ltsb_compat m n : n <> Sint63.max_int ->
  ltsb m n -> ltsb (m + 1) (n + 1).
Proof.
  move=> Hn ltmn.
  move: (ltmn) => /Sint63.ltbP => ltmn'.
  apply /Sint63.ltbP.
  rewrite !Sint63.to_Z_succ //.
    rewrite !Z.add_1_r.
    exact (Zplus_lt_compat_r _ _ 1 ltmn').
  exact (ltsb_nmax m n ltmn).
Qed.

Definition le_gas {T} (f g : M T) := forall env,
  RunW (f env) <> inr GasExhausted -> f env = g env.

Lemma forloop_mono h h' m n b : h <= h' ->
  le_gas (forloop h m n b) (forloop h' m n b).
Proof.
  elim : h h' m => [|h IH] [|h'] m H env //=.
  rewrite ltnS in H.
  case H' : (ltsb n m) => //.
  rewrite /Bind.
  case : (b m env) => env' -[c|e] //.
  by apply IH.
Qed.

Lemma enough_gas h m n p b env env' (tt' : unit) :
  ltsb m n ->
  forloop h m (n - 1)%uint63 b env = (env', inl tt') ->
  RunW (forloop h m p b env) <> inr GasExhausted ->
  RunW (forloop h n p b env') <> inr GasExhausted.
Proof.
  elim: h m env => [|h IH] m env Hmn //.
  rewrite {3}(lock h.+1) /=.
  have -> : (ltsb (n - 1) m) = false.
    apply /Sint63.ltbP /Zle_not_lt.
    rewrite Sint63.to_Z_pred ?Z.sub_1_r.
      exact /Z.lt_le_pred /Sint63.ltbP.
    exact (ltsb_nmin m n Hmn).
  case Hpm : (ltsb p m).
  - rewrite -lock /=.
    have -> : ltsb p n => //.
      exact (ltsb_trans p m n Hpm Hmn).
  - rewrite /Bind.
    case : (b m env) => [env'' [_|e]] => //.
    case Hmn' : ((m + 1)%uint63 == n).
    + move: Hmn' => /eqP ->.
      destruct h => //.
      rewrite {2}(lock h.+1) /=.
      have -> : (ltsb (n - 1) n).
        by apply /ltsb_pred_nmin /(ltsb_nmin m).
      move=> [-> _].
      rewrite -!lock => Hgas.
      have <- : forloop h.+1 n p b env' = forloop h.+2 n p b env' => //.
        by apply forloop_mono.
    + have Hmn'' : (ltsb (m + 1)%uint63 n).
        apply /Sint63.ltbP /Z.le_neq; split.
        - rewrite Sint63.to_Z_succ ?Z.add_1_r.
            by move : Hmn => /Sint63.ltbP /Zlt_le_succ.
          by apply (ltsb_nmax m n).
        - move/Sint63.to_Z_inj.
          by move:Hmn' => /eqP.
      rewrite -lock => Hf Hgas.
      move: (IH (m + 1)%uint63 env'' Hmn'' Hf Hgas) => Hgas'.
      have <- : forloop h n p b env' = forloop h.+1 n p b env' => //.
      by apply forloop_mono.
Qed.

Lemma forloop_cat h m n p b : lesb 0 m -> lesb m n ->
  lesb n (n + 1) -> lesb (n + 1) p ->
  le_gas (forloop h m p b) (forloop h m n b >> forloop h (n + 1)%uint63 p b).
Proof.
  elim: h m => [|h IH] m H0m Hmn Hnn' Hnp //.
  rewrite {3} (lock h.+1) /=.
  have -> : ltsb p m = false.
   move: (lesb_trans m n p Hmn (lesb_trans n (n + 1)%uint63 p Hnn' Hnp)) => Hmp.
   exact (lesb_not_ltsb _ _ Hmp).
  have -> : ltsb n m = false.
    exact (lesb_not_ltsb _ _ Hmn).
  move=> env.
  rewrite /Bind.
  case Heq : (m == n)%uint63.
  - move : Heq => /eqP ->.
    case : (b n env) => env' [a|e] Hgas //.
    destruct h => //.
    rewrite {1}(lock h.+1) /=.
    have -> : ltsb n (n + 1).
      exact /ltsb_succ_nmax /lesb_succ_nmax.
    case H : (Ret tt env') => [env'' [s|]] //.
    move : H Hgas => [] -> _ Hgas.
    rewrite -!lock (forloop_mono h.+1 h.+2) //.
  - move : Heq => /eqP Hneq.
    case : (b m env) => env' [a|e] Hgas //.
    rewrite IH /Bind -?lock //.
        case H : (forloop h (m + 1) n b env') => [env'' [a'|e]] => //.
        rewrite (forloop_mono _ (h.+1)) //.
        apply (enough_gas h (m + 1)%uint63 _ _ _ env' env'' a') => //.
          apply /succ_ltsb_compat => //.
            by apply lesb_succ_nmax.
          by apply lesb_to_ltsb.
        have -> : (n + 1 - 1)%uint63 = n => //.
          by ring.
      move: (lesb_trans 0 m (m + 1)%uint63 H0m) => -> //.
      apply lesb_succ_nmax.
      by apply (lesb_l_nmax _ n).
    apply /Sint63.lebP.
    rewrite Sint63.to_Z_succ ?Z.add_1_r.
      by move : (lesb_to_ltsb m n Hmn Hneq) => /Sint63.ltbP /Zlt_le_succ.
    by apply (lesb_l_nmax m n).
Qed.

Lemma int_to_natK n : nat_to_int (int_to_nat n) = n.
Proof.
  rewrite /nat_to_int /int_to_nat.
  rewrite Z2Nat.id ?of_to_Z //.
  by case : (to_Z_bounded n).
Qed.

Lemma hat_to_expnE n : 2 ^ n = expn 2 n.
Proof.
  elim: n => // n.
  rewrite expnSr Nat.pow_succ_r' => ->.
  by rewrite mulnC.
Qed.

Lemma nat_to_intK n : n < expn 2 63 -> int_to_nat (nat_to_int n) = n.
Proof.
  move=> Hn.
  rewrite /int_to_nat /nat_to_int.
  rewrite of_Z_spec.
  rewrite (_ : wB = Z.of_nat (expn 2 63)).
    rewrite -Nat2Z.inj_mod.
    rewrite Nat.mod_small //.
      by rewrite Nat2Z.id.
    apply /ltP => //.
  rewrite /wB /size.
  have -> : 2%Z = Z.of_nat 2.
    done.
  rewrite -Nat2Z.inj_pow.
  by rewrite hat_to_expnE.
Qed.

Definition RunM {A} (x : M A) env := RunW (x env).

Lemma coerceE T x : coerce T T x = Some x.
Proof.
  rewrite /coerce.
  case: ml_type_eq_dec => // a.
  by rewrite -(eq_rect_eq_dec ml_type_eq_dec).
Qed.

Definition mem_bindings k b :=
  let n := key_id k in
  let T := key_type k in
  (n < seq.size b) && ml_type_eq_dec (nth T (map (bind_type M) b) n) T.

Lemma lookup_updateE (k : key) (val : coq_type (key_type k)) env :
  mem_bindings k env ->
  obind (lookup k) (update (key_id k) (mkbind (key_type k) val) env) = Some val.
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
      rewrite ltnS => Hcount.
      move: (leq_ltn_trans Hcount Hmem).
      rewrite ltnNge.
      move/negP.
      elim.
      apply sub_count => b /andP [].
      move/eqbP /esym /eqbP.
      by rewrite H.
  - move=> Hmem Huniq.
    have Huniq' : uniq_bindings env.
      move=> x.
      move: (Huniq x) => /=.
      apply /leq_trans /leq_addl.
    move: {IH} (IH Hmem Huniq').
    case: update => //= env'.
    by rewrite H.
Qed.

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

Definition le_gasW {T} (f g : M T) := forall env,
  RunW (f env) <> inr GasExhausted -> RunW (f env) = RunW (g env).

Theorem fact_ok' h n : int_to_nat n < expn 2 61 ->
  le_gasW (fact_for h n) (Ret (fact_rec_int n)).
Proof.
  move=> H env.
  rewrite /fact_for {1}/Bind.
  case H' : (newref _ _ _) => [env'' [s|e]].
  - rewrite !bindretf.
    
Admitted.


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
(*       move/newgetref_int in H.
      by rewrite H => -[] _ <-. *)
      admit.
    destruct n.
      rewrite /nat_to_int /=.
      destruct h => //=.
      rewrite !bindA.
(*       move/newgetref_int in H.
      by rewrite H => -[] _ <-. *)
      admit.
    rewrite -(forloop_cat h 1 (nat_to_int n.+1)).
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
