From mathcomp Require Import all_ssreflect.
Require Import Uint63 BinNums ZArith cocti_defs test2 sortproof Eqdep_dec.

Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.

Lemma happly [A B] [f g : A -> B] x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

Definition nat_to_int := fun n => of_Z (Z.of_nat n).
Definition int_to_nat := fun n => Z.to_nat (to_Z n).

Definition fact_rec_int n : int :=
  nat_to_int (fact_rec (int_to_nat n)).

Definition at_loc {T} (l : loc T) (x : coq_type T) env :=
  getref T l env = Ret x env.

Lemma lesb_succ n : n <> Sint63.max_int -> lesb n (n + 1).
Proof.
  move=> H.
  apply /Sint63.lebP.
  rewrite Sint63.to_Z_succ // Z.add_1_r.
  by apply Z.le_succ_diag_r.
Qed.

Lemma lesb_trans l m n : lesb l m -> lesb m n -> lesb l n.
Proof.
  move/Sint63.lebP => lelm.
  move/Sint63.lebP => lemn.
  apply/Sint63.lebP.
  by apply (Z.le_trans _ _ _ lelm).
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

Lemma le_le_eq m n : lesb m n -> lesb n m -> m = n.
Proof.
  move/Sint63.lebP => lemn /Sint63.lebP lenm.
  by apply /Sint63.to_Z_inj /Z.le_antisymm.
Qed.

Lemma succ_notmax n : lesb n (n + 1) -> n <> Sint63.max_int.
Proof.
  case H : (n == Sint63.max_int).
  - by move: H => /eqP ->.
  - by move /eqP in H.
Qed.

Lemma notmax m n : lesb m n -> lesb n (n + 1) -> m <> Sint63.max_int.
Proof.
  case H : (m == Sint63.max_int).
  - move: H => /eqP -> /Sint63.lebP => H.
    have -> : n = Sint63.max_int => //=.
    case H'' : (n == Sint63.max_int).
    + by move /eqP in H''.
    + move /eqP in H''.
      move /Zle_not_lt in H.
      have H''' : (Sint63.to_Z n < Sint63.to_Z Sint63.max_int)%Z => //.
      apply Z.le_neq.
      split => //.
      - by apply Sint63.to_Z_bounded.
      - move=> I.
        by apply /H''/Sint63.to_Z_inj.
  - by move /eqP in H.
Qed.

Lemma enough_gas h m n p b env env' (tt' : unit) :
  ltsb m n ->
  forloop h m (n - 1)%uint63 b env = (env', inl tt') ->
  RunW (forloop h n p b env') = inr GasExhausted ->
  RunW (forloop h m p b env) = inr GasExhausted.
Proof.
  elim: h m env => [|h IH] m env Hmn Hgas Hf //=.
  case Hmp : (ltsb p m).
  - move: Hf.
    rewrite /=.
    have -> : ltsb p n => //.
    admit.
  - move: Hgas => /=.
    have -> : (ltsb (n - 1) m) = false. admit.
    rewrite /Bind.
    case : (b m env) => env'' [] // _.
    case Hmn' : ((m + 1) =? n)%uint63.
    + move: Hmn' => /eqb_correct ->.
      destruct h => //.
      rewrite [forloop h.+1 n (n - 1) b env''] /=.
      have -> : ltsb (n - 1) n. admit.
      case => -> _.
      case H : (RunW (forloop h.+1 n p b env')) => [a|e].
      - rewrite -H -Hf.
        apply /f_equal /(forloop_mono h.+1 h.+2) => //.
        by rewrite H.
      - destruct e => //;rewrite -H -Hf;
        apply /f_equal /(forloop_mono h.+1 h.+2) => //;
        by rewrite H.
    + move=> Hfor.
      apply IH => //.
        admit.
      

(*  case Hnp : (compares (n + 1) p) => //.
    + rewrite /Bind.
      case H : (b (n + 1)%uint63 env') => [env'' [tt|e]] //=.
      - admit.
      - admit.
    + admit. *)
  - admit.
Admitted.

Lemma forloop_cat' h m n p b : lesb 0 m -> lesb m n ->
  lesb n (n + 1) -> lesb (n + 1) p ->
  le_gas (forloop h m p b) (forloop h m n b >> forloop h (n + 1)%uint63 p b).
Proof.
  elim: h m => [|h IH] m H0m Hmn Hnn' Hnp //.
  rewrite {3} (lock h.+1) /=.
  case Hmp' : (ltsb p m).
  - admit. (*contr*)
  (* - case Hmn' : (ltsb n m).
    (* + case Hnp' : (ltsb p (n + 1)).
      - move: Hmp' Hmn' Hnp'.
        move /Eq_to_eq => <-.
        move /Eq_to_eq => <-.
        by move /compare_succ_notEq.
      - move: Hmp' Hmn' Hnp'.
        move /Eq_to_eq => <-.
        move /Eq_to_eq => <-.
        rewrite compare_succ //.
        by apply (notmax m n).
      - by move: (lesb_spec _ _ Hnp). *)
    + case Hnp' : (compares (n + 1) p).
      - move: Hmp' Hnp' Hmn'.
        move /Eq_to_eq => <-.
        move /Eq_to_eq => <-.
        rewrite compare_succ //.
        by apply succ_notmax.
      - move: Hmn'.
        move: Hmp' (Hnp) => /Eq_to_eq <- => Hmp'.
        move: (lesb_trans _ _ _ Hmn Hnn') => Hpm'.
        move: (le_le_eq _ _ Hmp' Hpm') => <-.
        by move: (compare_succ _ (succ_notmax _ Hnn')) ->.
      - by move: (lesb_spec _ _ Hnp).
    + by move: (lesb_spec _ _ Hmn). *)
  - case Hmn' : (ltsb n m).
    + 
    (* + case Hnp' : (compares (n + 1) p).
      - move=> env.
        move: Hmn' => /Eq_to_eq -> => Hgas.
        destruct h.
        + by rewrite !bindA !bindfailf.
        + rewrite bindA /Bind {1}(lock h.+1).
          case H : (b n env) => [env' [tt|e]] //=.
          move: (compare_succ n (succ_notmax _ Hnn')) -> => /=.
          rewrite -!lock.
          rewrite (forloop_mono h.+1 h.+2) //.
          by rewrite /Bind H in Hgas.
      - move=> env.
        move: Hmn' => /Eq_to_eq -> Hgas.
        destruct h.
        + by rewrite !bindA !bindfailf.
        + rewrite bindA /Bind {1}(lock h.+1).
          case H : (b n env) => [env' [tt|e]] //=.
          move: (compare_succ n (succ_notmax _ Hnn')) -> => /=.
          rewrite -!lock.
          rewrite (forloop_mono h.+1 h.+2) //.
          by rewrite /Bind H in Hgas.
      - by move: (lesb_spec _ _ Hnp). *)
    +(*  move: (Hmn') => /compare_Lt_succ_le => Hmn''.
      case Hnp' : (compares (n + 1) p) => env.
      - rewrite {1}/Bind.
        case H : (b m env) => [env' [tt|e]].
        + rewrite {1}/Bind H bindA {1}/Bind H => Hgas.
          rewrite (IH (m + 1)%uint63) //=.
            rewrite -lock /Bind.
            case H' : (forloop h (m + 1) n b env') => [env'' [tt'|e']] //.
            rewrite -(forloop_mono h h.+1) //.
            apply (enough_gas h m _ _ _  env' _ tt') => //.
          apply (lesb_trans _ _ _ H0m).
          by apply /lesb_succ /(notmax _ _ Hmn Hnn').
        + by rewrite bindA /Bind H.
      - rewrite {1}/Bind.
        case H : (b m env) => [env' [tt|e]].
        + rewrite {1}/Bind H bindA {1}/Bind H => Hgas.
          rewrite (IH (m + 1)%uint63) //=.
            rewrite -lock /Bind.
            case H' : (forloop h (m + 1) n b env') => [env'' [tt'|e']] //.
            rewrite -(forloop_mono h h.+1) //.
            apply (enough_gas h m _ _ _  env' _ tt') => //.
          apply (lesb_trans _ _ _ H0m).
          by apply /lesb_succ /(notmax _ _ Hmn Hnn').
        + by rewrite bindA /Bind H.
      - by move: (lesb_spec _ _ Hnp).
    + by move: (lesb_spec _ _ Hmn).
  - have Hmp : lesb m p.
      apply (lesb_trans _ (n + 1)) => //.
      by apply (lesb_trans _ n).
    by move: (lesb_spec _ _ Hmp).
Qed. *) Admitted.

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
      admit.
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
