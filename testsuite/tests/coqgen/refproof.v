From mathcomp Require Import all_ssreflect.
Require Import Uint63 BinNums ZArith Eqdep_dec Ring63.
Require Import cocti_defs test2 sortproof.

Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.

Lemma happly [A B] [f g : A -> B] x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

Definition N2int := fun n => of_Z (Z.of_nat n).
Definition int2N := fun n => Z.to_nat (to_Z n).

Definition fact_rec_int n : int :=
  N2int (fact_rec (int2N n)).

Definition at_loc {T} (l : loc T) (x : coq_type T) env :=
  getref T l env = Ret x env.

Lemma lesb_not_ltsb m n : lesb m n <-> ltsb n m = false.
Proof.
  split.
  - move=> lemn.
    by apply/Sint63.ltbP/Z.nlt_ge/Sint63.lebP.
  - by move/Sint63.ltbP/Z.nlt_ge/Sint63.lebP.
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

Lemma lesb_nmax m n : lesb m n -> n <> Sint63.max_int ->
  m <> Sint63.max_int.
Proof.
  case H : (m == Sint63.max_int).
  - move : H => /eqP -> /Sint63.lebP.
    move : (Sint63.to_Z_bounded n) => [_].
    move/Sint63.lebP => H.
    move/Sint63.lebP => H'.
    by move:(le_le_eq _ _ H H').
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

Lemma ltsb_to_lesb m n : ltsb m n -> lesb (m + 1) n.
Proof.
  move => ltmn.
  apply/Sint63.lebP.
  rewrite Sint63.to_Z_succ ?Z.add_1_r.
    by apply/Zlt_le_succ/Sint63.ltbP.
  by apply (ltsb_nmax _ n).
Qed.

Lemma succ_lesb_compat m n : n <> Sint63.max_int ->
  lesb m n -> lesb (m + 1) (n + 1).
Proof.
  move=> Hn lemn.
  move: (lemn) => /Sint63.lebP => lemn'.
  apply /Sint63.lebP.
  rewrite !Sint63.to_Z_succ //.
    rewrite !Z.add_1_r.
    exact (Zplus_le_compat_r _ _ 1 lemn').
   exact (lesb_nmax m n lemn Hn).
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

Lemma forloop_cat h m n p b : lesb 0 m -> lesb (m - 1) n ->
  lesb n (n + 1) -> lesb n p ->
  le_gas (forloop h m p b) (forloop h m n b >> forloop h (n + 1)%uint63 p b).
Proof.
  elim: h m => [|h IH] m H0m Hmn Hnn' Hnp //.
  rewrite {3} (lock h.+1) /=.
  case Hnm : (ltsb n m).
    have -> : (n + 1)%uint63 = m.
      move/succ_lesb_compat in Hmn.
      have nmax : n <> Sint63.max_int by apply lesb_succ_nmax.
      move:(Hmn nmax).
      have -> : (m - 1 + 1 = m)%uint63 by ring.
      move:Hnm.
      move/ltsb_to_lesb.
      by apply le_le_eq.
    by rewrite -lock.
  have -> : ltsb p m = false.
    move/lesb_not_ltsb in Hnm.
    apply/lesb_not_ltsb.
    by apply (lesb_trans m n p).
  move=> env; rewrite bindA {1 2 3}/Bind.
  case H : (b m env) => [env' [?|e]] NE //.
  case Hmn' : (m =? n)%uint63.
  + move/eqb_correct in Hmn'. subst n.
    destruct h => //.
    rewrite [forloop h.+1 (m + 1) m b]/=.
    have -> : ltsb m (m+1) by apply/ltsb_succ_nmax/lesb_succ_nmax.
    apply forloop_mono => //.
    by rewrite -lock.
  + move/eqb_false_correct in Hmn'.
    transitivity ((forloop h (m + 1) n b >> forloop h (n + 1) p b) env').
    - apply IH => //.
      + apply (lesb_trans _ m) => //.
        apply/lesb_succ_nmax /(lesb_l_nmax m n) => //;
          by apply lesb_not_ltsb.
      + have -> : (m + 1 - 1 = m)%uint63 by ring.
        by apply lesb_not_ltsb.
    - rewrite /Bind.
      case Hfor : (forloop h (m + 1) n b env') => [env'' []] //.
      apply forloop_mono => //.
        by rewrite -lock.
      eapply (enough_gas _ (m+1)).
        apply/succ_ltsb_compat => //.
          by apply (lesb_succ_nmax).
        apply /lesb_to_ltsb=> //; by apply /lesb_not_ltsb.
        have -> : (n + 1 - 1 = n)%uint63 by ring.
        by apply/Hfor.
      done.
Qed.

Lemma int2NK n : N2int (int2N n) = n.
Proof.
  rewrite /N2int /int2N.
  rewrite Z2Nat.id ?of_to_Z //.
  by case : (to_Z_bounded n).
Qed.

Lemma hat_to_expnE n : 2 ^ n = expn 2 n.
Proof.
  elim: n => // n.
  rewrite expnSr Nat.pow_succ_r' => ->.
  by rewrite mulnC.
Qed.

Lemma N2intK n : n < expn 2 63 -> int2N (N2int n) = n.
Proof.
  move=> Hn.
  rewrite /int2N /N2int.
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
  (key_id k1 =? key_id k2) &&
  (ml_type_eq_dec (key_type k1) (key_type k2)).

Definition mem_bindings k :=
  has (fun b => key_eqb k (bind_key M b)).

Definition uniq_bindings env :=
 forall c, count (fun b => key_id (bind_key M b) =? c) env <= 1.

Lemma lookup_updateE (k : key) (val : coq_type (key_type k)) env :
  mem_bindings k env -> uniq_bindings env ->
  obind (lookup k) (update (mkbind k val) env) = Some val.
Proof.
  elim: env => //= -[k' v env IH] /=.
  rewrite /key_eqb.
  case H: (key_id k =? key_id k') => /=.
  - case: ml_type_eq_dec => a //=.
    + by rewrite Nat.eqb_refl coerceE.
    + rewrite /mem_bindings /uniq_bindings /key_eqb.
      move => Hmem /(_ (key_id k)).
      move /Nat.eqb_spec in H.
      rewrite 1!H /= Nat.eqb_refl.
      rewrite has_count in Hmem.
      rewrite ltnS => Hcount.
      move: (leq_ltn_trans Hcount Hmem).
      rewrite ltnNge.
      move/negP.
      elim.
      apply sub_count => b /andP [].
      by rewrite Nat.eqb_sym H.
  - move=> Hmem Huniq.
    have Huniq' : uniq_bindings env.
      move=> x.
      move: (Huniq x) => /=.
      apply /leq_trans /leq_addl.
    move: {IH} (IH Hmem Huniq').
    case: update => //= env'.
    by rewrite H.
Qed.

Lemma update_lookupE (k : key) (val : coq_type (key_type k)) env :
  mem_bindings k env -> uniq_bindings env -> lookup k env = Some val ->
  update (mkbind k val) env = Some env.
Proof.
  elim : env => [|b refs IH] //=.
  move/orP => [].
  - rewrite /key_eqb => /andP [].
    case ml_type_eq_dec => //=.
    case H : b => [k' val'] //= Htype Hid _ _.
    rewrite Hid /coerce.
    case ml_type_eq_dec => Htype' //.
    move /Some_inj => H'.
    case ml_type_eq_dec => //= _.
    f_equal.
    admit.
  - move=> Hmem Huniq.
  Admitted.

Definition mem_env {T} (r : loc T) env :=
  let: mkEnv c refs := env in
  let: mkloc k := r in mem_bindings k refs.

Definition envok env :=
  let: mkEnv c refs := env in uniq_bindings refs /\
  all(fun b => key_id (bind_key M b) < c) refs.

Lemma lookupok k env : mem_bindings k env -> uniq_bindings env ->
  lookup k env <> None.
Proof.
  rewrite /mem_bindings.
  elim env => [|b refs IH] //=.
  case H : key_eqb => /=.
  - move:H.
    rewrite /key_eqb => /andP [H].
    case ml_type_eq_dec => //= H' _ _.
    case : b H H' => k' val -> -> /=.
    by rewrite coerceE.
  - move:H.
    rewrite {1}/key_eqb.
    case H : (key_id k =? key_id _) => /=.
    + case ml_type_eq_dec => //= H' _.
      rewrite has_count /uniq_bindings /= => Hcount.
      move/(_ (key_id k)).
      rewrite Nat.eqb_sym H /=.
      rewrite ltnS => Hcount'.
      move: (leq_ltn_trans Hcount' Hcount).
      rewrite ltnNge.
      move/negP.
      elim.
      apply sub_count => b' /andP [].
      by rewrite Nat.eqb_sym.
    + move=>_ Hhas.
      case : b H => k' val /= H Huniq.
      rewrite H.
      apply IH => //.
      rewrite /uniq_bindings => c.
      move:Huniq.
      rewrite /uniq_bindings.
      move/(_ c) => /=.
      case :(key_id k' =? c) => //=.
      rewrite ltnS.
      by move/leqW.
Qed.

Lemma updateok b env : mem_bindings (bind_key M b) env -> uniq_bindings env ->
  update b env <> None.
Proof.
  elim env => [|b' refs IH] //=.
  move /orP => [].
  - rewrite /key_eqb => /andP [] Hid Htype.
    move=> Huniq.
    case : b IH Hid Htype  => k v /= IH Hid Htype.
    case : b' Hid Htype Huniq => k' v' /= Hid Htype Huniq.
    by rewrite Hid Htype.
  - move=> Hmem Huniq.
    case : b IH Hmem => k v /= IH Hmem.
    case : b' Huniq => k' v' /= Huniq.
    case:ifP => Hid.
    + move:Huniq Hmem.
      rewrite /uniq_bindings => /(_ (key_id k)) /=.
      rewrite Nat.eqb_sym Hid ltnS => Hcount.
      rewrite /mem_bindings has_count => Hcount'.
      move:(leq_ltn_trans Hcount Hcount').
      rewrite ltnNge.
      move/negP.
      elim.
      apply sub_count => b /andP [].
      by rewrite Nat.eqb_sym.
    + rewrite /omap /obind /oapp.
      have Huniq' : uniq_bindings refs.
        rewrite /uniq_bindings => c.
        move: Huniq => /(_ c) /=.
        case : (key_id k' =? c) => //=.
        rewrite ltnS => Hcount.
        by eapply leq_trans.
      move/(_ Hmem Huniq') in IH.
      by case H:update.
Qed.

Lemma newref_getE {T} x env :
  RunM (do s <- newref T x; getref T s) env = inl x.
Proof.
  rewrite /RunM /newref /getref /Bind.
  case: env => i l /=.
  by rewrite Nat.eqb_refl coerceE.
Qed.

Lemma setref_getE {T} x y env :
  mem_env x env -> envok env ->
  RunM (do _ <- setref T x y; getref T x) env = inl y.
Proof.
  rewrite /RunM /setref /getref /Bind.
  case: env => i l.
  case: x y => k y /= Hmem Huniq.
  case H : update => [s'|] => //=.
  move: (lookup_updateE k y l Hmem (proj1 Huniq)).
  rewrite H /= => -> //.
  by move/(updateok (mkbind k y) l Hmem (proj1 Huniq)) in H.
Qed.

Lemma getset_skip {T} x env : mem_env x env -> envok env ->
  (do s <- getref T x; setref T x s) env = Ret tt env.
Proof.
  case env => c refs.
  case x => k.
  rewrite /mem_env /envok => Hmem [] Huniq H.
  rewrite /Bind /getref.
  case H' : lookup => [val|] /=.
  - case H'' : update => [refs'|].
    + have -> : refs = refs' => //.
      move : H''.
      rewrite update_lookupE //.
      by move/Some_inj.
    + by move : (updateok (mkbind k val) refs Hmem Huniq).
  - by move : (lookupok k refs Hmem Huniq).
Qed.

Lemma newref_envok {T} x t env env' :
  newref T x env = (env', inl t) -> envok env -> envok env'.
Proof.
  case env => n refs.
  case env' => n' refs'.
  rewrite /newref /envok.
  move => [] Hn <- Ht [] Huniq Hltn.
  split => //=.
  - rewrite /uniq_bindings /= => c.
    case Hnc : (n =? c) => //=.
    + move/eqP : Hnc => <-.
      rewrite ltnS.
      move:Hltn.
      rewrite all_count; move/eqP.
      rewrite -(count_predC (fun b : binding M => key_id (bind_key M b) < n)).
      rewrite -[LHS]addn0; move/eqP; rewrite eqn_add2l; move/eqP.
      under eq_count => b /=.
        rewrite -leqNgt.
      over.
      move=> ->.
      apply sub_count.
      rewrite /subpred => b.
      move/eqP /esym.
      by apply eq_leq.
    + by apply Huniq.
  - rewrite -Hn addn1.
    apply/andP; split => //.
    move:Hltn.
    apply sub_all.
    rewrite /subpred => b H.
    by apply (@ltn_trans n).
Qed.

Lemma getref_envok {T} x t env env' :
  getref T x env = (env', inl t) -> envok env -> envok env'.
Proof.
  case env => n refs.
  case env' => n' refs'.
  case: x t => k val.
  rewrite /getref.
  by case Hlook : lookup => //= [val'] [] <- <-.
Qed.

Lemma setref_envok {T} x s env env' :
  setref T x s env = (env', inl tt) -> envok env -> envok env'.
Proof.
  case: env => n refs.
  case: env' => n' refs'.
  case: x s => k val.
  rewrite /setref.
  case Hup: update => //= [refs''] [] <- <-.
  elim: refs refs'' Hup => //= b refs IH refs''.
  case: b => k' val'.
  case Hid: (key_id k =? key_id k') => //=.
  - case ml_type_eq_dec => //= [Htype].
    move/Some_inj => Hrefs.
    rewrite -Hrefs /uniq_bindings /=.
    by move/eqP : Hid => ->.
  - rewrite /omap /obind /oapp.
    case Hup: update => //= [refs0].
    move/Some_inj => <- [] Huniq /andP [] Hidlt Hall /=.
    rewrite Hidlt /=.
    have H : uniq_bindings refs0 ->
      uniq_bindings ({| bind_key := k'; bind_val := val' |} :: refs0).
      move=> Huniq' c /=.
      move/(_ c) in Huniq'.
      case Hc : (key_id k' =? c) => //.
      move: (Huniq c) => /=.
      rewrite Hc /= !ltnS leqn0 => /eqP.
      admit.
    split.
    - apply H.
      apply IH => //.
      split => //.
      rewrite /uniq_bindings => c.
      move: (Huniq c) => /=.
      case: (key_id k' =? c) => //=.
      rewrite ltnS => Hcount.
      by eapply leq_trans.
    - apply IH => //.
      split => //.
      rewrite /uniq_bindings => c.
      move: (Huniq c) => /=.
      case: (key_id k' =? c) => //=.
      rewrite ltnS => Hcount.
      by eapply leq_trans.
Admitted.

Lemma fact_envok h n t env env':
  fact_for h n env = (env', inl t) -> envok env -> envok env'.
Proof.
Admitted.

Lemma newref_memok {T} x t env env' : 
  newref T x env = (env', inl t) -> mem_env t env'.
Proof.
  case env => n refs.
  case env' => n' refs'.
  rewrite /newref.
  move => [] Hn <- Ht.
  rewrite -Ht /mem_env /=.
  apply/orP;left.
  rewrite /key_eqb /=.
  apply/andP;split.
  - apply Nat.eqb_refl.
  - by case ml_type_eq_dec.
Qed.

Lemma getref_memok {T} x t env env' : 
  getref T x env = (env', inl t) -> mem_env x env'.
Proof.
  case env => n refs.
  case env' => n' refs'.
  case: x t => k val.
  rewrite /getref.
  case Hlook : (lookup k refs) => //= [val'] [] _ <- Ht.
  rewrite /mem_bindings.
  elim: refs Hlook => [|b refs IH] //=.
  case: b => k'' val''.
  case Hid : (key_id k =? key_id k'') => //=.
  - rewrite /coerce.
    case ml_type_eq_dec => //= Htype _.
    apply /orP; left.
    rewrite /key_eqb Hid //=.
    case ml_type_eq_dec => //=.
    by apply esym in Htype.
  - move=> H.
    apply /orP; right.
    by apply IH.
Qed.

Lemma getrefok {T} x  env e : mem_env x env -> envok env ->
  RunW (getref T x env) <> inr e.
Proof.
  case: env => n refs.
  case : x => k.
  rewrite /mem_env /envok /= => Hmem [] Huniq Hrefs.
  case Hlook : lookup => //=.
  by move: (lookupok k refs Hmem Huniq).
Qed.

Lemma setrefok {T} x s env : mem_env x env -> envok env ->
  RunW (setref T x s env) = inl tt.
Proof.
  case env => n refs.
  case : x s => k val.
  rewrite /mem_env /envok /= => Hmem [] Huniq _.
  case Hup : update => //.
  by move: (updateok {| bind_key := k; bind_val := val |} refs Hmem Huniq).
Qed.

Lemma N2int_1E : (N2int 1 = 1)%uint63.
Proof. by rewrite /N2int. Qed.

Lemma N2int_add n m :
  N2int (n + m) = (N2int n + N2int m)%uint63.
Proof.
  rewrite /N2int.
  rewrite Nat2Z.inj_add.
  rewrite Sint63.add_of_Z.
  apply Sint63.to_Z_inj.
  rewrite !Sint63.of_Z_spec.
  rewrite -Sint63.cmod_mod -[RHS]Sint63.cmod_mod.
  f_equal.
  rewrite /Sint63.cmod.
  have -> : (((Z.of_nat n + wB / 2) mod wB - wB / 2 +
            ((Z.of_nat m + wB / 2) mod wB - wB / 2)) =
            (Z.of_nat n + wB / 2) mod wB + (Z.of_nat m + wB / 2) mod wB -
            (wB / 2 + wB / 2))%Z by ring.
  rewrite [RHS]Z.add_mod //.
  have -> : (wB / 2 + wB / 2 = wB)%Z by [].
  have -> : (- wB = 0 - wB)%Z by [].
  rewrite [((0 - wB) mod wB)%Z]Z.add_mod //.
  rewrite Zmod_0_l -(Zmod_0_l wB).
  rewrite -[RHS]Z.add_mod // Z.add_0_r.
  rewrite -[RHS]Z.add_mod //.
  have -> : (Z.of_nat n + wB / 2 + (Z.of_nat m + wB / 2) =
            (Z.of_nat n + Z.of_nat m + (wB / 2 + wB / 2)))%Z by ring.
  have -> : ((wB / 2 + wB / 2) = wB)%Z by [].
  rewrite [RHS]Z.add_mod //.
  rewrite Z_mod_same_full -(Zmod_0_l wB).
  by rewrite -[RHS]Z.add_mod // Z.add_0_r.
Qed.

Lemma N2int_mul m n : (N2int m * N2int n)%uint63 =
  N2int (m * n).
Proof.
  elim : n => [|n IH] //=.
  - by rewrite muln0 {2 3}/N2int /=; ring.
  - rewrite mulnS N2int_add -IH.
    rewrite -addn1 N2int_add N2int_1E.
    by ring.
Qed.

Definition gasok {T} (f : T + Exn) :=
  match f with
  | inr GasExhausted => false
  | _ => true
  end.

Definition le_gasW {T} (f g : M T) := forall env, envok env ->
  gasok (RunW (f env)) -> RunW (f env) = RunW (g env).

Theorem fact_ok' h n : int2N n < expn 2 61 ->
  le_gasW (fact_for h n) (Ret (fact_rec_int n)).
Proof.
  move=> H env.
  rewrite /fact_for /gasok {1 7}/Bind.
  case H' : newref => [env' [s|e]] Henv.
  - rewrite !bindretf.
    rewrite -(int2NK n).
    have Henv' : envok env' by apply (@newref_envok ml_int 1%uint63 s env).
    have Hmem : mem_env s env' by apply (@newref_memok ml_int 1%uint63 s env).
    elim : (int2N n) H env' H' Henv' Hmem => [|n' IH] H env' H' Henv' Hmem.
    + rewrite /N2int /=.
      destruct h => //= _.
      move: (@newref_getE ml_int 1%uint63 env).
      by rewrite /RunM {1}/Bind H'.
    + rewrite {1 4}/Bind.
      move => Hgasok.
      move:(Hgasok).
      rewrite (forloop_cat h 1 (N2int n') (N2int n'.+1) _) //.
      - move/ltnW in H.
        move:(IH H env' H' Henv' Hmem).
        rewrite {1 4 7 12}/Bind.
        case Hfor : (forloop h 1 _ _ _) => [env0 [a|e]] IH'.
        + destruct h => //=.
          have -> : ltsb (N2int n'.+1) (N2int n' + 1) = false.
            rewrite -addn1 N2int_add N2int_1E.
            apply/Sint63.ltbP => //.
            by move/Z.lt_neq.
          rewrite !bindA {1 6}/Bind.
          case Hget : getref => [env0' [a'|e]].
          - rewrite !bindretf {1 4}/Bind.
            case Hset : setref => [env0'' [t|e]].
            + destruct h => //=.
              have -> : ltsb (N2int n'.+1) (N2int n' + 1 + 1) = true.
                rewrite -{1}N2int_1E -N2int_add addn1.
                apply ltsb_succ_nmax => Hlt.
                admit.
              move=> /= _.
              have Hmem' : mem_env s env0'.
                by apply (getref_memok s a' env0).
              have Henv'' : envok env0'.
                apply (getref_envok s a' env0) => //.
                admit.
              move : (@setref_getE ml_int s 
                      (a' * (N2int n' + 1))%uint63 env0' Hmem' Henv'').
              rewrite /RunM /Bind Hset => ->.
              f_equal.
              move : IH'.
              rewrite Hget /=.
              move/(_ isT) => [] ->.
              rewrite /fact_rec_int !N2intK /=.
                  by rewrite mulnC -N2int_mul -N2int_1E -N2int_add addn1.
                rewrite ltn_neqAle.
                apply/andP;split.
                - apply/negbT/eqP => Hn.
                  move:Hn H => ->.
                  by move:(@leq_exp2l 2 63 61 isT) => ->.
                - apply (ltn_trans H).
                  by rewrite ltn_exp2l.
              apply (ltn_trans H).
              by rewrite ltn_exp2l.
            + have Hmem' : mem_env s env0'.
                by apply (getref_memok s a' env0).
              have Henv'' : envok env0'.
                apply (getref_envok s a' env0) => //.
                admit.
              move:(setrefok s (a' * (N2int n' + 1))%uint63 env0' Hmem' Henv'').
              by rewrite Hset.
          - admit.
        + move:IH'.
          rewrite -/(gasok (@inr unit _ e)).
          by case gasok => // /(_ isT).
      - move:H; clear; simpl => H.
        apply /Sint63.lebP.
        rewrite /N2int Sint63.of_Z_spec.
        rewrite Sint63.cmod_small.
          by apply Zle_0_nat.
        split.
        + apply (Z.le_trans _ 0%Z _) => //.
          by apply Zle_0_nat.
        + have -> : (wB / 2 = Z.of_nat (2 ^ 62))%Z.
            rewrite /wB /size.
            rewrite -{2}(Z.pow_1_r 2%Z).
            rewrite -Z.pow_sub_r.
            have -> : (Z.of_nat 63 - 1 = 62)%Z by [].
            have H' : (0 <= (2 ^ 62))%Z.
              admit.
            move:(Z_of_nat_complete (2 ^ 62)%Z H').

            Search (_ ^ _)%Z. Search (_%Z = Z.of_nat _).
            have -> : (63 - 1 = 62)%Z by [].
            have H' : forall m n,
                      m = Z.of_nat n -> (2 ^ m)%Z = Z.of_nat (2 ^ n).
             Print wB.
         admit.
      - admit.
      - admit.
      - move:Hgasok.
        case : forloop => env'' [a|e] //.
        move=> Hgasok [] H''.
        by rewrite H'' in Hgasok.
  - case: env H' Henv => n' refs Henv //.
Admitted.
