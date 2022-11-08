(* These are not used in ref_proof.v *)

(* Lemma bindinl {A} {B} {m : M A} {env} {env'} {a} {e : M B} :
  m env = (env', inl a) -> (m >> e) env = e env'.
Proof. by rewrite /Bind => ->. Qed. *)

(* Lemma fact_closed h n m env env' env'' : fact_for h n env = (Ret m) env' ->
  (fact_for h n env).2 = (fact_for h n env'').2.
Proof.
  rewrite /fact_for /=.
  elim: h env env' => [ |h IH] env env'.
  -
  -
Admitted. *)

(*Lemma fact_for_neg h n : int_to_nat n = 0 ->
  fact_for h.+1 n = Ret 1%uint63.
Proof.
  move=> Hn.
  elim: h => [/(happly empty_env)|h IH] //.
  apply IH.
  rewrite /fact_for.
Qed. *)

(* Lemma lesb_spec m n : lesb m n -> compares m n <> Gt.
Proof.
  move/Sint63.lebP.
  rewrite Sint63.compare_spec.
  by rewrite Z.compare_le_iff.
Qed.

Lemma lesb_spec' m n : lesb m n -> compares n m <> Lt.
Proof.
  move/Sint63.lebP.
  rewrite Sint63.compare_spec.
  by rewrite Z.compare_ge_iff.
Qed. *)

(* Lemma compare_succ n : n <> Sint63.max_int -> compares (n + 1) n = Gt.
Proof.
  move => H.
  rewrite Sint63.compare_spec Sint63.to_Z_succ //.
  by rewrite Z.add_1_r Zcompare_succ_Gt.
Qed.

Lemma compare_succ_notEq n : compares (n + 1) n <> Eq.
Proof.
  case H : (n == Sint63.max_int).
  - by move: H => /eqP ->.
  - move/eqP in H.
    by rewrite compare_succ.
Qed.

Lemma compare_Lt_succ_le m n : compares m n = Lt -> lesb (succ m) n.
Proof.
  case H : (m == Sint63.max_int).
  - move:H => /eqP -> H.
    apply/Sint63.lebP => /=.
    by apply Sint63.to_Z_bounded.
  - move:H => /eqP => H.
    rewrite Sint63.compare_spec Z.compare_lt_iff.
    rewrite -Z.le_succ_l -Z.add_1_r -Sint63.to_Z_succ //.
  by rewrite -Sint63.leb_spec.
Qed.

Lemma Lt_not_loop m n : n <> Sint63.max_int -> compares m n = Lt ->
  (1 <=? n - m + 1)%uint63.
Proof.
  move=> H.
  rewrite Sint63.compare_spec Z.compare_lt_iff => ltmns.
Admitted. *)

(* Lemma int_to_natE m n : (n <=? m + n)%uint63 ->
  int_to_nat (m + n) = int_to_nat m + int_to_nat n.
Proof.
  move => H.
  rewrite /int_to_nat add_spec.
  have -> : (Z.to_nat φ (m)%uint63 + Z.to_nat φ (n)%uint63) =
            (Z.to_nat φ (m)%uint63 + Z.to_nat φ (n)%uint63)%coq_nat => //. 
  rewrite -Z2Nat.inj_add.
  congr Z.to_nat.
  apply Z.mod_small.
  split; last first.
    move: add_le_r => /(_ m n).
    by rewrite H.
  apply Z.add_nonneg_nonneg.
  all: apply to_Z_bounded.
Qed. *)

(* Lemma Eq_to_eq m n : compares m n = Eq -> m = n.
Proof.
  rewrite Sint63.compare_spec.
  by move /Z.compare_eq  /Sint63.to_Z_inj.
Qed.

Lemma int_to_nat_1 : 1 = int_to_nat 1.
Proof. by rewrite /int_to_nat to_Z_1. Qed. *)

(* Lemma forloop_mono' h m n b : n <> Sint63.max_int ->
  (1 <=? n - m + 2)%uint63 -> int_to_nat (n - m + 2) <= h ->
  forloop h m n b = forloop h.+1 m n b.
Proof.
  move=> Hn.
  elim: h m => [|h IH] m H.
  - rewrite /int_to_nat -{1}Z2Nat.inj_0 => /leP.
    move: to_Z_bounded => /(_ (n - m + 2)%uint63) [H' _].
    rewrite -Z2Nat.inj_le // => H''.
    have : (0 <= φ (n - m + 2)%uint63 <= 0)%Z.
      by split.
    rewrite -ZMicromega.eq_le_iff.
    rewrite -to_Z_0 => /to_Z_inj => H'''.
    move:H.
    by rewrite -H'''.
  - move=> Hgas /=.
    case H' : (compares m n) => //.
    + move:H' Hgas.
      rewrite Sint63.compare_spec.
      move /Z.compare_eq /Sint63.to_Z_inj ->.
      destruct h => [|H'] /=.
      - rewrite /int_to_nat.
        by rewrite add_spec sub_spec Z.sub_diag Zmod_0_l.
      - by rewrite compare_succ //.
    + rewrite (IH (m + 1)%uint63) //.
        admit.
      rewrite -(leq_add2r 1 _ h) //.
      have H'' : ((n - (m + 1) + 2 + 1) = (n - m + 2))%uint63.
        admit.
      rewrite {1}int_to_nat_1 -int_to_natE.
      all: rewrite H'' ?addn1 //.
Admitted. *)

(* Lemma forloop_cat h m n p b : lesb 0 m -> lesb m n ->
  lesb n (n + 1) -> lesb (n + 1) p ->
  int_to_nat (p - m) <= h ->
  forloop h m n b >> forloop h (n + 1)%uint63 p b = forloop h m p b.
Proof.
  elim: h m => [|h IH] m //.
  rewrite {3}(lock h.+1).
  move=> Hm Hmn Hnn' Hnp Hpm.
  case H: (compares m n) => //=.
  - rewrite Sint63.compare_spec in H.
    apply Z.compare_eq in H.
    apply Sint63.to_Z_inj in H.
    rewrite H.
    destruct h => //=.
    + (* rewrite bindA !bindfailf.
      case H' : (compares n p) => //.
      move: H'.
      rewrite Sint63.compare_spec.
      move/ Z.compare_nle_iff.
      elim.
      move: (Hnp).
      move/ Sint63.lebP.
      apply /Z.le_trans.
      by apply /Sint63.lebP.
    + rewrite Sint63.compare_spec.
      move/ Sint63.lebP in Hnn'.
      Search (_ <= _)%Z (_ ?= _)%Z.
      move/ Z.compare_ge_iff in Hnn'.
      case H' : (Sint63.to_Z (n + 1) ?= Sint63.to_Z n)%Z => //.
      - apply Z.compare_eq in H'.
        case H'' : (eqb n max_int).
        + move/ eqb_correct in H''.
          move/ Sint63.to_Z_inj in H'.
          rewrite H'' /= in H'.
          by move/ eqb_complete in H'.
        + 
      -
  -
  -


  - case: (compares (n + 1) p) => //=.
    + case: (compares m p) => //=.
      rewrite /Bind.
    +
    +
  -
  -
*)
Admitted. *)

