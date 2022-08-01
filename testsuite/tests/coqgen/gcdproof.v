From mathcomp Require Import all_ssreflect.
Require Import Sint63 Ascii String Floats cocti_defs test2 sortproof.

Definition divisible m n := ((mods m n) =? 0%sint63)%sint63.

Eval compute in divisible 2 4.

Definition eq x y := if Sint63.compare x y is Eq then true else false.

Lemma eq_ok h m n : ml_eq h.+1 ml_int m n = Ret (m =? n)%sint63.
Proof.
  rewrite /ml_eq /wrap_compare /compare_rec bindretf.
  case H : (m =? n)%sint63.
  - move/eqb_correct in H.
    by rewrite H Sint63.compare_spec BinInt.Z.compare_refl.
  - move:H => /eqbP.
    rewrite -BinInt.Z.compare_eq_iff Sint63.compare_spec.
    by case BinInt.Z.compare.
Qed.

Lemma rem_same' n : BinInt.Z.rem (to_Z n) (to_Z n) = to_Z 0.
Proof.
  case H : (n =? 0)%sint63.
  - move/eqbP in H.
    by rewrite H PreOmega.Z.rem_0_r_ext.
  - move/eqbP in H.
    by rewrite BinInt.Z.rem_same.
Qed.

Lemma mod_0_r m : (m mod 0)%sint63 = m.
Proof.
  apply to_Z_inj.
  by rewrite mod_spec PreOmega.Z.rem_0_r_ext.
Qed.

Lemma mod_0_l m : to_Z m <> to_Z 0 -> (0 mod m)%sint63 = 0%sint63.
Proof.
  move=> Hm.
  apply to_Z_inj.
  by rewrite mod_spec BinInt.Z.rem_0_l.
Qed.

Lemma div_mod m n :
  forall x : int, divisible m x -> divisible n x -> divisible (n mod m) x.
Proof.
  rewrite /divisible => x.
  case Hx : (x =? 0)%sint63.
  - move/eqbP /to_Z_inj in Hx.
    rewrite Hx !mod_0_r => /eqbP /to_Z_inj ->.
    by rewrite mod_0_r.
  - case Hm : (m =? 0)%sint63.
    + move/eqbP /to_Z_inj in Hm.
      by rewrite Hm mod_0_r.
    + move/eqbP in Hx.
      move/eqbP; rewrite mod_spec; move/(BinInt.Z.quot_exact) => Hmx.
      move/eqbP; rewrite mod_spec; move/(BinInt.Z.quot_exact) => Hnx.
      apply /eqbP; rewrite !mod_spec Hmx // Hnx //.
      rewrite BinInt.Z.mul_rem_distr_l //.
      rewrite BinInt.Z.mul_comm.
      apply BinInt.Z.rem_mul => //.
      move=> H''.
      rewrite H'' BinInt.Z.mul_0_r in Hmx.
      move/eqbP in Hm.
      by apply /Hm /Hmx.
Qed.

(*gcd is greatest*)
Theorem Gcd h m n k :
   gcd h m n = Ret k ->
   forall x : int, (divisible m x) && (divisible n x) -> divisible k x.
Proof.
  elim: h m n => [_ _ /failret| h IH m n] //=.
  destruct h => //.
  - by rewrite bindfailf => /failret.
  - rewrite eq_ok bindretf.
    case: ifPn => _.
    + by move/ret_inj => <- x /andP [].
    + move=> H x /andP [divmx divnx].
      apply (IH (n mod m)%sint63 m) => //.
      apply /andP; split => //.
      by apply div_mod.
Qed.

Lemma gcd_0_l h m k :
 gcd h 0%sint63 m = Ret k -> m = k.
Proof.
  case: h => [/failret| [|h]] //=.
  - by move/failret.
  - by move/ret_inj.
Qed.

Lemma gcd_0_r h m k :
 gcd h m 0%sint63 = Ret k -> m = k.
Proof.
  case: h => [/failret|/= h] //=.
  destruct h.
  - by move/failret.
  - rewrite eq_ok bindretf.
    case: ifPn.
    + by move/eqbP /to_Z_inj => <- /ret_inj.
    + move/eqbP => Hm.
      by rewrite mod_0_l // => /gcd_0_l.
Qed.

Lemma gcd_pure h m n : pure (gcd h m n).
Proof.
  elim: h m n => [|h IH] m n /=.
  - by right; eexists.
  - destruct h => //.
    + by right; eexists.
    + Admitted.

Lemma gcd_ok'' h m k : to_Z m <> to_Z 0 ->
  gcd h.+2 0%sint63 m = Ret k -> gcd h.+1 m 0%sint63 = Ret k.
Proof.
  move=> H.
  have H' : (m =? 0)%sint63 = false.
    by apply /eqbP.
  elim: h m k H H' => [|h IH] m k H H'.
  - move=> /=.
    rewrite eq_ok bindretf /=.
Restart.
  move=> H /=.
  rewrite eq_ok bindretf mod_0_r mod_0_l //=.
Admitted.

Lemma gcd_ok' h m k : to_Z m <> to_Z 0 ->
  gcd h.+3 0%sint63 m = Ret k -> gcd h.+2 0%sint63 m = Ret k.
Proof.
  move=> H /=.
  by rewrite eq_ok bindretf mod_0_l mod_0_r.
Qed.

Lemma gcd_one_step h m n k : to_Z m <> to_Z 0 ->
  gcd h.+2 m n = Ret k -> gcd h.+1 (n mod m)%sint63 m = Ret k.
Proof.
  move=> Hm /=.
  rewrite eq_ok bindretf.
  have Hm' : (m =? 0)%sint63 = false.
    by apply/eqbP.
  by rewrite Hm'.
Qed.

(*Lemma gcd_mul h m n k : (n mod m)%sint63 = 0%sint63 ->
  gcd h.+1 0%sint63 m = Ret k -> gcd h.+1 m n = Ret k.
Proof.
Admitted.*)

Lemma gcd_ok h m n k :
  gcd h.+1 (n mod m)%sint63 m = Ret k -> gcd h.+1 m n = Ret k.
Proof.
  move=> H.
  elim: h m n H => [|h IH m n H] //=.
  rewrite eq_ok bindretf.
  case: ifPn.
  - move /eqbP /to_Z_inj => Hnm.
    congr Ret.
    apply (gcd_0_r h.+2).
    by rewrite -H Hnm mod_0_r.
  - move/eqbP => Hm.
    case Hnm : ((n mod m) =? 0)%sint63.
    + move/eqbP /to_Z_inj in Hnm.
      apply IH.
      rewrite Hnm mod_0_r.
      apply gcd_ok'' => //.
      by rewrite -Hnm.
    + apply IH.
      apply gcd_one_step in H => //.
      apply/eqbP.
      by rewrite Hnm.
Qed.

(*gcd is common divisor*)
Theorem gCD n m k : gcd h n m = Ret k -> (divisible n k) && (divisible m k).
Proof.
  elim: h n m => [_ _ /failret | h IH m n] //=.
  destruct h => //.
  - rewrite bindfailf.
    by move/failret.
  - rewrite eq_ok bindretf.
    case: ifPn => H.
    + move/ret_inj <-.
      rewrite /divisible.
      apply /andP.
      split.
      - apply /eqbP.
        rewrite mod_spec.
        move/eqbP in H.
        by rewrite H.
      - apply /eqbP.
        by rewrite mod_spec rem_same'.
    + move=> H1.
      apply IH.
      by apply (gcd_ok _ _ _ k).
Qed.

Lemma gcd_com m n k : gcd h m n = Ret k -> gcd h n m = Ret k.
Proof.
  elim: h m n => [m n /failret|h IH m n] //.
  destruct h => //.
  move=> H /=.
  rewrite eq_ok bindretf.
  case: ifPn.
  - move/eqbP /to_Z_inj => Hn.
    congr Ret.
    apply (gcd_0_r h.+2).
    by rewrite -Hn.
  - move/eqbP => Hn.
Admitted.