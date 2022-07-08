From mathcomp Require Import all_ssreflect.
Require Import Sint63 Ascii String Floats cocti_defs test2.

Definition le x y := if Sint63.compare x y is Gt then false else true.

Fixpoint sorted l := (* all を使って bool 上の述語を定義する *)
  if l is a :: l' then all (le a) l' && sorted l' else true.

Lemma compare_ok h x y : ml_le h.+1 ml_int x y =1 Ret (le x y).
Proof. by move=> env. Qed.

Lemma insert_pure h b l l' env env' : insert h ml_int b l env = Ret l' env'
  -> insert h ml_int b l =1 Ret l'.
Proof.
Admitted.

Lemma le_seq_insert h a b l l' : insert h ml_int b l =1 Ret l' ->
  le a b -> all (le a) l -> all (le a) l'.
Proof.
  elim: h l l' => [_ _ /(_ empty_env) |h IH [|c l] l'] //=.
  - by move/(_ empty_env) => -[] /= <- /= ->.  - move/(_ empty_env) => /=.
    rewrite /Bind.
    destruct h => //.
    rewrite compare_ok (lock (h.+1)) /=.
    case: ifPn.
    + move=> lebc [] <- leab /andP [] leac leall /=.
      by rewrite leab leac.
    + move=> nlebc.
      rewrite -lock.
      move H : (insert h.+1 ml_int b l empty_env) => [env' r].
      case: r H => // l'' H [] henv <- leab /andP [] leac leall /=.
      move/ insert_pure /IH in H.
      by rewrite leac H.
Qed.

About allP.
About eqb_correct.
Search Sint63.compare.
Search "to_Z_inj".

Lemma le_seq_trans a b l : le a b -> all (le b) l -> all (le a) l.
Proof.
  move=> leab /allP. lebl.
  apply/allP => x Hx.
  by apply/le_trans/lebl.
Qed.

Lemma insert_ok : .
Proof.

Qed.


Theorem isort_ok h l l' : isort h ml_int l =1 Ret l' -> sorted l'.
Proof.

Qed.

