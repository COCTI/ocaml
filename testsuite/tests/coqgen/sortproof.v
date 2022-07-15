From mathcomp Require Import all_ssreflect.
Require Import Sint63 Ascii String Floats cocti_defs test2.

Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.

Lemma bindretf A B (a : A) (f : A -> M B) : Ret a >>= f = f a.
Proof.
  rewrite /Bind /=.
  exact: funext.
Qed.

Lemma bindmret A (m : M A) : m >>= Ret = m.
Proof.
  rewrite /Bind /=.
  apply funext => env /=.
  by case: (m env) => env' [] r.
Qed.

Definition fmap A B (f : A -> B) (m : M A) : M B :=
  m >>= fun a => Ret (f a).

Lemma bindA A B C (m : M A) (f : A -> M B) (g : B -> M C) :
  (m >>= f) >>= g = m >>= (fun x => f x >>= g).
Proof.
  rewrite /Bind.
  apply funext => env.
  by case: (m env) => env' [] r.
Qed.

Lemma bind_if A B (b : bool) (m : M A) (f g : A -> M B) :
  m >>= (fun x => if b then f x else g x) = if b then m >>= f else m >>= g.
Proof. by case: ifPn. Qed.

Lemma if_bind A B (b : bool) (m n : M A) (f : A -> M B) :
  (if b then m else n) >>= f = (if b then m >>= f else n >>= f).
Proof. by case: ifPn. Qed.

Section Sort.
Definition le x y := if Sint63.compare x y is Gt then false else true.

Fixpoint sorted l := (* all を使って bool 上の述語を定義する *)
  if l is a :: l' then all (le a) l' && sorted l' else true.

Lemma compare_ok h x y : ml_le h.+1 ml_int x y = Ret (le x y).
Proof. exact: funext. Qed.

Lemma insert_pure h b l l' env env' : insert h ml_int b l env = Ret l' env'
  -> insert h ml_int b l = Ret l'.
Proof.
  elim: h l l' => //= h IH [l [] _ <-|a l l'] //.
  destruct h => //.
  rewrite compare_ok (lock (h.+1)) !bindretf.
  case: ifPn => [leba [] _ <-|nleba] //.
  rewrite -lock /Bind.
  move H : (insert h.+1 ml_int b l env) => [env0 r].
  case: r H => // a0 H [] henv <-.
  apply funext => env''.
  by rewrite (IH l a0) // H henv.
Qed.

Lemma happly [A B] [f g : A -> B] x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

Corollary insert_env h b l l' env env' :
 insert h ml_int b l env = Ret l' env' -> env = env'.
Proof.
  move=> H.
  move:(H) => /insert_pure.
  move/(happly env).
  by rewrite H => -[] <-.
Qed.

Lemma isort_pure h l l' env env' : isort h ml_int l env = Ret l' env'
  -> isort h ml_int l = Ret l'.
Proof.
  elim: h l l' => // h IH [_ [] _ <- |a l l'] //=.
  rewrite /Bind.
  move H : (isort h ml_int l env) => [env0 r].
  case: r H => // l'' H H'.
  apply funext => env''.
  rewrite (IH l l'') /=.
  + by move: H' => /insert_pure ->.
  + rewrite H.
    move:H'.
    by move /insert_env <-.
Qed.

Lemma le_seq_insert h a b l l' : insert h ml_int b l = Ret l' ->
  le a b -> all (le a) l -> all (le a) l'.
Proof.
  elim: h l l' => /= [_ _ |h IH [|c l] l'] /(happly empty_env) //.
  - by move=> -[] /= <- /= ->.
  - rewrite /Bind.
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

Lemma eq_intP : Equality.axiom (fun (x y : int) => (x =? y)%sint63).
Proof.
  move=> x y.
  apply: (iffP idP) => [|<-].
  apply eqb_correct.
  by rewrite Uint63.eqb_refl.
Qed.

Definition eq_int_mixin := EqMixin eq_intP.
Canonical int_eqType := Eval hnf in EqType _ eq_int_mixin.

Lemma le_trans : forall x y z, le x y -> le y z -> le x z.
Proof.
  move=> x y z.
  rewrite /le.
  rewrite !Sint63.compare_spec.
  case H1 : (BinInt.Z.compare (to_Z x) (to_Z y)) => _ //=.
  - move: H1.
    by move/(BinInt.Z.compare_eq) => <-.
  - case H2 : (BinInt.Z.compare (to_Z y) (to_Z z)) => _ //=.
    + move: H2.
      move/(BinInt.Z.compare_eq) => <-.
      by rewrite H1.
    + by rewrite (Zcompare.Zcompare_Lt_trans _ (to_Z y) _).
Qed.

Lemma le_total : forall x y, ~~ le x y -> le y x.
Proof.
  move=> x y.
  rewrite /le.
  rewrite !Sint63.compare_spec.
  case H : (BinInt.Z.compare (to_Z x) (to_Z y)) => //=.
  move: H.
  rewrite -(Zcompare.Zcompare_antisym).
  by rewrite CompOpp_iff /= => ->.
Qed.

Lemma le_seq_trans a b l : le a b -> all (le b) l -> all (le a) l.
Proof.
  move=> leab /allP lebl.
  apply/allP => x Hx.
  by apply/le_trans/lebl.
Qed.

Lemma insert_ok h a l l' : insert h ml_int a l = Ret l' ->
  sorted l -> sorted l'.
Proof.
  elim: h l l' => [_ _ |h IH[|c l] l'] /(happly empty_env) //=.
  - by move=> [] <-.
  - destruct h => //.
    rewrite compare_ok (lock (h.+1)) /=.
    rewrite bindretf.
    case: ifPn.
    + move=> leac [] <- /andP [] leall sortedl /=.
      by rewrite leac leall sortedl (le_seq_trans a c l).
    + move=> nleac.
      rewrite -lock /Bind.
      move H : (insert h.+1 ml_int a l empty_env) => [env' r].
      case: r H => // l'' H [] henv <- /andP [] leall sortedl /=.
      apply /andP.
      split.
      - rewrite (le_seq_insert h.+1 c a l l'') //.
        by apply (insert_pure _ _ _ _ empty_env env').
        by apply le_total.
      - move/ insert_pure /IH in H.
        by rewrite H.
Qed.

Theorem isort_ok h l l' : isort h ml_int l = Ret l' -> sorted l'.
Proof.
  elim: h l l' => [_ _ |h IH [|c l] l'] /(happly empty_env) //=.
  - by move=> [] <-.
  - rewrite /Bind.
    destruct h => //.
    move H : (isort h.+1 ml_int l empty_env) => [env r].
    case: r H => // l'' H H'.
    apply (insert_ok h.+1 c l'' l').
    - apply /(insert_pure _ _ _ _ env empty_env) /H'.
    - apply /(IH l l'') /(isort_pure _ _ _ empty_env env) /H.
Qed.
