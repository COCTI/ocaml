From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs.

(* Generated representation of all ML types *)
data ml_type : Set where
  ml-int : ml_type
  ml-char : ml_type
  ml-float : ml_type
  ml-bool : ml_type
  ml-unit : ml_type
  ml-exn : ml_type
  ml-array : ml_type → ml_type
  ml-list : ml_type → ml_type
  ml-lazy : ml_type → ml_type
  ml-string : ml_type
  ml-empty : ml_type
  ml-array-t : ml_type → ml_type
  ml_my_opt : ml_type → ml_type
  ml_even_int : ml_type
  ml_quadruplet : ml_type → ml_type → ml_type → ml_type → ml_type
  ml_my_list : ml_type → ml_type
  ml-lazy-val : ml_type → ml_type
  ml-ref : ml_type → ml_type
  ml-arrow : ml_type → ml_type → ml_type

variable
 u1 u2 u3 u4 u5 u6 v1 v2 v3 v4 v5 v6 : ml-type

-- Proof of DecidableEquality on ml-type

data _~_ : (T1 T2 : ml-type) → Set where
  ~ml-int : ml-int ~ ml-int
  ~ml-char : ml-char ~ ml-char
  ~ml-float : ml-float ~ ml-float
  ~ml-bool : ml-bool ~ ml-bool
  ~ml-unit : ml-unit ~ ml-unit
  ~ml-exn : ml-exn ~ ml-exn
  ~ml-array : (u1 v1 : ml-type) → ml-array u1 ~ ml-array v1
  ~ml-list : (u1 v1 : ml-type) → ml-list u1 ~ ml-list v1
  ~ml-lazy : (u1 v1 : ml-type) → ml-lazy u1 ~ ml-lazy v1
  ~ml-string : ml-string ~ ml-string
  ~ml-empty : ml-empty ~ ml-empty
  ~ml-array-t : (u1 v1 : ml-type) → ml-array-t u1 ~ ml-array-t v1
  ~ml_my_opt : (u1 v1 : ml-type) → ml_my_opt u1 ~ ml_my_opt v1
  ~ml_even_int : ml_even_int ~ ml_even_int
  ~ml_quadruplet : (u1 u2 u3 u4 v1 v2 v3 v4 : ml-type) → ml_quadruplet u1 u2 u3 u4 ~ ml_quadruplet v1 v2 v3 v4
  ~ml_my_list : (u1 v1 : ml-type) → ml_my_list u1 ~ ml_my_list v1
  ~ml-lazy-val : (u1 v1 : ml-type) → ml-lazy-val u1 ~ ml-lazy-val v1
  ~ml-ref : (u1 v1 : ml-type) → ml-ref u1 ~ ml-ref v1
  ~ml-arrow : (u1 u2 v1 v2 : ml-type) → ml-arrow u1 u2 ~ ml-arrow v1 v2

view : (T1 T2 : ml-type) →  Maybe (T1 ~ T2)
view ml-int ml-int = just ~ml-int
view ml-char ml-char = just ~ml-char
view ml-float ml-float = just ~ml-float
view ml-bool ml-bool = just ~ml-bool
view ml-unit ml-unit = just ~ml-unit
view ml-exn ml-exn = just ~ml-exn
view (ml-array u1) (ml-array v1) = just (~ml-array u1 v1)
view (ml-list u1) (ml-list v1) = just (~ml-list u1 v1)
view (ml-lazy u1) (ml-lazy v1) = just (~ml-lazy u1 v1)
view ml-string ml-string = just ~ml-string
view ml-empty ml-empty = just ~ml-empty
view (ml-array-t u1) (ml-array-t v1) = just (~ml-array-t u1 v1)
view (ml_my_opt u1) (ml_my_opt v1) = just (~ml_my_opt u1 v1)
view ml_even_int ml_even_int = just ~ml_even_int
view (ml_quadruplet u1 u2 u3 u4) (ml_quadruplet v1 v2 v3 v4) = just (~ml_quadruplet u1 u2 u3 u4 v1 v2 v3 v4)
view (ml_my_list u1) (ml_my_list v1) = just (~ml_my_list u1 v1)
view (ml-lazy-val u1) (ml-lazy-val v1) = just (~ml-lazy-val u1 v1)
view (ml-ref u1) (ml-ref v1) = just (~ml-ref u1 v1)
view (ml-arrow u1 u2) (ml-arrow v1 v2) = just (~ml-arrow u1 u2 v1 v2)
view _ _ = nothing

view-diag : (T : ml-type) → ¬ (view T T ≡ nothing)
view-diag ml-int()
view-diag ml-char()
view-diag ml-float()
view-diag ml-bool()
view-diag ml-unit()
view-diag ml-exn()
view-diag (ml-array _) ()
view-diag (ml-list _) ()
view-diag (ml-lazy _) ()
view-diag ml-string()
view-diag ml-empty()
view-diag (ml-array-t _) ()
view-diag (ml_my_opt _) ()
view-diag ml_even_int()
view-diag (ml_quadruplet _ _ _ _) ()
view-diag (ml_my_list _) ()
view-diag (ml-lazy-val _) ()
view-diag (ml-ref _) ()
view-diag (ml-arrow _ _) ()

ml-array-inj : ml-array u1 ≡ ml-array v1 → (u1 ≡ v1)
ml-array-inj refl = refl

ml-list-inj : ml-list u1 ≡ ml-list v1 → (u1 ≡ v1)
ml-list-inj refl = refl

ml-lazy-inj : ml-lazy u1 ≡ ml-lazy v1 → (u1 ≡ v1)
ml-lazy-inj refl = refl

ml-array-t-inj : ml-array-t u1 ≡ ml-array-t v1 → (u1 ≡ v1)
ml-array-t-inj refl = refl

ml_my_opt-inj : ml_my_opt u1 ≡ ml_my_opt v1 → (u1 ≡ v1)
ml_my_opt-inj refl = refl

ml_quadruplet-inj : ml_quadruplet u1 u2 u3 u4 ≡ ml_quadruplet v1 v2 v3 v4 → up4 (u1 ≡ v1) (u2 ≡ v2) (u3 ≡ v3) (u4 ≡ v4)
ml_quadruplet-inj refl = refl ,,, refl ,,, refl ,,, refl

ml_my_list-inj : ml_my_list u1 ≡ ml_my_list v1 → (u1 ≡ v1)
ml_my_list-inj refl = refl

ml-lazy-val-inj : ml-lazy-val u1 ≡ ml-lazy-val v1 → (u1 ≡ v1)
ml-lazy-val-inj refl = refl

ml-ref-inj : ml-ref u1 ≡ ml-ref v1 → (u1 ≡ v1)
ml-ref-inj refl = refl

ml-arrow-inj : ml-arrow u1 u2 ≡ ml-arrow v1 v2 → _×_ (u1 ≡ v1) (u2 ≡ v2)
ml-arrow-inj refl = refl , refl

ml-array-cong : (u1 ≡ v1) → ml-array u1 ≡ ml-array v1
ml-array-cong (refl) = refl

ml-list-cong : (u1 ≡ v1) → ml-list u1 ≡ ml-list v1
ml-list-cong (refl) = refl

ml-lazy-cong : (u1 ≡ v1) → ml-lazy u1 ≡ ml-lazy v1
ml-lazy-cong (refl) = refl

ml-array-t-cong : (u1 ≡ v1) → ml-array-t u1 ≡ ml-array-t v1
ml-array-t-cong (refl) = refl

ml_my_opt-cong : (u1 ≡ v1) → ml_my_opt u1 ≡ ml_my_opt v1
ml_my_opt-cong (refl) = refl

ml_quadruplet-cong : up4 (u1 ≡ v1) (u2 ≡ v2) (u3 ≡ v3) (u4 ≡ v4) → ml_quadruplet u1 u2 u3 u4 ≡ ml_quadruplet v1 v2 v3 v4
ml_quadruplet-cong (refl ,,, refl ,,, refl ,,, refl) = refl

ml_my_list-cong : (u1 ≡ v1) → ml_my_list u1 ≡ ml_my_list v1
ml_my_list-cong (refl) = refl

ml-lazy-val-cong : (u1 ≡ v1) → ml-lazy-val u1 ≡ ml-lazy-val v1
ml-lazy-val-cong (refl) = refl

ml-ref-cong : (u1 ≡ v1) → ml-ref u1 ≡ ml-ref v1
ml-ref-cong (refl) = refl

ml-arrow-cong : _×_ (u1 ≡ v1) (u2 ≡ v2) → ml-arrow u1 u2 ≡ ml-arrow v1 v2
ml-arrow-cong (refl , refl) = refl

eq-decc : (T1 T2 : ml-type) → Dec (T1 ≡ T2) 
eq-decc T1 T2 with view T1 T2 | inspect (view T1) T2
eq-decc _ _ | just ~ml-int | _ = yes refl
eq-decc _ _ | just ~ml-char | _ = yes refl
eq-decc _ _ | just ~ml-float | _ = yes refl
eq-decc _ _ | just ~ml-bool | _ = yes refl
eq-decc _ _ | just ~ml-unit | _ = yes refl
eq-decc _ _ | just ~ml-exn | _ = yes refl
eq-decc _ _ | just (~ml-array u1 v1) | _ = map′ ml-array-cong ml-array-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-list u1 v1) | _ = map′ ml-list-cong ml-list-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-lazy u1 v1) | _ = map′ ml-lazy-cong ml-lazy-inj ((eq-decc u1 v1))
eq-decc _ _ | just ~ml-string | _ = yes refl
eq-decc _ _ | just ~ml-empty | _ = yes refl
eq-decc _ _ | just (~ml-array-t u1 v1) | _ = map′ ml-array-t-cong ml-array-t-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml_my_opt u1 v1) | _ = map′ ml_my_opt-cong ml_my_opt-inj ((eq-decc u1 v1))
eq-decc _ _ | just ~ml_even_int | _ = yes refl
eq-decc _ _ | just (~ml_quadruplet u1 u2 u3 u4 v1 v2 v3 v4) | _ = map′ ml_quadruplet-cong ml_quadruplet-inj (up4-dec (eq-decc u1 v1) (eq-decc u2 v2) (eq-decc u3 v3) (eq-decc u4 v4))
eq-decc _ _ | just (~ml_my_list u1 v1) | _ = map′ ml_my_list-cong ml_my_list-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-lazy-val u1 v1) | _ = map′ ml-lazy-val-cong ml-lazy-val-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-ref u1 v1) | _ = map′ ml-ref-cong ml-ref-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-arrow u1 u2 v1 v2) | _ = map′ ml-arrow-cong ml-arrow-inj (_×-dec_ (eq-decc u1 v1) (eq-decc u2 v2))
eq-decc m n | nothing | [ eq ] = no λ where refl → view-diag _ eq

-- End of the proof of DecidableEquality on ml-type

(* Module argument for monadic functor *)
Module MLtypes.
Definition ml_type_eq_dec (T1 T2 : ml_type) : {T1=T2}+{T1<>T2}.
revert T2; induction T1; destruct T2;
  try (right; intro; discriminate); try (now left);
  try (case (IHT1_5 T2_5); [|right; injection; intros; contradiction]);
  try (case (IHT1_4 T2_4); [|right; injection; intros; contradiction]);
  try (case (IHT1_3 T2_3); [|right; injection; intros; contradiction]);
  try (case (IHT1_2 T2_2); [|right; injection; intros; contradiction]);
  (case (IHT1 T2) || case (IHT1_1 T2_1)); try (left; now subst);
    right; injection; intros; contradiction.
Defined.

Definition ml_type_eq_mixin := EqMixin (comparePc _ ml_type_eq_dec).
Canonical ml_type_eqType := Eval hnf in EqType _ ml_type_eq_mixin.

Local Definition ml_type := ml_type_eqType.
Local Notation loc := (@loc ml_type).

Section with_monad.
Context [M : Type -> Type].

(* Generated type definitions *)
data my_opt (a : Type) : Set where My_none : my_opt My_some : a → my_opt

data even_int : Set where
  Zorro : even_int
  DoubleZ : even_int → even_int
  D : ℤ → even_int

data quadruplet (a : Type) (b : Type) (c : Type) (d : Type) : Set where
  Quatuor : a → b → c → d → quadruplet

data my_list (a : Type) : Set where
  E : my_list
  Cons : a → my_list a → my_list

data ml_exns : Set where
  Invalid-argument : string → ml_exns
  Failure : string → ml_exns
  Not-found : ml_exns


data lazy_val (a : Type) = Set where
  LzVal : a → lazy_val
  LzThunk : (M a) → lazy_val
  LzExn : ml_exns → lazy_val

data lazy_t (a a1 : Type) = Set where
  Lval : a → lazy_t
  Lref : (loc (ml_lazy_val a1)) → lazy_t

Local (* Generated type translation function *)
coq_type (T : ml_type) → Type
coq_type = case T of λ {ml-int → ℤ
           ; ml-char → Char
           ; ml-float → Float
           ; ml-bool → Bool
           ; ml-unit → Unit
           ; ml-exn → ml-exns
           ; ml-array T1 → loc (ml-array-t T1)
           ; ml-list T1 → List (coq_type T1)
           ; ml-lazy T1 → lazy-t (coq_type T1) T1
           ; ml-string → String
           ; ml-empty → empty
           ; ml-array-t T1 → array-t (coq_type T1)
           ; ml_my_opt T1 → my_opt (coq_type T1)
           ; ml_even_int → even_int
           ; ml_quadruplet T1 T2 T3 T4 →
               quadruplet (coq_type T1) (coq_type T2) (coq_type T3)
                 (coq_type T4)
           ; ml_my_list T1 → my_list (coq_type T1)
           ; ml-lazy-val T1 → lazy-val (coq_type T1)
           ; ml-ref T1 → loc T1
           ; ml-arrow T1 T2 → coq_type T1 -> M (coq_type T2)
           }

End with_monad.
Local Definition ml_exn := ml_exn.
End MLtypes.
Export MLtypes.

Module REFmonadML := REFmonad (MLtypes).
Export REFmonadML.

Definition coq_type := @MLtypes.coq_type M.
Definition empty_env := mkEnv nil.
Definition it : W unit := inr (inr tt, empty_env).

(* Generated comparison function *)
compare_rec (h : nat) (T : ml_type)
  → coq_type T -> coq_type T -> M comparison
compare_rec = case h of λ {h.+1 →
                              let compare_rec = compare_rec h in
                              case T of λ {ml-int →
                                              λ { x y →
                                                Ret (compare-integer x y) }
                              ; ml-char →
                                  λ { x y → Ret (compare-ascii x y) }
                              ; ml-float →
                                  λ { x y → Ret (compare-float x y) }
                              ; ml-bool →
                                  λ { x y → Ret (compare-bool x y) }
                              ; ml-unit → λ { x y → Ret Eq }
                              ; ml-exn →
                                  λ { x y →
                                    case x, y of λ {Not-found, Not-found →
                                                       Ret Eq
                                    ; Invalid-argument x1,
                                      Invalid-argument y1 →
                                        compare_rec ml-string x1 y1
                                    ; Failure x1, Failure y1 →
                                        compare_rec ml-string x1 y1
                                    ; Not-found, _ → Ret Lt
                                    ; _, Not-found → Ret Gt
                                    ; Invalid-argument _, _ → Ret Lt
                                    ; _, Invalid-argument _ → Ret Gt
                                    } }
                              ; ml-array T1 →
                                  λ { x y →
                                    compare-ref compare-rec (ml-array-t T1) x
                                      y }
                              ; ml-list T1 →
                                  λ { x y →
                                    compare-list compare-rec T1 x y }
                              ; ml-lazy T1 →
                                  λ { x y →
                                    Raise
                                      (Catchable
                                         (Invalid_argument "compare"%string)) }
                              ; ml-string →
                                  λ { x y → Ret (compare-string x y) }
                              ; ml-empty → λ { x y → case x of λ { } }
                              ; ml-array-t T1 →
                                  λ { x y →
                                    case x, y of λ {ArrayVal x1, ArrayVal y1 →
                                                       compare_rec
                                                         (ml-list T1) x1 y1
                                    } }
                              ; ml_my_opt T1 →
                                  λ { x y →
                                    case x, y of λ {My_none, My_none →
                                                       Ret Eq
                                    ; My_some x1, My_some y1 →
                                        compare_rec T1 x1 y1
                                    ; My_none, _ → Ret Lt
                                    ; _, My_none → Ret Gt
                                    } }
                              ; ml_even_int →
                                  λ { x y →
                                    case x, y of λ {Zorro, Zorro → Ret Eq
                                    ; DoubleZ x1, DoubleZ y1 →
                                        compare_rec ml_even_int x1 y1
                                    ; D x1, D y1 → compare_rec ml-int x1 y1
                                    ; Zorro, _ → Ret Lt
                                    ; _, Zorro → Ret Gt
                                    ; DoubleZ _, _ → Ret Lt
                                    ; _, DoubleZ _ → Ret Gt
                                    } }
                              ; ml_quadruplet T1 T2 T3 T4 →
                                  λ { x y →
                                    case x, y of λ {Quatuor x1 x2 x3 x4,
                                                     Quatuor y1 y2 y3 y4 →
                                                       lexi_compare
                                                         (compare_rec T1 x1
                                                            y1)
                                                         (Delay
                                                            (lexi_compare
                                                               (compare_rec
                                                                  T2 x2 y2)
                                                               (Delay
                                                                  (lexi_compare
                                                                    (compare_rec
                                                                    T3 x3 y3)
                                                                    (Delay
                                                                    (compare_rec
                                                                    T4 x4 y4))))))
                                    } }
                              ; ml_my_list T1 →
                                  λ { x y →
                                    case x, y of λ {E, E → Ret Eq
                                    ; Cons x1 x2, Cons y1 y2 →
                                        lexi_compare (compare_rec T1 x1 y1)
                                          (Delay
                                             (compare_rec (ml_my_list T1) x2
                                                y2))
                                    ; E, _ → Ret Lt
                                    ; _, E → Ret Gt
                                    } }
                              ; ml-lazy-val T1 →
                                  λ { x y →
                                    Raise
                                      (Catchable
                                         (Invalid_argument "compare"%string)) }
                              ; ml-ref T1 →
                                  λ { x y →
                                    compare-ref compare-rec T1 x y }
                              ; ml-arrow T1 T2 →
                                  λ { x y →
                                    Raise
                                      (Catchable
                                         (Invalid_argument "compare"%string)) }
                              }
              ; _ → λ { _ _ → FailGas }
              }

Definition ml_compare := compare_rec.

Definition wrap_compare wrap T h x y : M bool :=
  do c <- compare_rec T h x y; Ret (wrap c).

Definition ml_eq := wrap_compare (fun c => if c is Eq then true else false).
Definition ml_lt := wrap_compare (fun c => if c is Lt then true else false).
Definition ml_gt := wrap_compare (fun c => if c is Gt then true else false).
Definition ml_ne := wrap_compare (fun c => if c is Eq then false else true).
Definition ml_ge := wrap_compare (fun c => if c is Lt then false else true).
Definition ml_le := wrap_compare (fun c => if c is Gt then false else true).

(* Array operations *)
Definition newarray T len (x : coq_type T) :=
  do len <- nat_of_int len; cnew (ml_array_t T) (ArrayVal _ (nseq len x)).
Definition getarray T (a : coq_type (ml_array T)) n : M (coq_type T) :=
  do s <- cget (ml_array_t T) a;
  let: ArrayVal s := s in
  do n <- bounded_nat_of_int (seq.size s) n;
  if s is x :: _ then Ret (nth x s n) else
  raise _ (Invalid_argument "getarray").
Definition setarray T (a : coq_type (ml_array T)) n (x : coq_type T) :=
  do s <- cget (ml_array_t T) a;
  let: ArrayVal s := s in
  do n <- bounded_nat_of_int (seq.size s) n;
  cput (ml_array_t T) a (ArrayVal _ (set_nth x s n x)).

(* Lazy values *)
Definition force a (lz : coq_type (ml_lazy a)) :=
  match lz with
  | Lval x => Ret x
  | Lref r =>
    do r' <- cget (ml_lazy_val a) r;
    match r' with
    | LzVal x => Ret x
    | LzExn e => raise _ e
    | LzThunk f => handle _
        (do x <- f; do _ <- cput (ml_lazy_val a) r (LzVal _ x); Ret x)
        (fun e => do _ <- cput _ r (LzExn _ e); raise _ e)
    end
  end.
Definition make_lazy a (b : M (coq_type a)) : M (coq_type (ml_lazy a)) :=
  do x <- cnew (ml_lazy_val a) (LzThunk _ b); Ret (Lref _ _ x).
Definition make_lazy_val a (b : coq_type a) : coq_type (ml_lazy a) :=
  Lval _ _ b.

(* Default amount of gas *)
Definition h := 100000.

(* Translated code *)

add (x y : coq_type ml-int) → coq_type ml-int
add = _+_ x y

mult_2 (x y : coq_type ml-int) → coq_type ml-int
mult_2 = _*_ (_*_ 2%int63 x) y

arrow (v : coq_type ml-unit) → coq_type ml-string
arrow = case v of λ {tt → "huhu"%string }

two_first (lis : coq_type (ml_my_list ml-int))
  → coq_type (ml_my_list ml-int)
two_first = case lis of λ {E →
                              Cons (coq_type ml-int) 0%int63
                                (Cons (coq_type ml-int) 0%int63
                                   (E (coq_type ml-int)))
            ; Cons x E →
                Cons (coq_type ml-int) x
                  (Cons (coq_type ml-int) 0%int63 (E (coq_type ml-int)))
            ; Cons x (Cons y _) →
                Cons (coq_type ml-int) x
                  (Cons (coq_type ml-int) y (E (coq_type ml-int)))
            }

f1 (T : ml_type) (x : coq_type T) → coq_type T
f1 = x

f2 (x y z u : coq_type ml-int) → coq_type ml-int
f2 = _+_ x (_*_ y ((λ { t v → _*_ (_*_ 2%int63 t) v }) z u))

ignore (T : ml_type) (_ : coq_type T) → coq_type ml-unit
ignore = tt

g (x : coq_type ml-int) → coq_type ml-int
g = let u = 2%int63 in _+_ x u

g2 (x : coq_type ml-int) → coq_type ml-int
g2 = let u = 5%int63 in _-_ x u

f3 (T T_1 : ml_type) (x : coq_type T_1) (y : coq_type T)
  → M (coq_type ml-unit)
f3 = do _ <- Ret (ignore T_1 x); do _ <- Ret (ignore T y); Ret tt

