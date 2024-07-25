open import agdagen_defs
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool using (true; false; Bool; if_then_else_)
open import Relation.Nullary.Decidable.Core using (_because_; isYes; Dec; yes)
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)
open import Data.String using (String)
open import Data.Float using (Float)
  renaming (_+_ to _ℝ+_; _*_ to _ℝ*_; _-_ to _ℝ-_; _÷_ to _ℝ÷_; -_ to ℝ-_)
open import Data.Char using (Char)
open import Data.Nat using (ℕ; suc) renaming (_<?_ to _ℕ<?_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; length; _∷_)
open import Data.Product using (_×_ ; _,_; proj₁ ; proj₂; _,′_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (map′; _×-dec_; no)
open import Relation.Binary.PropositionalEquality using (inspect; [_])
open import Data.Integer using (ℤ; _+_; _-_; _*_; +_; -_)
open import Data.Integer.DivMod using (_%_ ; _/_)
open import Function.Base using (case_of_)

-- Generated representation of all ML types

data ml-type : Set where
  ml-int : ml-type
  ml-char : ml-type
  ml-float : ml-type
  ml-bool : ml-type
  ml-unit : ml-type
  ml-exn : ml-type
  ml-list : (ml-type) → ml-type
  ml-lazy : (ml-type) → ml-type
  ml-string : ml-type
  ml-empty : ml-type
  ml-array-t : (ml-type) → ml-type
  ml-my-opt : (ml-type) → ml-type
  ml-even-int : ml-type
  ml-quadruplet : (ml-type) → (ml-type) → (ml-type) → (ml-type) →
    ml-type
  ml-my-list : (ml-type) → ml-type
  ml-point : (ml-type) → (ml-type) → ml-type
  ml-lazy-val : (ml-type) → ml-type
  ml-ref : (ml-type) → ml-type
  ml-arrow : (ml-type) → (ml-type) → ml-type

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
  ~ml-list : (u1 v1 : ml-type) → ml-list u1 ~ ml-list v1
  ~ml-lazy : (u1 v1 : ml-type) → ml-lazy u1 ~ ml-lazy v1
  ~ml-string : ml-string ~ ml-string
  ~ml-empty : ml-empty ~ ml-empty
  ~ml-array-t : (u1 v1 : ml-type) → ml-array-t u1 ~ ml-array-t v1
  ~ml-my-opt : (u1 v1 : ml-type) → ml-my-opt u1 ~ ml-my-opt v1
  ~ml-even-int : ml-even-int ~ ml-even-int
  ~ml-quadruplet : (u1 u2 u3 u4 v1 v2 v3 v4 : ml-type) → ml-quadruplet u1 u2 u3 u4 ~ ml-quadruplet v1 v2 v3 v4
  ~ml-my-list : (u1 v1 : ml-type) → ml-my-list u1 ~ ml-my-list v1
  ~ml-point : (u1 u2 v1 v2 : ml-type) → ml-point u1 u2 ~ ml-point v1 v2
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
view (ml-list u1) (ml-list v1) = just (~ml-list u1 v1)
view (ml-lazy u1) (ml-lazy v1) = just (~ml-lazy u1 v1)
view ml-string ml-string = just ~ml-string
view ml-empty ml-empty = just ~ml-empty
view (ml-array-t u1) (ml-array-t v1) = just (~ml-array-t u1 v1)
view (ml-my-opt u1) (ml-my-opt v1) = just (~ml-my-opt u1 v1)
view ml-even-int ml-even-int = just ~ml-even-int
view (ml-quadruplet u1 u2 u3 u4) (ml-quadruplet v1 v2 v3 v4) = just (~ml-quadruplet u1 u2 u3 u4 v1 v2 v3 v4)
view (ml-my-list u1) (ml-my-list v1) = just (~ml-my-list u1 v1)
view (ml-point u1 u2) (ml-point v1 v2) = just (~ml-point u1 u2 v1 v2)
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
view-diag (ml-list _) ()
view-diag (ml-lazy _) ()
view-diag ml-string()
view-diag ml-empty()
view-diag (ml-array-t _) ()
view-diag (ml-my-opt _) ()
view-diag ml-even-int()
view-diag (ml-quadruplet _ _ _ _) ()
view-diag (ml-my-list _) ()
view-diag (ml-point _ _) ()
view-diag (ml-lazy-val _) ()
view-diag (ml-ref _) ()
view-diag (ml-arrow _ _) ()

ml-list-inj : ml-list u1 ≡ ml-list v1 → (u1 ≡ v1)
ml-list-inj refl = refl

ml-lazy-inj : ml-lazy u1 ≡ ml-lazy v1 → (u1 ≡ v1)
ml-lazy-inj refl = refl

ml-array-t-inj : ml-array-t u1 ≡ ml-array-t v1 → (u1 ≡ v1)
ml-array-t-inj refl = refl

ml-my-opt-inj : ml-my-opt u1 ≡ ml-my-opt v1 → (u1 ≡ v1)
ml-my-opt-inj refl = refl

ml-quadruplet-inj : ml-quadruplet u1 u2 u3 u4 ≡ ml-quadruplet v1 v2 v3 v4 → up4 (u1 ≡ v1) (u2 ≡ v2) (u3 ≡ v3) (u4 ≡ v4)
ml-quadruplet-inj refl = refl ,,, refl ,,, refl ,,, refl

ml-my-list-inj : ml-my-list u1 ≡ ml-my-list v1 → (u1 ≡ v1)
ml-my-list-inj refl = refl

ml-point-inj : ml-point u1 u2 ≡ ml-point v1 v2 → _×_ (u1 ≡ v1) (u2 ≡ v2)
ml-point-inj refl = refl , refl

ml-lazy-val-inj : ml-lazy-val u1 ≡ ml-lazy-val v1 → (u1 ≡ v1)
ml-lazy-val-inj refl = refl

ml-ref-inj : ml-ref u1 ≡ ml-ref v1 → (u1 ≡ v1)
ml-ref-inj refl = refl

ml-arrow-inj : ml-arrow u1 u2 ≡ ml-arrow v1 v2 → _×_ (u1 ≡ v1) (u2 ≡ v2)
ml-arrow-inj refl = refl , refl

ml-list-cong : (u1 ≡ v1) → ml-list u1 ≡ ml-list v1
ml-list-cong (refl) = refl

ml-lazy-cong : (u1 ≡ v1) → ml-lazy u1 ≡ ml-lazy v1
ml-lazy-cong (refl) = refl

ml-array-t-cong : (u1 ≡ v1) → ml-array-t u1 ≡ ml-array-t v1
ml-array-t-cong (refl) = refl

ml-my-opt-cong : (u1 ≡ v1) → ml-my-opt u1 ≡ ml-my-opt v1
ml-my-opt-cong (refl) = refl

ml-quadruplet-cong : up4 (u1 ≡ v1) (u2 ≡ v2) (u3 ≡ v3) (u4 ≡ v4) → ml-quadruplet u1 u2 u3 u4 ≡ ml-quadruplet v1 v2 v3 v4
ml-quadruplet-cong (refl ,,, refl ,,, refl ,,, refl) = refl

ml-my-list-cong : (u1 ≡ v1) → ml-my-list u1 ≡ ml-my-list v1
ml-my-list-cong (refl) = refl

ml-point-cong : _×_ (u1 ≡ v1) (u2 ≡ v2) → ml-point u1 u2 ≡ ml-point v1 v2
ml-point-cong (refl , refl) = refl

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
eq-decc _ _ | just (~ml-list u1 v1) | _ = map′ ml-list-cong ml-list-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-lazy u1 v1) | _ = map′ ml-lazy-cong ml-lazy-inj ((eq-decc u1 v1))
eq-decc _ _ | just ~ml-string | _ = yes refl
eq-decc _ _ | just ~ml-empty | _ = yes refl
eq-decc _ _ | just (~ml-array-t u1 v1) | _ = map′ ml-array-t-cong ml-array-t-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-my-opt u1 v1) | _ = map′ ml-my-opt-cong ml-my-opt-inj ((eq-decc u1 v1))
eq-decc _ _ | just ~ml-even-int | _ = yes refl
eq-decc _ _ | just (~ml-quadruplet u1 u2 u3 u4 v1 v2 v3 v4) | _ = map′ ml-quadruplet-cong ml-quadruplet-inj (up4-dec (eq-decc u1 v1) (eq-decc u2 v2) (eq-decc u3 v3) (eq-decc u4 v4))
eq-decc _ _ | just (~ml-my-list u1 v1) | _ = map′ ml-my-list-cong ml-my-list-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-point u1 u2 v1 v2) | _ = map′ ml-point-cong ml-point-inj (_×-dec_ (eq-decc u1 v1) (eq-decc u2 v2))
eq-decc _ _ | just (~ml-lazy-val u1 v1) | _ = map′ ml-lazy-val-cong ml-lazy-val-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-ref u1 v1) | _ = map′ ml-ref-cong ml-ref-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-arrow u1 u2 v1 v2) | _ = map′ ml-arrow-cong ml-arrow-inj (_×-dec_ (eq-decc u1 v1) (eq-decc u2 v2))
eq-decc m n | nothing | [ eq ] = no λ where refl → view-diag _ eq

-- End of the proof of DecidableEquality on ml-type

ml-type-eq-dec : DecidableEquality ml-type
ml-type-eq-dec = eq-decc

instance
  ml-type-is-eq-dec : eqType ml-type
  ml-type-is-eq-dec = record {eq-dec = ml-type-eq-dec}

data array-t (T : Set) : Set where
  ArrayVal : List T → array-t T

ml-array : ml-type → ml-type
ml-array T = ml-ref (ml-array-t T)
module MLtypes-aux (M : Set → Set) where
  -- Generated type definitions
  loc = loc-b ml-type
  
  data ml-exns : Set where
    Invalid-argument : (String) → ml-exns
    Failure : (String) → ml-exns
    Not-found : ml-exns
  
  data point (a : Set) (b : Set) : Set where
    Point : (a) → (b) → point a b
  
  data my-list (a : Set) : Set where
    E-1 : my-list a
    Cons : (a) → (my-list a) → my-list a
  
  data quadruplet (a : Set) (b : Set) (c : Set) (d : Set) : Set where
    Quatuor : (a) → (b) → (c) → (d) → quadruplet a b c d
  
  data even-int : Set where
    Zorro : even-int
    DoubleZ : (even-int) → even-int
    Ddd : (ℤ) → even-int
  
  data my-opt (a : Set) : Set where
    My-none : my-opt a
    My-some : (a) → my-opt a
  
  data lazy-val (a : Set) : Set where
    LzVal : a → lazy-val a
    LzThunk : (M a) → lazy-val a
    LzExn : ml-exns → lazy-val a
  
  data lazy-t (a : Set) (a1 : ml-type) : Set where
    Lval : a → lazy-t a a1
    Lref : (loc (ml-lazy-val a1)) → lazy-t a a1
  -- Generated type translation function
  
  coq-type : (T : ml-type) → Set
  coq-type T =
      case T of λ {
        (ml-int) → ℤ
        ; (ml-char) → Char
        ; (ml-float) → Float
        ; (ml-bool) → Bool
        ; (ml-unit) → ⊤
        ; (ml-exn) → ml-exns
        ; (ml-list T1) → List (coq-type T1)
        ; (ml-lazy T1) → lazy-t (coq-type T1) T1
        ; (ml-string) → String
        ; (ml-empty) → ⊥
        ; (ml-array-t T1) → array-t (coq-type T1)
        ; (ml-my-opt T1) → my-opt (coq-type T1)
        ; (ml-even-int) → even-int
        ; (ml-quadruplet T1 T2 T3 T4) →
            quadruplet (coq-type T1) (coq-type T2) (coq-type T3)
              (coq-type T4)
        ; (ml-my-list T1) → my-list (coq-type T1)
        ; (ml-point T1 T2) → point (coq-type T1) (coq-type T2)
        ; (ml-lazy-val T1) → lazy-val (coq-type T1)
        ; (ml-ref T1) → loc T1
        ; (ml-arrow T1 T2) → coq-type T1 → M (coq-type T2)
        }
  
  
open MLtypes-aux hiding (loc; coq-type)

MLtypes : MLTY
MLtypes = record {
  ml-type = ml-type ;
  coq-type-b = MLtypes-aux.coq-type ;
  ml-exn = ml-exn ;
  ml-type-is-eq-dec = ml-type-is-eq-dec
  }

open MLTY MLtypes hiding (ml-type; ml-exn)

REFmonadML : REFmonad MLtypes
REFmonadML = record {}

open REFmonad REFmonadML

empty-env : Env2
empty-env = mkEnv []

it : W ⊤
it = inj₂ (inj₂ tt , empty-env)

-- Generated comparison function


compare-rec : (h : ℕ) {T : ml-type}
  → coq-type T -> coq-type T -> M comparator
compare-rec ℕ.zero {T} x y = FailGas
compare-rec (suc h) {ml-int} = λ x y →  Ret (compare-integer x y)
compare-rec (suc h) {ml-char} = λ x y → Ret (compare-ascii x y)
compare-rec (suc h) {ml-float} = λ x y → Ret (compare-float x y)
compare-rec (suc h) {ml-bool} = λ x y → Ret (compare-bool x y)
compare-rec (suc h) {ml-unit} = λ x y → Ret Eq
compare-rec (suc h) {ml-list T} =
  λ x y → compare-list {T} {compare-rec h} x y
compare-rec (suc h) {ml-lazy T} =
  λ x y → Raise (Catchable (Invalid-argument "compare"))
compare-rec (suc h) {ml-string} = λ x y → Ret (compare-string x y)
compare-rec (suc h) {ml-array-t T} (ArrayVal x) (ArrayVal y) =
  compare-rec h x y
compare-rec (suc h) {ml-lazy-val T} =
  λ x y → Raise (Catchable (Invalid-argument "compare"))
compare-rec (suc h) {ml-ref T} =
  λ x y → compare-ref {T} {compare-rec h} x y
compare-rec (suc h) {ml-arrow T T1} =
  λ x y → Raise (Catchable (Invalid-argument "compare"))

compare-rec (suc h) {ml-exn} =
  λ x y → case x , y of λ {
    (Invalid-argument x1 , Invalid-argument y1) → compare-rec h x1 y1
    ; (Invalid-argument _ , _) → Ret Lt
    ; (_ , Invalid-argument _) → Ret Gt
    ; (Failure x1 , Failure y1) → compare-rec h x1 y1
    ; (Failure _ , _) → Ret Lt
    ; (_ , Failure _) → Ret Gt
    ; (Not-found , Not-found) → Ret Eq
    }
compare-rec (suc h) {ml-my-opt a1} =
  λ x y → case x , y of λ {
    (My-none , My-none) → Ret Eq
    ; (My-none , _) → Ret Lt
    ; (_ , My-none) → Ret Gt
    ; (My-some x1 , My-some y1) → compare-rec h x1 y1
    }
compare-rec (suc h) {ml-even-int} =
  λ x y → case x , y of λ {
    (Zorro , Zorro) → Ret Eq
    ; (Zorro , _) → Ret Lt
    ; (_ , Zorro) → Ret Gt
    ; (DoubleZ x1 , DoubleZ y1) → compare-rec h x1 y1
    ; (DoubleZ _ , _) → Ret Lt
    ; (_ , DoubleZ _) → Ret Gt
    ; (Ddd x1 , Ddd y1) → compare-rec h x1 y1
    }
compare-rec (suc h) {ml-quadruplet a1 a2 a3 a4} =
  λ x y → case x , y of λ {
    (Quatuor x1 x2 x3 x4 , Quatuor y1 y2 y3 y4) → 
      lexi-compare (compare-rec h x1 y1)
       (Delay (
         lexi-compare (compare-rec h x2 y2)
          (Delay (
            lexi-compare (compare-rec h x3 y3)
             (Delay (compare-rec h x4 y4))))))
    }
compare-rec (suc h) {ml-my-list a1} =
  λ x y → case x , y of λ {
    (E-1 , E-1) → Ret Eq
    ; (E-1 , _) → Ret Lt
    ; (_ , E-1) → Ret Gt
    ; (Cons x1 x2 , Cons y1 y2) → 
        lexi-compare (compare-rec h x1 y1)
         (Delay (compare-rec h x2 y2))
    }
compare-rec (suc h) {ml-point a1 a2} =
  λ x y → case x , y of λ {
    (Point x1 x2 , Point y1 y2) → 
      lexi-compare (compare-rec h x1 y1)
       (Delay (compare-rec h x2 y2))
    }


ml-compare = compare-rec

wrap-compare : (comparator → Bool) → (h : ℕ) → (T : ml-type) → coq-type T → coq-type T → M Bool
wrap-compare wrap h T x y = Do c ← compare-rec h {T} x y // Ret (wrap c)

ml-eq = wrap-compare (λ {Eq → true ; _ → false })
ml-lt = wrap-compare (λ {Lt → true ; _ → false })
ml-gt = wrap-compare (λ {Gt → true ; _ → false })
ml-ne = wrap-compare (λ {Eq → false ; _ → true })
ml-ge = wrap-compare (λ {Lt → false ; _ → true })
ml-le = wrap-compare (λ {Gt → false ; _ → true })

-- Array operations
nat-of-int : ℤ → M ℕ
nat-of-int (+_ n) = Ret n
nat-of-int (ℤ.negsuc n) = Raise BoundedNat

newarray : (T : ml-type) → ℤ → (x : coq-type T) → M (loc (ml-array-t T))
newarray T len x = Do len ← nat-of-int len // cnew (ml-array-t T) (ArrayVal (ncons len x))

bounded-nat-of-int : ℕ → ℤ → M ℕ
bounded-nat-of-int m n = Do n ← nat-of-int n // case (n ℕ<? m) of λ {
                (yes _) → Ret n ;
                _ → Raise BoundedNat }

getarray : (T : ml-type) → (a : coq-type (ml-array T)) → (n : ℤ) → M (coq-type T)
getarray T a n = Do s ← cget (ml-array-t T) a // case s of λ {
                      (ArrayVal u) → Do n ← bounded-nat-of-int (length u) n //
                        case u of λ {
                          [] → raise T (Invalid-argument "getarray") ;
                          (x ∷ q) → Ret (nth x u n) } }

setarray : (T : ml-type) → (a : coq-type (ml-array T)) → (n : ℤ) → (coq-type T) → M ⊤
setarray T a n x = Do s ← cget (ml-array-t T) a //
                      case s of λ {
                        (ArrayVal u) → Do n ← bounded-nat-of-int (length u) n //
                          cput (ml-array-t T) a (ArrayVal (set-nth x u n x)) }

-- Lazy values
force : (a : ml-type) → (lz : coq-type (ml-lazy a)) → M (coq-type a)
force a (Lval x) = Ret x
force a (Lref r) = Do r' ← cget (ml-lazy-val a) r //
                           (case r' of λ {
                               (LzVal x) → Ret x ;
                               (LzExn e) → raise _ e ;
                               (LzThunk f) → let ff : M (coq-type a)
                                                 ff = f in
                                                    handle _ (Do x ← ff //
                                                       Do _ ← cput (ml-lazy-val a) r (LzVal x) //
                                                       Ret x)
                                                       (λ e → Do _ ← cput _ r (LzExn e) //
                                                              raise _ e) })

make-lazy : (a : ml-type) (b : M (coq-type a)) → M (coq-type (ml-lazy a))
make-lazy a b = Do x ← cnew (ml-lazy-val a) (LzThunk b) // Ret (Lref x)

make-lazy-val : (a : ml-type) (b : coq-type a) → coq-type (ml-lazy a)
make-lazy-val a b = Lval b

-- Default amount of gas

h = 100000

-- Translated code

add : (x y : coq-type ml-int) → coq-type ml-int
add x y = _+_ x y

mult-2 : (x y : coq-type ml-int) → coq-type ml-int
mult-2 x y = _*_ (_*_ (+ 2) x) y

arrow : (v : coq-type ml-unit) → coq-type ml-string
arrow v = case v of λ {
            (tt) → "huhu"
            }

two-first : (lis : coq-type (ml-my-list ml-int))
  → coq-type (ml-my-list ml-int)
two-first lis =
    case lis of λ {
      (E-1) → Cons (+ 0) (Cons (+ 0) E-1)
      ; (Cons x E-1) → Cons x (Cons (+ 0) E-1)
      ; (Cons x (Cons y _)) → Cons x (Cons y E-1)
      }

f1 : (T-1 : ml-type) (x : coq-type T-1) → coq-type T-1
f1 T-1 x = x

f2 : (x y z u : coq-type ml-int) → coq-type ml-int
f2 x y z u = _+_ x (_*_ y ((λ t v → _*_ (_*_ (+ 2) t) v) z u))

ignore : (T-1 : ml-type) (_ : coq-type T-1) → coq-type ml-unit
ignore T-1 _ = tt

g : (x : coq-type ml-int) → coq-type ml-int
g x = let u = (+ 2) in _+_ x u

add5 : (x : coq-type ml-int) → coq-type ml-int
add5 x =
    let aux : (y : coq-type ml-int) → coq-type ml-int
        aux y = _+_ y (+ 5) in aux x

add7ifnon3 : (x : coq-type ml-int) → coq-type ml-int
add7ifnon3 x =
    let helper : (y : coq-type ml-int) → coq-type ml-int
        helper y = case y of λ {
                     ((+ 4)) → (+ 3)
                     ; (n) → _+_ n (+ 7)
                     }
          in helper (_+_ x (+ 1))

f3 : (x : coq-type ml-int) → coq-type ml-int
f3 x =
    let h-1 : (y : coq-type ml-int) → coq-type ml-int
        h-1 y = case y of λ {
                  ((+ 0)) → (+ 0)
                  ; (n) → _+_ n (+ 1)
                  }
          in h-1 x

div : (x y : coq-type ml-float) → coq-type ml-float
div x y = _ℝ÷_ x y

harmonic : (x y : coq-type ml-float) → coq-type ml-float
harmonic x y = _ℝ÷_ (2.0) (_ℝ+_ (_ℝ÷_ (1.0) x) (_ℝ÷_ (1.0) y))

float-sum : (h : ℕ) (l : coq-type (ml-list ml-float))
  → M (coq-type ml-float)
float-sum h l =
    case h of λ {
      (suc h) →
        case l of λ {
          ([]) → Ret (0.0)
          ; (_∷_ first rest) →
              Do v ← float-sum h rest // Ret (_ℝ+_ first v)
          }
      ; (_) → FailGas
      }

newton's-method : (e : coq-type ml-float)
  (f : coq-type (ml-arrow ml-float ml-float)) → M (coq-type ml-float)
newton's-method e f =
    let diff : (e-1 : coq-type ml-float)
              (f-1 : coq-type (ml-arrow ml-float ml-float))
              (x : coq-type ml-float) → M (coq-type ml-float)
        diff e-1 f-1 x =
          Do v ←
          (Do v ← f-1 x //
           Do v-1 ← f-1 (_ℝ+_ x e-1) // Ret (_ℝ-_ v-1 v)) //
          Ret (_ℝ÷_ v e-1) in
            Do r ← (cnew ml-float (1.0)) //
            Do _ ←
            (Do u ← Ret (+ 1) //
             Do v ← Ret (+ 10) //
             forloop u v
               (λ i →
                  Do v ←
                  (Do v ←
                   (Do v ← (Do v ← cget ml-float r // diff e f v) //
                    Do v-1 ← (Do v ← cget ml-float r // f v) //
                    Ret (_ℝ÷_ v-1 v)) //
                   Do v-1 ← cget ml-float r // Ret (_ℝ-_ v-1 v)) //
                  cput ml-float r v)) //
            cget ml-float r

fact : (h : ℕ) (n : coq-type ml-int) → M (coq-type ml-int)
fact h n =
    Do i ← (cnew ml-int n) //
    Do v ← (cnew ml-int (+ 1)) //
    Do _ ←
    whileloop h (Do v-1 ← cget ml-int i // ml-gt h ml-int v-1 (+ 0))
      (Do _ ←
       (Do v-1 ←
        (Do v-1 ← cget ml-int i //
         Do v-2 ← cget ml-int v // Ret (_*_ v-2 v-1)) //
        cput ml-int v v-1) //
       Do v-1 ← (Do v-1 ← cget ml-int i // Ret (_-_ v-1 (+ 1))) //
       cput ml-int i v-1) //
    cget ml-int v

ref' : (T-1 : ml-type) → coq-type T-1 → M (coq-type (ml-ref T-1))
ref' T-1 = cnew T-1

foo1 : (T-1 : ml-type) (x : coq-type T-1) → M (coq-type T-1)
foo1 T-1 x =
    let id : (T-2 : ml-type) (y : coq-type T-2) → coq-type T-2
        id T-2 y = y in id (ml-arrow T-1 T-1) (λ x-1 → Ret (id T-1 x-1)) x

id : (T-1 : ml-type) (h-1 : coq-type T-1) → coq-type T-1
id T-1 h-1 = h-1

foo2 : (x z : coq-type ml-int) → coq-type ml-int
foo2 x z = _+_ x z

foo3 : coq-type ml-int → M (coq-type (ml-arrow ml-int ml-int))
foo3 =
    id (ml-arrow ml-int (ml-arrow ml-int ml-int))
      (λ x → Ret (λ x-1 → Ret (foo2 x x-1)))

foo2-1 : (T-1 T-2 : ml-type) (x : coq-type T-2)
  → coq-type T-1 → M (coq-type T-2)
foo2-1 T-1 T-2 x = id (ml-arrow T-1 T-2) (λ y → Ret x)

incr : (r : coq-type (ml-ref ml-int)) → M (coq-type ml-unit)
incr r = Do x ← (cget ml-int r) // cput ml-int r (_+_ x (+ 1))

oo = Restart it (Do r ← (cnew ml-int (+ 1)) // incr r)

f : (x y z : coq-type ml-int) → coq-type ml-int
f x y z = _+_ (_+_ x y) z

r = Restart oo (cnew ml-int (+ 5))

g-1 : (x : coq-type ml-int) → M (coq-type ml-int)
g-1 x = Do r ← FromW r // Do v ← cget ml-int r // Ret (_+_ x v)

it-1 = Restart r (Do r ← FromW r // cput ml-int r (+ 1))

f-1 : (y : coq-type ml-int) → M (coq-type ml-int)
f-1 y = Do r ← FromW r // Do v ← cget ml-int r // Ret (_-_ y v)

c = Restart it-1 (g-1 (+ 7))

-Eval1 : coq-type ml-int
-Eval1 = (+ 4)

concat : (h : ℕ) (T-1 : ml-type) (l1 l2 : coq-type (ml-list T-1))
  → M (coq-type (ml-list T-1))
concat h T-1 l1 l2 =
    case h of λ {
      (suc h) →
        case l1 of λ {
          ([]) → Ret l2
          ; (_∷_ x q) → concat h T-1 q (_∷_ x l2)
          }
      ; (_) → FailGas
      }

u = Restart c (cnew (ml-list ml-int) [])

app : (h : ℕ) (l : coq-type (ml-list ml-int))
  → M (coq-type (ml-list ml-int))
app h l =
    Do u ← FromW u //
    Do v ← cget (ml-list ml-int) u // concat h ml-int l v

it-2 =
    Restart u
      (Do u ← FromW u //
       Do v ← (Do v ← cget (ml-list ml-int) u // Ret (_∷_ (+ 1) v)) //
       cput (ml-list ml-int) u v)

it-3 = Restart it-2 (app h (_∷_ (+ 7) []))

concat-1 : (h : ℕ) (T-1 : ml-type) (l1 l2 : coq-type (ml-list T-1))
  → M (coq-type (ml-list T-1))
concat-1 h T-1 l1 l2 =
    case h of λ {
      (suc h) →
        case l1 of λ {
          ([]) → Ret l2
          ; (_∷_ x q) → concat-1 h T-1 q (_∷_ x l2)
          }
      ; (_) → FailGas
      }

hy : (h : ℕ) (T-1 : ml-type)
  → coq-type (ml-list T-1) →
      coq-type (ml-list T-1) → M (coq-type (ml-list T-1))
hy h T-1 = concat-1 h T-1

ref2 : (T-1 : ml-type) → coq-type T-1 → M (coq-type (ml-ref T-1))
ref2 T-1 = cnew T-1

raise2 : (T-1 : ml-type) → coq-type ml-exn → M (coq-type T-1)
raise2 T-1 = raise T-1

emp : (T-1 T-2 : ml-type) (_ : coq-type T-2) → coq-type (ml-list T-1)
emp T-1 T-2 _ = []

scor7 : (T-1 : ml-type) (x : coq-type T-1) → coq-type (ml-point T-1 ml-int)
scor7 T-1 x = Point x (+ 7)

scorbis : (T-1 : ml-type) → coq-type T-1 → coq-type (ml-point T-1 ml-int)
scorbis T-1 = scor7 T-1

hoo : coq-type ml-int
hoo = (+ 7)

hoo2 : (T-1 : ml-type) (_ : coq-type T-1) → coq-type ml-int
hoo2 T-1 _ = (+ 7)

g-2 = Restart it-3 (Do y ← (cnew ml-int (+ 5)) // cget ml-int y)

carre : (x : coq-type ml-int) → coq-type ml-int
carre x = _*_ x x

yy : coq-type ml-int
yy = carre (+ 2)

rr : coq-type ml-int
rr = if true then (+ 4) else ( (+ 5))

a : (T-1 : ml-type) (x : coq-type T-1) → coq-type T-1
a T-1 x = x

u-1 = Restart g-2 (cnew ml-int (+ 3))

it-4 =
    Restart u-1
      (Do u-1 ← FromW u-1 //
       Do v ← (Do v ← cget ml-int u-1 // Ret (_+_ v (+ 1))) //
       cput ml-int u-1 v)

wz =
    Restart it-4
      (Do u-1 ← FromW u-1 //
       Do v ← (Do v ← cget ml-int u-1 // Ret (_+_ v (+ 1))) //
       cput ml-int u-1 v)

u-2 = Restart wz (cnew ml-int (+ 3))

icr =
    Restart u-2
      (Do u-2 ← FromW u-2 //
       Do v ← (Do v ← cget ml-int u-2 // Ret (_+_ v (+ 1))) //
       cput ml-int u-2 v)

f1-1 : (T-1 : ml-type) (x : coq-type T-1) → coq-type ml-unit
f1-1 T-1 x = tt

f2-1 : (v : coq-type ml-unit) → M (coq-type ml-unit)
f2-1 v = Do icr ← FromW icr // (Ret (case v of λ {
                                         (tt) → icr
                                         }))

f3-1 : (T-1 : ml-type) (x : coq-type T-1) → M (coq-type ml-unit)
f3-1 T-1 x = Do wz ← FromW wz // (Ret wz)

f6 : (v : coq-type ml-unit) → coq-type ml-unit → coq-type ml-unit
f6 v = case v of λ {
         (tt) → λ v → case v of λ {
                             (tt) → tt
                             }
         }

mm = Restart icr (cnew ml-int (+ 1))

wii =
    Restart mm
      (Do mm ← FromW mm //
       Do _ ←
       (Do v ← (Do v ← cget ml-int mm // Ret (_*_ (+ 2) v)) //
        cput ml-int mm v) //
       Ret (+ 4))

f-2 : (x : coq-type ml-int) → coq-type ml-string
f-2 x =
    case x of λ {
      ((+ 1)) → "soleil"
      ; ((+ 2)) → "soleil"
      ; ((+ 3)) → "soleil"
      ; (_) → "lune"
      }

x : coq-type ml-int
x = _+_ (-(+ 7)) (+ 5)


