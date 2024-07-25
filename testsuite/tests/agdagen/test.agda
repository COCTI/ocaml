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
open import Data.Integer.DivMod using (_/_)
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
  ml-color : ml-type
  ml-tree : (ml-type) → (ml-type) → ml-type
  ml-point : ml-type
  ml-ref-vals : (ml-type) → ml-type
  ml-endo : (ml-type) → ml-type
  ml-option : (ml-type) → ml-type
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
  ~ml-color : ml-color ~ ml-color
  ~ml-tree : (u1 u2 v1 v2 : ml-type) → ml-tree u1 u2 ~ ml-tree v1 v2
  ~ml-point : ml-point ~ ml-point
  ~ml-ref-vals : (u1 v1 : ml-type) → ml-ref-vals u1 ~ ml-ref-vals v1
  ~ml-endo : (u1 v1 : ml-type) → ml-endo u1 ~ ml-endo v1
  ~ml-option : (u1 v1 : ml-type) → ml-option u1 ~ ml-option v1
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
view ml-color ml-color = just ~ml-color
view (ml-tree u1 u2) (ml-tree v1 v2) = just (~ml-tree u1 u2 v1 v2)
view ml-point ml-point = just ~ml-point
view (ml-ref-vals u1) (ml-ref-vals v1) = just (~ml-ref-vals u1 v1)
view (ml-endo u1) (ml-endo v1) = just (~ml-endo u1 v1)
view (ml-option u1) (ml-option v1) = just (~ml-option u1 v1)
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
view-diag ml-color()
view-diag (ml-tree _ _) ()
view-diag ml-point()
view-diag (ml-ref-vals _) ()
view-diag (ml-endo _) ()
view-diag (ml-option _) ()
view-diag (ml-lazy-val _) ()
view-diag (ml-ref _) ()
view-diag (ml-arrow _ _) ()

ml-list-inj : ml-list u1 ≡ ml-list v1 → (u1 ≡ v1)
ml-list-inj refl = refl

ml-lazy-inj : ml-lazy u1 ≡ ml-lazy v1 → (u1 ≡ v1)
ml-lazy-inj refl = refl

ml-array-t-inj : ml-array-t u1 ≡ ml-array-t v1 → (u1 ≡ v1)
ml-array-t-inj refl = refl

ml-tree-inj : ml-tree u1 u2 ≡ ml-tree v1 v2 → _×_ (u1 ≡ v1) (u2 ≡ v2)
ml-tree-inj refl = refl , refl

ml-ref-vals-inj : ml-ref-vals u1 ≡ ml-ref-vals v1 → (u1 ≡ v1)
ml-ref-vals-inj refl = refl

ml-endo-inj : ml-endo u1 ≡ ml-endo v1 → (u1 ≡ v1)
ml-endo-inj refl = refl

ml-option-inj : ml-option u1 ≡ ml-option v1 → (u1 ≡ v1)
ml-option-inj refl = refl

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

ml-tree-cong : _×_ (u1 ≡ v1) (u2 ≡ v2) → ml-tree u1 u2 ≡ ml-tree v1 v2
ml-tree-cong (refl , refl) = refl

ml-ref-vals-cong : (u1 ≡ v1) → ml-ref-vals u1 ≡ ml-ref-vals v1
ml-ref-vals-cong (refl) = refl

ml-endo-cong : (u1 ≡ v1) → ml-endo u1 ≡ ml-endo v1
ml-endo-cong (refl) = refl

ml-option-cong : (u1 ≡ v1) → ml-option u1 ≡ ml-option v1
ml-option-cong (refl) = refl

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
eq-decc _ _ | just ~ml-color | _ = yes refl
eq-decc _ _ | just (~ml-tree u1 u2 v1 v2) | _ = map′ ml-tree-cong ml-tree-inj (_×-dec_ (eq-decc u1 v1) (eq-decc u2 v2))
eq-decc _ _ | just ~ml-point | _ = yes refl
eq-decc _ _ | just (~ml-ref-vals u1 v1) | _ = map′ ml-ref-vals-cong ml-ref-vals-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-endo u1 v1) | _ = map′ ml-endo-cong ml-endo-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-option u1 v1) | _ = map′ ml-option-cong ml-option-inj ((eq-decc u1 v1))
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
    Restart-1 : (⊤ → M ℤ) → ml-exns
    Invalid-argument : (String) → ml-exns
    Failure : (String) → ml-exns
    Not-found : ml-exns
  
  data option (a : Set) : Set where
    Some : (a) → option a
    None : option a
  
  data endo (a : Set) : Set where
    Endo : (a → M a) → endo a
  
  data ref-vals (a : Set) (a-1 : ml-type) : Set where
    RefVal : (loc a-1) → (List a) → ref-vals a a-1
  
  data point : Set where
    Point : (loc ml-int) → (loc ml-int) → point
  
  data tree (a : Set) (b : Set) : Set where
    Leaf : (a) → tree a b
    Node : (tree a b) → (b) → (tree a b) → tree a b
  
  data color : Set where
    Red : color
    Green : color
    Blue : color
  
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
        ; (ml-color) → color
        ; (ml-tree T1 T2) → tree (coq-type T1) (coq-type T2)
        ; (ml-point) → point
        ; (ml-ref-vals T1) → ref-vals (coq-type T1) T1
        ; (ml-endo T1) → endo (coq-type T1)
        ; (ml-option T1) → option (coq-type T1)
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
    (Restart-1 x1 , Restart-1 y1) → compare-rec h x1 y1
    ; (Restart-1 _ , _) → Ret Lt
    ; (_ , Restart-1 _) → Ret Gt
    ; (Invalid-argument x1 , Invalid-argument y1) → compare-rec h x1 y1
    ; (Invalid-argument _ , _) → Ret Lt
    ; (_ , Invalid-argument _) → Ret Gt
    ; (Failure x1 , Failure y1) → compare-rec h x1 y1
    ; (Failure _ , _) → Ret Lt
    ; (_ , Failure _) → Ret Gt
    ; (Not-found , Not-found) → Ret Eq
    }
compare-rec (suc h) {ml-color} =
  λ x y → case x , y of λ {
    (Red , Red) → Ret Eq
    ; (Red , _) → Ret Lt
    ; (_ , Red) → Ret Gt
    ; (Green , Green) → Ret Eq
    ; (Green , _) → Ret Lt
    ; (_ , Green) → Ret Gt
    ; (Blue , Blue) → Ret Eq
    }
compare-rec (suc h) {ml-tree a1 a2} =
  λ x y → case x , y of λ {
    (Leaf x1 , Leaf y1) → compare-rec h x1 y1
    ; (Leaf _ , _) → Ret Lt
    ; (_ , Leaf _) → Ret Gt
    ; (Node x1 x2 x3 , Node y1 y2 y3) → 
        lexi-compare (compare-rec h x1 y1)
         (Delay (
           lexi-compare (compare-rec h x2 y2)
            (Delay (compare-rec h x3 y3))))
    }
compare-rec (suc h) {ml-point} =
  λ x y → case x , y of λ {
    (Point x1 x2 , Point y1 y2) → 
      lexi-compare (compare-rec h x1 y1)
       (Delay (compare-rec h x2 y2))
    }
compare-rec (suc h) {ml-ref-vals a1} =
  λ x y → case x , y of λ {
    (RefVal x1 x2 , RefVal y1 y2) → 
      lexi-compare (compare-rec h x1 y1)
       (Delay (compare-rec h x2 y2))
    }
compare-rec (suc h) {ml-endo a1} =
  λ x y → case x , y of λ {
    (Endo x1 , Endo y1) → compare-rec h x1 y1
    }
compare-rec (suc h) {ml-option a1} =
  λ x y → case x , y of λ {
    (Some x1 , Some y1) → compare-rec h x1 y1
    ; (Some _ , _) → Ret Lt
    ; (_ , Some _) → Ret Gt
    ; (None , None) → Ret Eq
    }


ml-compare = compare-rec

wrap-compare : (comparator → Bool) → (h : ℕ) → (T : ml-type) → coq-type T → coq-type T → M Bool
wrap-compare wrap h T x y = do c ← compare-rec h {T} x y
                               Ret (wrap c)

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
newarray T len x = do len ← nat-of-int len
                      cnew (ml-array-t T) (ArrayVal (ncons len x))

bounded-nat-of-int : ℕ → ℤ → M ℕ
bounded-nat-of-int m n = do n ← nat-of-int n
                            case (n ℕ<? m) of λ {
                              (yes _) → Ret n ;
                              _ → Raise BoundedNat }

getarray : (T : ml-type) → (a : coq-type (ml-array T)) → (n : ℤ) → M (coq-type T)
getarray T a n = do s ← cget (ml-array-t T) a
                    case s of λ {
                      (ArrayVal u) → do n ← bounded-nat-of-int (length u) n
                                        case u of λ {
                                          [] → raise T (Invalid-argument "getarray") ;
                                          (x ∷ q) → Ret (nth x u n) } }

setarray : (T : ml-type) → (a : coq-type (ml-array T)) → (n : ℤ) → (coq-type T) → M ⊤
setarray T a n x = do s ← cget (ml-array-t T) a
                      case s of λ {
                        (ArrayVal u) → do n ← bounded-nat-of-int (length u) n
                                          cput (ml-array-t T) a (ArrayVal (set-nth x u n x)) }

-- Lazy values
force : (a : ml-type) → (lz : coq-type (ml-lazy a)) → M (coq-type a)
force a (Lval x) = Ret x
force a (Lref r) = do r' ← cget (ml-lazy-val a) r
                      (case r' of λ {
                         (LzVal x) → Ret x ;
                         (LzExn e) → raise _ e ;
                         (LzThunk f) → let ff : M (coq-type a)
                                           ff = f in
                                              handle _ (do x ← ff
                                                           do _ ← cput (ml-lazy-val a) r (LzVal x)
                                                              Ret x)
                                                       (λ e → do _ ← cput _ r (LzExn e)
                                                                 raise _ e) })

make-lazy : (a : ml-type) (b : M (coq-type a)) → M (coq-type (ml-lazy a))
make-lazy a b = do x ← cnew (ml-lazy-val a) (LzThunk b)
                   Ret (Lref x)

make-lazy-val : (a : ml-type) (b : coq-type a) → coq-type (ml-lazy a)
make-lazy-val a b = Lval b

-- Default amount of gas

h = 100000

-- Translated code

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
          ; (first ∷ rest) → do v ← float-sum h rest
                                Ret (_ℝ+_ first v)
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
          do v ← do v ← f-1 x
                    do v-1 ← f-1 (_ℝ+_ x e-1)
                       Ret (_ℝ-_ v-1 v)
             Ret (_ℝ÷_ v e-1)
          in
            do r ← (cnew ml-float (1.0))
               do _ ←
                   do u ← Ret (+ 1)
                      do v ← Ret (+ 10)
                         forloop u v
                           (λ i →
                              do v ←
                                  do v ←
                                      do v ← do v ← cget ml-float r
                                                diff e f v
                                         do v-1 ← do v ← cget ml-float r
                                                     f v
                                            Ret (_ℝ÷_ v-1 v)
                                     do v-1 ← cget ml-float r
                                        Ret (_ℝ-_ v-1 v)
                                 cput ml-float r v)
                  cget ml-float r

fact : (h : ℕ) (n : coq-type ml-int) → M (coq-type ml-int)
fact h n =
    do i ← (cnew ml-int n)
       do v ← (cnew ml-int (+ 1))
          do _ ←
              whileloop h (do v-1 ← cget ml-int i
                              ml-gt h ml-int v-1 (+ 0))
                (do _ ←
                     do v-1 ←
                         do v-1 ← cget ml-int i
                            do v-2 ← cget ml-int v
                               Ret (_*_ v-2 v-1)
                        cput ml-int v v-1
                    do v-1 ← do v-1 ← cget ml-int i
                                Ret (_-_ v-1 (+ 1))
                       cput ml-int i v-1)
             cget ml-int v

ref' : (T-1 : ml-type) → coq-type T-1 → M (coq-type (ml-ref T-1))
ref' T-1 = cnew T-1

foo1 : (T-1 : ml-type) (x : coq-type T-1) → M (coq-type T-1)
foo1 T-1 x =
    let id : (T-2 : ml-type) (y : coq-type T-2) → coq-type T-2
        id T-2 y = y in id (ml-arrow T-1 T-1) (λ x-1 → Ret (id T-1 x-1)) x

id : (T-1 : ml-type) (h-1 : coq-type T-1) → coq-type T-1
id T-1 h-1 = h-1

foo2 : (x : coq-type ml-int) → coq-type ml-int → M (coq-type ml-int)
foo2 x =
    let y = _+_ x (+ 1) in id (ml-arrow ml-int ml-int) (λ z → Ret (_+_ y z))

foo3 : (x : coq-type ml-int) → M (coq-type (ml-arrow ml-int ml-int))
foo3 x =
    id (ml-arrow ml-int (ml-arrow ml-int ml-int)) (λ x-1 → Ret (foo2 x-1)) x

incr : (r : coq-type (ml-ref ml-int)) → M (coq-type ml-unit)
incr r = do x ← (cget ml-int r)
            cput ml-int r (_+_ x (+ 1))

it-1 = Restart it (do r ← (cnew ml-int (+ 1))
                      incr r)

lazy-counter : (c : coq-type (ml-ref ml-int))
  → M (coq-type (ml-lazy ml-int))
lazy-counter c = make-lazy ml-int (do _ ← incr c
                                      cget ml-int c)

it-2 =
    Restart it-1
      (do c ← (cnew ml-int (+ 0))
          do m ← (lazy-counter c)
             do n ← (lazy-counter c)
                do n-1 ← (force ml-int n)
                   do m-1 ← (force ml-int m)
                      Ret (m-1 ∷ n-1 ∷ []))

it-3 =
    Restart it-2
      (do x ← (cnew (ml-list ml-empty) [])
          cget (ml-list ml-empty) x)

nil =
    Restart it-3
      ((λ T-1 → do x ← (cnew (ml-list T-1) [])
                   cget (ml-list T-1) x) ml-empty)

loop : (h : ℕ) (T-1 T-2 : ml-type) (h-1 : coq-type T-2)
  → M (coq-type T-1)
loop h T-1 T-2 h-1 =
    case h of λ {
      (suc h) → loop h T-1 T-2 h-1
      ; (_) → FailGas
      }

fib : (h : ℕ) (n : coq-type ml-int) → M (coq-type ml-int)
fib h n =
    case h of λ {
      (suc h) →
        do v ← ml-le h ml-int n (+ 1)
           if v then Ret (+ 1) else
              (do v ← fib h (_-_ n (+ 2))
                  do v-1 ← fib h (_-_ n (+ 1))
                     Ret (_+_ v-1 v))
      ; (_) → FailGas
      }

it-4 = Restart nil (fib h (+ 10))

ack : (h : ℕ) (m n : coq-type ml-int) → M (coq-type ml-int)
ack h m n =
    case h of λ {
      (suc h) →
        do v ← ml-le h ml-int m (+ 0)
           if v then Ret (_+_ n (+ 1)) else
              (do v ← ml-le h ml-int n (+ 0)
                  if v then ack h (_-_ m (+ 1)) (+ 1) else
                     (do v ← ack h m (_-_ n (+ 1))
                         ack h (_-_ m (+ 1)) v))
      ; (_) → FailGas
      }

it-5 = Restart it-4 (ack h (+ 3) (+ 7))

it-6 = Restart it-5 (ml-lt h ml-string "hellas" "hello")

cmp = Restart it-6 (ml-lt h ml-char 'a' 'A')

map : (h : ℕ) (T-1 T-2 : ml-type) (f : coq-type (ml-arrow T-2 T-1))
  (l : coq-type (ml-list T-2)) → M (coq-type (ml-list T-1))
map h T-1 T-2 f l =
    case h of λ {
      (suc h) →
        case l of λ {
          ([]) → Ret []
          ; (a ∷ l-1) → do v ← map h T-1 T-2 f l-1
                           do v-1 ← f a
                              Ret (v-1 ∷ v)
          }
      ; (_) → FailGas
      }

map' : (h : ℕ) (T-1 T-2 : ml-type) (f : coq-type (ml-arrow T-2 T-1))
  (param : coq-type (ml-list T-2)) → M (coq-type (ml-list T-1))
map' h T-1 T-2 f param =
    case h of λ {
      (suc h) →
        case param of λ {
          ([]) → Ret []
          ; (a ∷ l) → do v ← map' h T-1 T-2 f l
                         do v-1 ← f a
                            Ret (v-1 ∷ v)
          }
      ; (_) → FailGas
      }

it-7 =
    Restart cmp
      (map h ml-int ml-int (λ x → Ret (_+_ x (+ 1)))
         ((+ 3) ∷ (+ 2) ∷ (+ 1) ∷ []))

one = Restart it-7 (do r ← (cnew ml-int (+ 1))
                       cget ml-int r)

map3 : (h : ℕ) (T-1 : ml-type) (f : coq-type (ml-arrow T-1 ml-int))
  (param : coq-type (ml-list T-1)) → M (coq-type (ml-list ml-int))
map3 h T-1 f param =
    do one ← FromW one
       case h of λ {
         (suc h) →
           case param of λ {
             ([]) → Ret []
             ; (a ∷ l) →
                 do v ← map3 h T-1 f l
                    do v-1 ← do v ← f a
                                Ret (_+_ one v)
                       Ret (v-1 ∷ v)
             }
         ; (_) → FailGas
         }

it-8 =
    Restart one
      (map3 h ml-int (λ x → Ret (_+_ x (+ 1))) ((+ 3) ∷ (+ 2) ∷ (+ 1) ∷ []))

append : (h : ℕ) (T-1 : ml-type) (l1 l2 : coq-type (ml-list T-1))
  → M (coq-type (ml-list T-1))
append h T-1 l1 l2 =
    case h of λ {
      (suc h) →
        case l1 of λ {
          ([]) → Ret l2
          ; (a ∷ l) → do v ← append h T-1 l l2
                         Ret (a ∷ v)
          }
      ; (_) → FailGas
      }

arr = Restart it-8 (newarray ml-int (+ 3) (+ 5))

it-9 = Restart arr (do arr ← FromW arr
                       setarray ml-int arr (+ 1) (+ 6))

it-10 = Restart it-9 (ml-ge h ml-color Green Blue)

mknode : (T-1 : ml-type) (t1 t2 : coq-type (ml-tree T-1 ml-int))
  → coq-type (ml-tree T-1 ml-int)
mknode T-1 t1 t2 = Node t1 (+ 0) t2

it-11 =
    Restart it-10
      (ml-lt h (ml-tree ml-string ml-int)
         (mknode ml-string (Leaf "a") (Leaf "b"))
         (mknode ml-string (Leaf "a")
            (mknode ml-string (Leaf "b") (Leaf "b"))))

iter-int : (h : ℕ) (T-1 : ml-type) (n : coq-type ml-int)
  (f : coq-type (ml-arrow T-1 T-1)) (x : coq-type T-1) → M (coq-type T-1)
iter-int h T-1 n f x =
    case h of λ {
      (suc h) →
        do v ← ml-lt h ml-int n (+ 1)
           if v then Ret x else (do v ← f x
                                    iter-int h T-1 (_-_ n (+ 1)) f v)
      ; (_) → FailGas
      }

fib2 : (h : ℕ) (n : coq-type ml-int) → M (coq-type ml-int)
fib2 h n =
    do l1 ← (cnew ml-int (+ 1))
       do l2 ← (cnew ml-int (+ 1))
          do _ ←
              iter-int h ml-unit n
                (λ _ →
                   do x ← (cget ml-int l1)
                      do y ← (cget ml-int l2)
                         do _ ← cput ml-int l1 y
                            cput ml-int l2 (_+_ x y))
                tt
             cget ml-int l1

it-12 = Restart it-11 (fib2 h (+ 1000))

iota : (h : ℕ) (m n : coq-type ml-int) → M (coq-type (ml-list ml-int))
iota h m n =
    case h of λ {
      (suc h) →
        do v ← ml-le h ml-int n (+ 0)
           if v then Ret [] else
              (do v ← iota h (_+_ m (+ 1)) (_-_ n (+ 1))
                  Ret (m ∷ v))
      ; (_) → FailGas
      }

it-13 = Restart it-12 (iota h (+ 1) (+ 10))

r = Restart it-13 (cnew (ml-list ml-int) ((+ 3) ∷ []))

z =
    Restart r
      (do r ← FromW r
          do _ ←
              do v ← do v ← cget (ml-list ml-int) r
                        Ret ((+ 1) ∷ v)
                 cput (ml-list ml-int) r v
             cget (ml-list ml-int) r)

it-14 = Restart z (do r ← FromW r
                      cget (ml-list ml-int) r)

z' = Restart it-14 (do z ← FromW z
                       (Ret z))

it-15 =
    Restart z'
      (do r ← FromW r
          let r-1 = r in
                  do _ ←
                      do v ← do v ← cget (ml-list ml-int) r-1
                                Ret ((+ 1) ∷ v)
                         cput (ml-list ml-int) r-1 v
                     cget (ml-list ml-int) r-1)

f : (v : coq-type ml-unit) → M (coq-type (ml-list ml-int))
f v = do z' ← FromW z'
         (Ret (case v of λ {
                 (tt) → z'
                 }))

f2 : (h : ℕ) (v : coq-type ml-unit) → M (coq-type (ml-list ml-int))
f2 h v = case v of λ {
           (tt) → do v ← f tt
                     do v-1 ← f tt
                        append h ml-int v-1 v
           }

g : (h : ℕ) (x : coq-type ml-int) → M (coq-type (ml-list ml-int))
g h x =
    do z ← FromW z
       case h of λ {
         (suc h) →
           do v ← ml-gt h ml-int x (+ 0)
              if v then Ret z else g h (+ 1)
         ; (_) → FailGas
         }

double-r : (v : coq-type ml-unit) → M (coq-type ml-unit)
double-r v =
    do r ← FromW r
       case v of λ {
         (tt) →
           do v ← do v ← cget (ml-list ml-int) r
                     Ret ((+ 4) ∷ v)
              cput (ml-list ml-int) r v
         }

it-16 =
    Restart it-15 (do r ← FromW r
                      do _ ← double-r tt
                         cget (ml-list ml-int) r)

mccarthy-m : (h : ℕ) (n : coq-type ml-int) → M (coq-type ml-int)
mccarthy-m h n =
    case h of λ {
      (suc h) →
        do v ← ml-gt h ml-int n (+ 100)
           if v then Ret (_-_ n (+ 10)) else
              (do v ← mccarthy-m h (_+_ n (+ 11))
                  mccarthy-m h v)
      ; (_) → FailGas
      }

it-17 = Restart it-16 (mccarthy-m h (+ 10))

tarai : (h : ℕ) (x y z-1 : coq-type ml-int) → M (coq-type ml-int)
tarai h x y z-1 =
    case h of λ {
      (suc h) →
        do v ← ml-lt h ml-int y x
           if v then
              (do v ← tarai h (_-_ z-1 (+ 1)) x y
                  do v-1 ← tarai h (_-_ y (+ 1)) z-1 x
                     do v-2 ← tarai h (_-_ x (+ 1)) y z-1
                        tarai h v-2 v-1 v) else Ret y
      ; (_) → FailGas
      }

it-18 = Restart it-17 (tarai h (+ 1) (+ 2) (+ 3))

failwith : (T-1 : ml-type) (s : coq-type ml-string) → M (coq-type T-1)
failwith T-1 s = raise T-1 (Failure s)

it-19 = Restart it-18 (failwith ml-empty "Bad")

it-20 =
    Restart it-19
      (handle ml-string (if true then failwith ml-string "a" else Ret "b")
         (λ v → case v of λ {
                  (Failure x) → Ret x
                  ; (_) → raise ml-string v
                  }))

it-21 = Restart it-20 ((λ x → raise ml-empty x) (Failure "Hello"))

it-22 =
    Restart it-21
      (handle ml-int
         (do v ← raise ml-int (Restart-1 (λ x → Ret (+ 3)))
             Ret (id ml-int v))
         (λ v →
            case v of λ {
              (Restart-1 f-1) → f-1 tt
              ; (_) → raise ml-int v
              }))

omega : (T-1 : ml-type) (n : coq-type T-1) → M (coq-type T-1)
omega T-1 n =
    do r-1 ← (cnew (ml-arrow T-1 T-1) (λ x → Ret x))
       let delta : (i : coq-type T-1) → M (coq-type T-1)
           delta i = AppM (cget (ml-arrow T-1 T-1) r-1) i in
               do _ ← cput (ml-arrow T-1 T-1) r-1 delta
                  delta n

fixpt : (h : ℕ) (T-1 T-2 : ml-type)
  (f-1 : coq-type (ml-arrow (ml-arrow T-2 T-1) (ml-arrow T-2 T-1)))
  → M (coq-type (ml-arrow T-2 T-1))
fixpt h T-1 T-2 f-1 =
    do r-1 ← (cnew (ml-arrow T-2 T-1) (λ x → loop h T-1 T-2 x))
       let delta : (i : coq-type T-2) → M (coq-type T-1)
           delta i = do v ← cget (ml-arrow T-2 T-1) r-1
                        AppM (f-1 v) i
             in do _ ← cput (ml-arrow T-2 T-1) r-1 delta
                   Ret delta

fib-1 =
    Restart it-22
      (fixpt h ml-int ml-int
         (λ fib-1 →
            Ret
              (λ n →
                 do v ← ml-le h ml-int n (+ 1)
                    if v then Ret (+ 1) else
                       (do v ← fib-1 (_-_ n (+ 2))
                           do v-1 ← fib-1 (_-_ n (+ 1))
                              Ret (_+_ v-1 v)))))

it-23 = Restart fib-1 (do fib-1 ← FromW fib-1
                          fib-1 (+ 10))

it-24 = Restart it-23 (omega ml-int (+ 1))

it-25 =
    Restart it-24 (AppM (fixpt h ml-empty ml-int (λ f-1 → Ret f-1)) (+ 0))


