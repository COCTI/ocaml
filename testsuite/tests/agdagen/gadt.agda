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
  ml-uu : (ml-type) → ml-type
  ml-lisT : (ml-type) → ml-type
  ml-twi : (ml-type) → ml-type
  ml-recu : ml-type
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
  ~ml-uu : (u1 v1 : ml-type) → ml-uu u1 ~ ml-uu v1
  ~ml-lisT : (u1 v1 : ml-type) → ml-lisT u1 ~ ml-lisT v1
  ~ml-twi : (u1 v1 : ml-type) → ml-twi u1 ~ ml-twi v1
  ~ml-recu : ml-recu ~ ml-recu
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
view (ml-uu u1) (ml-uu v1) = just (~ml-uu u1 v1)
view (ml-lisT u1) (ml-lisT v1) = just (~ml-lisT u1 v1)
view (ml-twi u1) (ml-twi v1) = just (~ml-twi u1 v1)
view ml-recu ml-recu = just ~ml-recu
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
view-diag (ml-uu _) ()
view-diag (ml-lisT _) ()
view-diag (ml-twi _) ()
view-diag ml-recu()
view-diag (ml-lazy-val _) ()
view-diag (ml-ref _) ()
view-diag (ml-arrow _ _) ()

ml-list-inj : ml-list u1 ≡ ml-list v1 → (u1 ≡ v1)
ml-list-inj refl = refl

ml-lazy-inj : ml-lazy u1 ≡ ml-lazy v1 → (u1 ≡ v1)
ml-lazy-inj refl = refl

ml-array-t-inj : ml-array-t u1 ≡ ml-array-t v1 → (u1 ≡ v1)
ml-array-t-inj refl = refl

ml-uu-inj : ml-uu u1 ≡ ml-uu v1 → (u1 ≡ v1)
ml-uu-inj refl = refl

ml-lisT-inj : ml-lisT u1 ≡ ml-lisT v1 → (u1 ≡ v1)
ml-lisT-inj refl = refl

ml-twi-inj : ml-twi u1 ≡ ml-twi v1 → (u1 ≡ v1)
ml-twi-inj refl = refl

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

ml-uu-cong : (u1 ≡ v1) → ml-uu u1 ≡ ml-uu v1
ml-uu-cong (refl) = refl

ml-lisT-cong : (u1 ≡ v1) → ml-lisT u1 ≡ ml-lisT v1
ml-lisT-cong (refl) = refl

ml-twi-cong : (u1 ≡ v1) → ml-twi u1 ≡ ml-twi v1
ml-twi-cong (refl) = refl

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
eq-decc _ _ | just (~ml-uu u1 v1) | _ = map′ ml-uu-cong ml-uu-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-lisT u1 v1) | _ = map′ ml-lisT-cong ml-lisT-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-twi u1 v1) | _ = map′ ml-twi-cong ml-twi-inj ((eq-decc u1 v1))
eq-decc _ _ | just ~ml-recu | _ = yes refl
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
  
  data recu : Set where
    R : (recu) → recu
  
  data twi (a : Set) : Set where
    TW : (a) → (ℤ) → (ℤ) → twi a
  
  data q : Set → Set₁ where
    Q1 : {a : Set} → (a) → q a
    Q2 : {b : Set} → {c : Set} → {a-1 : Set} → (b) → (a-1) → (c) → q a-1
  
  data point : Set → Set → Set₁ where
    NNpoint : (ℤ) → (ℤ) → point ℤ ℤ
    FFpoint : (Float) → (Float) → point Float Float
    NFpoint : (ℤ) → (Float) → point ℤ Float
    FNpoint : (Float) → (ℤ) → point Float ℤ
    OOpoint : {b-1 : Set} → {a-1 : Set} → (a-1) → (b-1) → point a-1 b-1
  
  data gadt-lisT : Set → Set₁ where
    E-g : {r : Set} → gadt-lisT r
    C-g : {r : Set} → (r) → (gadt-lisT r) → gadt-lisT r
  
  data lisT (a : Set) : Set where
    E-1 : lisT a
    C-1 : (a) → (lisT a) → lisT a
  
  data uu (uu-1 : Set) : Set where
    UU : (uu-1) → uu uu-1
  
  data expr : Set → Set₁ where
    EBinop : expr (ℤ → M (ℤ → M ℤ))
    EApp : {a-1 : Set} → {b : Set} → (expr (a-1 → M b)) → (expr a-1) → expr b
    EInt : (ℤ) → expr ℤ
    EBool : (Bool) → expr Bool
  
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
        ; (ml-uu T1) → uu (coq-type T1)
        ; (ml-lisT T1) → lisT (coq-type T1)
        ; (ml-twi T1) → twi (coq-type T1)
        ; (ml-recu) → recu
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
compare-rec (suc h) {ml-uu a1} =
  λ x y → case x , y of λ {
    (UU x1 , UU y1) → compare-rec h x1 y1
    }
compare-rec (suc h) {ml-lisT a1} =
  λ x y → case x , y of λ {
    (E-1 , E-1) → Ret Eq
    ; (E-1 , _) → Ret Lt
    ; (_ , E-1) → Ret Gt
    ; (C-1 x1 x2 , C-1 y1 y2) → 
        lexi-compare (compare-rec h x1 y1)
         (Delay (compare-rec h x2 y2))
    }
compare-rec (suc h) {ml-twi a1} =
  λ x y → case x , y of λ {
    (TW x1 x2 x3 , TW y1 y2 y3) → 
      lexi-compare (compare-rec h x1 y1)
       (Delay (
         lexi-compare (compare-rec h x2 y2)
          (Delay (compare-rec h x3 y3))))
    }
compare-rec (suc h) {ml-recu} =
  λ x y → case x , y of λ {
    (R x1 , R y1) → compare-rec h x1 y1
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

eval : (h : ℕ) (a : ml-type) (param : expr M a) → M (coq-type a)
eval h a param =
    case h of λ {
      (suc h) →
        case param of λ {
          (EInt n) → Ret n
          ; (EBool b) → Ret b
          ; (EBinop) → Ret (λ x → Ret (λ y → Ret (_+_ x y)))
          ; (EApp f x) → do v ← eval h _ x
                            AppM (eval h (ml-arrow _ a) f) v
          }
      ; (_) → FailGas
      }

e1 : expr M ℤ
e1 = EApp (EApp EBinop (EInt (+ 5))) (EInt (+ 8))

f : (T-1 : ml-type) (x : coq-type (ml-twi T-1)) → coq-type ml-int
f T-1 x = case x of λ {
            (TW _ m n) → _+_ m n
            }

u : q M ℤ
u = Q1 (+ 5)

add-int : (i1 i2 : expr M ℤ) → coq-type ml-int
add-int i1 i2 =
    case i1 of λ {
      (EInt a) → case i2 of λ {
                   (EInt b) → _+_ a b
                   ; (_) → (+ 0)
                   }
      ; (_) → (+ 0)
      }


