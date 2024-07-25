open import agdagen_defs public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Relation.Binary.Definitions using (DecidableEquality) public
open import Data.Bool using (true; false; Bool; if_then_else_) public
open import Relation.Nullary.Decidable.Core using (_because_; isYes; Dec; yes) public
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ) public
open import Data.String using (String) public
open import Data.Float using (Float)
  renaming (_+_ to _ℝ+_; _*_ to _ℝ*_; _-_ to _ℝ-_; _÷_ to _ℝ÷_; -_ to ℝ-_) public
open import Data.Char using (Char) public
open import Data.Nat using (ℕ; suc) renaming (_<?_ to _ℕ<?_) public
open import Data.Unit using (⊤; tt) public
open import Data.List using (List; []; length; _∷_) public
open import Data.Product using (_×_ ; _,_; proj₁ ; proj₂; _,′_) public
open import Data.Empty using (⊥) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Relation.Nullary using (¬_) public
open import Relation.Nullary.Decidable using (map′; _×-dec_; no) public
open import Relation.Binary.PropositionalEquality using (inspect; [_]) public
open import Data.Integer using (ℤ; _+_; _-_; _*_; +_; -_) public
open import Data.Integer.DivMod using (_/_) public
open import Function.Base using (case_of_) public

-- Generated representation of all ML types

data ml-type : Set where
  ml-int : ml-type
  ml-char : ml-type
  ml-float : ml-type
  ml-bool : ml-type
  ml-unit : ml-type
  ml-exn : ml-type
  ml-list : (ml-type) → ml-type
  ml-string : ml-type
  ml-empty : ml-type
  ml-uu : (ml-type) → ml-type
  ml-lisT : (ml-type) → ml-type
  ml-ref : (ml-type) → ml-type
  ml-arrow : (ml-type) → (ml-type) → ml-type

postulate ml-type-eq-dec : DecidableEquality ml-type

instance
  ml-type-is-eq-dec : eqType ml-type
  ml-type-is-eq-dec = record {eq-dec = ml-type-eq-dec}

data tagged (s : String)(t : Set) : Set where
    Tagged : t → tagged s t

ℤ* = tagged "Z" ℤ
Char* = tagged "char" Char
Float* = tagged "float" Float
Bool* = tagged "bool" Bool

module MLtypes-aux (M : Set → Set) where
  -- Generated type definitions
  loc = loc-b ml-type

  data ml-exns : Set where
    Invalid-argument : (String) → ml-exns
    Failure : (String) → ml-exns
    Not-found : ml-exns

  data q : Set → Set₁ where
    Q1 : {a : Set} → (a) → q a
    Q2 : {b : Set} → {c : Set} → {a-1 : Set} → (b) → (a-1) → (c) → q a-1

  data gadt-lisT : Set → Set₁ where
    E-g : {r : Set} → gadt-lisT r
    C-g : {r : Set} → (r) → (gadt-lisT r) → gadt-lisT r

  data lisT (a : Set) : Set where
    E-1 : lisT a
    C-1 : (a) → (lisT a) → lisT a

  data uu (uu-1 : Set) : Set where
    UU : (uu-1) → uu uu-1

  data point : Set → Set → Set₁ where
    NNpoint : (ℤ) → (ℤ) → point ℤ ℤ
    FFpoint : (Float) → (Float) → point Float Float
    NFpoint : (ℤ) → (Float) → point ℤ Float
    FNpoint : (Float) → (ℤ) → point Float ℤ
    OOpoint : {b-1 : Set} → {a-1 : Set} → (a-1) → (b-1) → point a-1 b-1

  data expr : Set → Set₁ where
    EBinop : expr (ℤ → M (ℤ → M ℤ))
    EApp : {a-1 : Set} → {b : Set} → (expr (a-1 → M b)) → (expr a-1) → expr b
    EInt : (ℤ) → expr ℤ
    EBool : (Bool) → expr Bool

  -- Generated type translation function
  coq-type : (T : ml-type) → Set
  coq-type T =
      case T of λ {
        ml-int → ℤ
        ; (ml-char) → Char
        ; (ml-float) → Float
        ; (ml-bool) → Bool
        ; (ml-unit) → ⊤
        ; (ml-exn) → ml-exns
        ; (ml-list T1) → List (coq-type T1)
        ; (ml-string) → String
        ; (ml-empty) → ⊥
        ; (ml-uu T1) → uu (coq-type T1)
        ; (ml-lisT T1) → lisT (coq-type T1)
        ; (ml-ref T1) → loc T1
        ; (ml-arrow T1 T2) → coq-type T1 → M (coq-type T2)
        }

open MLtypes-aux hiding (loc; coq-type) public
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
open REFmonad REFmonadML public

empty-env : Env2
empty-env = mkEnv []

it : W ⊤
it = inj₂ (inj₂ tt , empty-env)

-- Default amount of gas

h = 100000

-- Translated code

{-Bool
⊤
ml-exns
List (coq-type T1)
String
; (ml-empty) → ⊥
; (ml-uu T1) → uu (coq-type T1)
; (ml-lisT T1) → lisT (coq-type T1)
; (ml-ref T1) → loc T1
; (ml-arrow T1 T2) → coq-type T1 → M (coq-type T2)-}

-- code généré
{-
eval : (h : ℕ) (a : ml-type) (param : expr M (coq-type a)) → M (coq-type a)
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
      }-}

-- code fonctionnel
{-
eval : (h : ℕ) (a : Set) (param : expr M a) → M a
eval h a param =
    case h of λ {
      (suc h) →
        case param of λ {
          (EInt n) → Ret n
          ; (EBool b) → Ret b
          ; (EBinop) → Ret (λ x → Ret (λ y → Ret (_+_ x y)))
          ; (EApp f x) → do v ← eval h _ x
                            AppM (eval h (_ → M a) f) v
          }
      ; (_) → FailGas
      }-}
















{-
e1 : expr M ℤ
e1 = EApp (EApp EBinop (EInt (+ 5))) (EInt (+ 8))

u : q M ℤ
u = Q1 (+ 5)-}
{-
add-int : (i1 i2 : expr M ℤ) → coq-type ml-int
add-int i1 i2 =
    case i1 of λ {
      (EInt a) → case i2 of λ {
                   (EInt b) → _+_ a b
                   ; (_) → (+ 0)
                   }
      ; (_) → (+ 0)
      }
-}
