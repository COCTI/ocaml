open import agdagen_defs

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool using (true; false; Bool; if_then_else_)
open import Relation.Nullary.Decidable.Core using (_because_; isYes)
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)
open import Data.String
open import Data.Float using (Float)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Unit
open import Data.List using (List)


data ml-type : Set where
  ml-int : ml-type
  ml-char : ml-type
  ml-float : ml-type
  ml-bool : ml-type
  ml-unit : ml-type
  ml-exn : ml-type
--  ml-array : ml-type → ml-type
  ml-list : ml-type → ml-type
  ml-string : ml-type


postulate ml-type-eq-dec-b : (T1 T2 : ml-type) → (T1 ≡ T2) ⊎ (T1 ≢ T2)

ml-type-eq-dec : DecidableEquality ml-type
ml-type-eq-dec T1 T2 = case ml-type-eq-dec-b T1 T2 of λ {
                            (inj₁ a) → true because ofʸ a
                            ; (inj₂ b) → false because ofⁿ b }

data ml-exns : Set where
  Invalid-argument : String → ml-exns
  Failure : String → ml-exns
  Not-found : ml-exns

coq-type : (M : Set → Set) (T : ml-type) → Set
coq-type M ml-int = ℕ
coq-type M ml-char = Char
coq-type M ml-float = Float
coq-type M ml-bool = Bool
coq-type M ml-unit = ⊤
coq-type M ml-exn = ml-exns
--coq-type ml-array T1 = loc (ml-array-t T1)
coq-type M (ml-list T1) = List (coq-type M T1)
--coq-type ml-lazy T1 = lazy-t (coq-type T1) T1
coq-type M ml-string = String
{- coq-type ml-empty = empty
--coq-type ml-array-t T1 = array-t (coq-type T1)
--coq-type ml-m T1 = m (coq-type T1)
--coq-type ml-lazy-val T1 = lazy-val (coq-type T1)
--coq-type ml-ref T1 = loc T1
--coq-type ml-arrow T1 T2 = coq-type T1 -> M (coq-type T2) -}

instance
  ml-type-is-eq-dec : eqType ml-type
  ml-type-is-eq-dec = record {eq-dec = ml-type-eq-dec}

MLtypes : MLTY
MLtypes = record {
  ml-type = ml-type;
  ml-exn = ml-exn;
  coq-type = coq-type
  }
