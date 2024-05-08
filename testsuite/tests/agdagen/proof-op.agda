open import agdagen_defs
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Maybe.Base

-- thanks to @gallais on zulip (https://agda.zulipchat.com/#user/353727) for his tip on this!
-- the link https://github.com/gallais/potpourri/blob/main/agda/poc/LinearDec.agda helped me
-- to simplify the proof a lot

-- #############################################

data ml-type : Set where
  ml-int : ml-type
  ml-char : ml-type
  ml-list : ml-type → ml-type
  ml-arrow : ml-type → ml-type → ml-type

variable
  u1 u2 u3 u4 u5 u6 v1 v2 v3 v4 v5 v6 : ml-type
  A B C D E F : Set

-- #############################################

data _~_ : (T1 T2 : ml-type) → Set where
  ~ml-int : ml-int ~ ml-int
  ~ml-char : ml-char ~ ml-char
  ~ml-list : (u1 v1 : ml-type) → ml-list u1 ~ ml-list v1
  ~ml-arrow : (u1 u2 v1 v2 : ml-type) → ml-arrow u1 u2 ~ ml-arrow v1 v2

up3-dec : (Dec A) → (Dec B) → (Dec C) → Dec (up3 A B C)
up3-dec (yes a1) (yes a2) (yes a3) = yes (a1 ,, a2 ,, a3)
up3-dec (no a) _ _ = no (λ z → a (proj₁ z))
up3-dec _ (no a) _ = no (λ z → a (proj₂ z))
up3-dec _ _ (no a) = no (λ z → a (proj₃ z))

up4-dec : Dec A → Dec B → Dec C → Dec D → Dec (up4 A B C D)
up4-dec (yes a1) (yes a2) (yes a3) (yes a4) = yes (a1 ,,, a2 ,,, a3 ,,, a4)
up4-dec (no a) _ _ _ = no (λ z → a (proj₁ z))
up4-dec _ (no a) _ _ = no (λ z → a (proj₂ z))
up4-dec _ _ (no a) _ = no (λ z → a (proj₃ z))
up4-dec _ _ _ (no a) = no (λ z → a (proj₄ z))

up5-dec : Dec A → Dec B → Dec C → Dec D → Dec E → Dec (up5 A B C D E)
up5-dec (yes a1) (yes a2) (yes a3) (yes a4) (yes a5) = yes (a1 ,,,, a2 ,,,, a3 ,,,, a4 ,,,, a5)
up5-dec (no a) _ _ _ _ = no (λ z → a (proj₁ z))
up5-dec _ (no a) _ _ _ = no (λ z → a (proj₂ z))
up5-dec _ _ (no a) _ _ = no (λ z → a (proj₃ z))
up5-dec _ _ _ (no a) _ = no (λ z → a (proj₄ z))
up5-dec _ _ _ _ (no a) = no (λ z → a (proj₅ z))

up6-dec : Dec A → Dec B → Dec C → Dec D → Dec E → Dec F → Dec (up6 A B C D E F)
up6-dec (yes a1) (yes a2) (yes a3) (yes a4) (yes a5) (yes a6) = yes (a1 ,,,,, a2 ,,,,, a3 ,,,,, a4 ,,,,, a5 ,,,,, a6)
up6-dec (no a) _ _ _ _ _ = no (λ z → a (proj₁ z))
up6-dec _ (no a) _ _ _ _ = no (λ z → a (proj₂ z))
up6-dec _ _ (no a) _ _ _ = no (λ z → a (proj₃ z))
up6-dec _ _ _ (no a) _ _ = no (λ z → a (proj₄ z))
up6-dec _ _ _ _ (no a) _ = no (λ z → a (proj₅ z))
up6-dec _ _ _ _ _ (no a) = no (λ z → a (proj₆ z))

view : (T1 T2 : ml-type) →  Maybe (T1 ~ T2)
view ml-int ml-int = just ~ml-int
view ml-char ml-char = just ~ml-char
view (ml-list u1) (ml-list v1) = just (~ml-list u1 v1)
view (ml-arrow u1 u2) (ml-arrow v1 v2) = just (~ml-arrow u1 u2 v1 v2)
view _ _ = nothing

view-diag : (T : ml-type) → ¬ (view T T ≡ nothing)
view-diag ml-int()
view-diag ml-char()
view-diag (ml-list _) ()
view-diag (ml-arrow _ _) ()

ml-list-inj : ml-list u1 ≡ ml-list v1 → (u1 ≡ v1)
ml-list-inj refl = refl

ml-arrow-inj : ml-arrow u1 u2 ≡ ml-arrow v1 v2 → _×_ (u1 ≡ v1) (u2 ≡ v2)
ml-arrow-inj refl = refl , refl

ml-list-cong : (u1 ≡ v1) → ml-list u1 ≡ ml-list v1
ml-list-cong (refl) = refl

ml-arrow-cong : _×_ (u1 ≡ v1) (u2 ≡ v2) → ml-arrow u1 u2 ≡ ml-arrow v1 v2
ml-arrow-cong (refl , refl) = refl

eq-decc : (T1 T2 : ml-type) → Dec (T1 ≡ T2)
eq-decc T1 T2 with view T1 T2 | inspect (view T1) T2
eq-decc _ _ | just ~ml-int | _ = yes refl
eq-decc _ _ | just ~ml-char | _ = yes refl
eq-decc _ _ | just (~ml-list u1 v1) | _ = map′ ml-list-cong ml-list-inj ((eq-decc u1 v1))
eq-decc _ _ | just (~ml-arrow u1 u2 v1 v2) | _ = map′ ml-arrow-cong ml-arrow-inj (_×-dec_ (eq-decc u1 v1) (eq-decc u2 v2))
eq-decc m n | nothing | [ eq ] = no λ where refl → view-diag _ eq


{-eq-decc : (T1 T2 : ml-type) → Dec (T1 ≡ T2)
eq-decc T1 T2 with view T1 T2 | inspect (view T1) T2
eq-decc _ _ | just ~ml-int                 | _      = yes refl
eq-decc _ _ | just ~ml-char                | _      = yes refl
eq-decc _ _ | just (~ml-list u v)          | _      = map′ ml-list-cong ml-list-inj (eq-decc u v)
eq-decc _ _ | just (~ml-arrow u1 u2 v1 v2) | _      = map′ ml-arrow-cong ml-arrow-inj (_×-dec_ (eq-decc u1 v1) (eq-decc u2 v2))
eq-decc m n | nothing                      | [ eq ] = no λ where refl → view-diag _ eq-}

















{-data _~_ : (T1 T2 : ml-type) → Set where
  ~ml-int : ml-int ~ ml-int
  ~ml-char : ml-char ~ ml-char
  ~ml-list : (u v : ml-type) → ml-list u ~ ml-list v
  ~ml-arrow : (u1 u2 v1 v2 : ml-type) → ml-arrow u1 u2 ~ ml-arrow v1 v2


view : (T1 T2 : ml-type) → Maybe (T1 ~ T2)
view ml-int ml-int = just ~ml-int
view ml-char ml-char = just ~ml-char
view (ml-list u) (ml-list v) = just (~ml-list u v)
view (ml-arrow u1 u2) (ml-arrow v1 v2) = just (~ml-arrow u1 u2 v1 v2)
view _ _ = nothing

view-diag : (T : ml-type) → ¬ (view T T ≡ nothing)
view-diag ml-int ()
view-diag ml-char ()
view-diag (ml-list _) ()
view-diag (ml-arrow _ _) ()

ml-list-inj : ml-list u1 ≡ ml-list v1 → (u1 ≡ v1)
ml-list-inj refl = refl

ml-list-cong : (u1 ≡ v1) → ml-list u1 ≡ ml-list v1
ml-list-cong (refl) = refl

ml-arrow-inj : ml-arrow u1 u2 ≡ ml-arrow v1 v2 → _×_ (u1 ≡ v1) (u2 ≡ v2)
ml-arrow-inj refl = refl , refl

ml-arrow-cong : _×_ (u1 ≡ v1) (u2 ≡ v2) → ml-arrow u1 u2 ≡ ml-arrow v1 v2
ml-arrow-cong (refl , refl) = refl


up3-dec : (Dec A) → (Dec B) → (Dec C) → Dec (up3 A B C)
up3-dec (yes a1) (yes a2) (yes a3) = yes (a1 ,, a2 ,, a3)
up3-dec (no a) _ _ = no (λ z → a (proj₁ z))
up3-dec _ (no a) _ = no (λ z → a (proj₂ z))
up3-dec _ _ (no a) = no (λ z → a (proj₃ z))

up4-dec : Dec A → Dec B → Dec C → Dec D → Dec (up4 A B C D)
up4-dec (yes a1) (yes a2) (yes a3) (yes a4) = yes (a1 ,,, a2 ,,, a3 ,,, a4)
up4-dec (no a) _ _ _ = no (λ z → a (proj₁ z))
up4-dec _ (no a) _ _ = no (λ z → a (proj₂ z))
up4-dec _ _ (no a) _ = no (λ z → a (proj₃ z))
up4-dec _ _ _ (no a) = no (λ z → a (proj₄ z))

up5-dec : Dec A → Dec B → Dec C → Dec D → Dec E → Dec (up5 A B C D E)
up5-dec (yes a1) (yes a2) (yes a3) (yes a4) (yes a5) = yes (a1 ,,,, a2 ,,,, a3 ,,,, a4 ,,,, a5)
up5-dec (no a) _ _ _ _ = no (λ z → a (proj₁ z))
up5-dec _ (no a) _ _ _ = no (λ z → a (proj₂ z))
up5-dec _ _ (no a) _ _ = no (λ z → a (proj₃ z))
up5-dec _ _ _ (no a) _ = no (λ z → a (proj₄ z))
up5-dec _ _ _ _ (no a) = no (λ z → a (proj₅ z))

up6-dec : Dec A → Dec B → Dec C → Dec D → Dec E → Dec F → Dec (up6 A B C D E F)
up6-dec (yes a1) (yes a2) (yes a3) (yes a4) (yes a5) (yes a6) = yes (a1 ,,,,, a2 ,,,,, a3 ,,,,, a4 ,,,,, a5 ,,,,, a6)
up6-dec (no a) _ _ _ _ _ = no (λ z → a (proj₁ z))
up6-dec _ (no a) _ _ _ _ = no (λ z → a (proj₂ z))
up6-dec _ _ (no a) _ _ _ = no (λ z → a (proj₃ z))
up6-dec _ _ _ (no a) _ _ = no (λ z → a (proj₄ z))
up6-dec _ _ _ _ (no a) _ = no (λ z → a (proj₅ z))
up6-dec _ _ _ _ _ (no a) = no (λ z → a (proj₆ z))






eq-decc : (T1 T2 : ml-type) → Dec (T1 ≡ T2)
eq-decc T1 T2 with view T1 T2 | inspect (view T1) T2
eq-decc _ _ | just ~ml-int                 | _      = yes refl
eq-decc _ _ | just ~ml-char                | _      = yes refl
eq-decc _ _ | just (~ml-list u v)          | _      = map′ ml-list-cong ml-list-inj (eq-decc u v)
eq-decc _ _ | just (~ml-arrow u1 u2 v1 v2) | _      = map′ ml-arrow-cong ml-arrow-inj (_×-dec_ (eq-decc u1 v1) (eq-decc u2 v2))
eq-decc m n | nothing                      | [ eq ] = no λ where refl → view-diag _ eq-}


--map′ (cong ml-list) (λ where refl → refl) (eq-decc m n)
