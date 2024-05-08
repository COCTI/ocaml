open import agdagen_defs
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_×_ to up2)

-- #############################################

data ml-type : Set where
  ml-int : ml-type
  ml-char : ml-type
  ml-list : ml-type → ml-type
  ml-arrow : ml-type → ml-type → ml-type
  ml-trip : ml-type → ml-type → ml-type → ml-type

-- #############################################

g-int : ml-type → Set
g-int (ml-int) = ⊤
g-int _ = ⊥

g-char : ml-type → Set
g-char (ml-char) = ⊤
g-char _ = ⊥

g-list : ml-type → Set
g-list (ml-list _) = ⊤
g-list _ = ⊥

g-arrow : ml-type → Set
g-arrow (ml-arrow _ _) = ⊤
g-arrow _ = ⊥

-- #############################################

ml-list-inj : {T1 T2 : ml-type} → ml-list T1 ≡ ml-list T2 → T1 ≡ T2
ml-list-inj refl = refl

ml-arrow-inj : {T1 T2 T3 T4 : ml-type} → ml-arrow T1 T2 ≡ ml-arrow T3 T4 → up2 (T1 ≡ T3) (T2 ≡ T4)
ml-arrow-inj refl = refl , refl

ml-trip-inj : {T1 T2 T3 T4 T5 T6 : ml-type} → ml-trip T1 T3 T5 ≡ ml-trip T2 T4 T6 → up3 (T1 ≡ T2) (T3 ≡ T4) (T5 ≡ T6)
ml-trip-inj refl = refl ,, refl ,, refl

ml-arrow-cong : {u1 v1 u2 v2 : ml-type} → up2 (u1 ≡ u2) (v1 ≡ v2) → ml-arrow u1 v1 ≡ ml-arrow u2 v2
ml-arrow-cong (refl , refl) = refl




type-equal-list : {T1 T2 : ml-type} → ((T1 ≡ T2) ⊎ (T1 ≢ T2)) → ml-list T1 ≡ ml-list T2 ⊎ ml-list T1 ≢ ml-list T2
type-equal-list (inj₁ refl) = inj₁ refl
type-equal-list (inj₂ x) = inj₂ λ z → x (ml-list-inj z)

type-equal-arrow : {T1 T2 T3 T4 : ml-type} → up2 ((T1 ≡ T3) ⊎ (T1 ≢ T3)) ((T2 ≡ T4) ⊎ (T2 ≢ T4)) → (ml-arrow T1 T2 ≡ ml-arrow T3 T4) ⊎ (ml-arrow T1 T2 ≢ ml-arrow T3 T4)
type-equal-arrow (inj₁ refl , inj₁ refl) = inj₁ refl
type-equal-arrow (_ , inj₂ x) = inj₂ λ z → x (proj₂ (ml-arrow-inj z))
type-equal-arrow (inj₂ x , _) = inj₂ λ z → x (proj₁ (ml-arrow-inj z))

type-equal-trip : {T1 T2 T3 T4 T5 T6 : ml-type} → up3 ((T1 ≡ T2) ⊎ (T1 ≢ T2)) ((T3 ≡ T4) ⊎ (T3 ≢ T4)) ((T5 ≡ T6) ⊎ (T5 ≢ T6)) → (ml-trip T1 T3 T5 ≡ ml-trip T2 T4 T6) ⊎ (ml-trip T1 T3 T5 ≢ ml-trip T2 T4 T6)
type-equal-trip (inj₁ refl ,, inj₁ refl ,, inj₁ refl) = inj₁ refl
type-equal-trip (_ ,, _ ,, inj₂ x) = inj₂ λ z → x (proj₃ (ml-trip-inj z))
type-equal-trip (_ ,, inj₂ x ,, _) = inj₂ λ z → x (proj₂ (ml-trip-inj z))
type-equal-trip (inj₂ x ,, _ ,, _) = inj₂ λ z → x (proj₁ (ml-trip-inj z))

-- #############################################

not-ml-int : (y : ml-type) → (ml-int ≡ y) → (g-int y)
not-ml-int y = eq-ind ml-int g-int tt y

not-ml-char : (y : ml-type) → (ml-char ≡ y) → (g-char y)
not-ml-char y = eq-ind ml-char g-char tt y

not-ml-list : {T : ml-type} → (y : ml-type) → (ml-list T ≡ y) → (g-list y)
not-ml-list y = eq-ind (ml-list _) g-list tt y

not-ml-arrow : {T1 T2 : ml-type} → (y : ml-type) → (ml-arrow T1 T2 ≡ y) → (g-arrow y)
not-ml-arrow y = eq-ind (ml-arrow _ _) g-arrow tt y

-- #############################################

interleaved mutual

    ml-type-eq-dec-comp : (T1 T2 : ml-type) → (T1 ≡ T2) ⊎ (T1 ≢ T2)
    ml-type-eq-dec-int : (T : ml-type) → (ml-int ≡ T) ⊎ (ml-int ≢ T)
    ml-type-eq-dec-char : (T : ml-type) → (ml-char ≡ T) ⊎ (ml-char ≢ T)
    ml-type-eq-dec-list : (u T : ml-type) → (ml-list u ≡ T) ⊎ (ml-list u ≢ T)
    ml-type-eq-dec-arrow : (u1 u2 T : ml-type) → (ml-arrow u1 u2 ≡ T) ⊎ (ml-arrow u1 u2 ≢ T)


    ml-type-eq-dec-comp ml-int T = ml-type-eq-dec-int T
    ml-type-eq-dec-comp ml-char T = ml-type-eq-dec-char T
    ml-type-eq-dec-comp (ml-list u) T = ml-type-eq-dec-list u T
    ml-type-eq-dec-comp (ml-arrow u1 u2)  T = ml-type-eq-dec-arrow u1 u2 T


    ml-type-eq-dec-int ml-int = inj₁ refl
    ml-type-eq-dec-int (ml-list T) = inj₂ (not-ml-int (ml-list T))
    ml-type-eq-dec-int ml-char = inj₂ (not-ml-int ml-char)
    ml-type-eq-dec-int (ml-arrow T1 T2) = inj₂ (not-ml-int (ml-arrow T1 T2))

    ml-type-eq-dec-char ml-char = inj₁ refl
    ml-type-eq-dec-char (ml-list T) = inj₂ (not-ml-char (ml-list T))
    ml-type-eq-dec-char ml-int = inj₂ (not-ml-char ml-int)
    ml-type-eq-dec-char (ml-arrow T1 T2) = inj₂ (not-ml-char (ml-arrow T1 T2))

    ml-type-eq-dec-list u (ml-list v) = type-equal-list (ml-type-eq-dec-comp u v)
    ml-type-eq-dec-list _ ml-char = inj₂ (not-ml-list ml-char)
    ml-type-eq-dec-list _ ml-int = inj₂ (not-ml-list ml-int)
    ml-type-eq-dec-list _ (ml-arrow T1 T2) = inj₂ (not-ml-list (ml-arrow T1 T2))

    ml-type-eq-dec-arrow u1 u2 (ml-arrow v1 v2) = type-equal-arrow (ml-type-eq-dec-comp u1 v1 , ml-type-eq-dec-comp u2 v2)
    ml-type-eq-dec-arrow _ _ ml-char = inj₂ (not-ml-arrow ml-char)
    ml-type-eq-dec-arrow _ _ ml-int = inj₂ (not-ml-arrow ml-int)
    ml-type-eq-dec-arrow _ _ (ml-list T1) = inj₂ (not-ml-arrow (ml-list T1))
