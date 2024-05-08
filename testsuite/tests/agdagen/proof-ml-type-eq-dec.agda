open import agdagen_defs
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product

-- #############################################

eq-ind : {A : Set} (x : A) (P : A → Set) (f : P x) (a : A) (e : x ≡ a) → P a
eq-ind x P f .x refl = f

-- #############################################

data ml-type : Set where
  ml-int : ml-type
  ml-char : ml-type
  {-ml-float : ml-type
  ml-bool : ml-type
  ml-unit : ml-type
  ml-exn : ml-type
  ml-array : ml-type → ml-type-}
  ml-list : ml-type → ml-type
  {-ml-lazy : ml-type → ml-type
  ml-string : ml-type
  ml-empty : ml-type
  ml-array-t : ml-type → ml-type
  ml-m : ml-type → ml-type
  ml-lazy-val : ml-type → ml-type
  ml-ref : ml-type → ml-type-}
  ml-arrow : ml-type → ml-type → ml-type


-- #############################################

g-int : ml-type → Set
g-int ml-int = ⊤
g-int _ = ⊥

g-char : ml-type → Set
g-char ml-char = ⊤
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

ml-arrow-inj : {T1 T2 T3 T4 : ml-type} → ml-arrow T1 T2 ≡ ml-arrow T3 T4 → (T1 ≡ T3) × (T2 ≡ T4)
ml-arrow-inj refl = refl , refl

type-equal-list : {T1 T2 : ml-type} → ((T1 ≡ T2) ⊎ (T1 ≢ T2)) → ml-list T1 ≡ ml-list T2 ⊎ ml-list T1 ≢ ml-list T2
type-equal-list (inj₁ refl) = inj₁ refl
type-equal-list (inj₂ y) = inj₂ λ f → y (ml-list-inj f)

type-equal-arrow : {T1 T2 T3 T4 : ml-type} → ((T1 ≡ T3) ⊎ (T1 ≢ T3)) × ((T2 ≡ T4) ⊎ (T2 ≢ T4)) → (ml-arrow T1 T2 ≡ ml-arrow T3 T4) ⊎ (ml-arrow T1 T2 ≢ ml-arrow T3 T4)
type-equal-arrow (inj₁ refl , inj₁ refl) = inj₁ refl
type-equal-arrow (_ , inj₂ y) = inj₂ λ z → y (proj₂ (ml-arrow-inj z))
type-equal-arrow (inj₂ x , _) = inj₂ λ z → x (proj₁ (ml-arrow-inj z))

x : ℕ × ℕ × ℕ
x = 3 , 3 , 3
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

ml-type-eq-dec-b : (T1 T2 : ml-type) → (T1 ≡ T2) ⊎ (T1 ≢ T2)

ml-type-eq-dec-b ml-int ml-int = inj₁ refl
ml-type-eq-dec-b ml-char ml-char = inj₁ refl
ml-type-eq-dec-b (ml-list T1) (ml-list T2) = type-equal-list (ml-type-eq-dec-b T1 T2)
ml-type-eq-dec-b (ml-arrow T1 T2) (ml-arrow T3 T4) = type-equal-arrow (ml-type-eq-dec-b T1 T3 , ml-type-eq-dec-b T2 T4)
ml-type-eq-dec-b ml-int (ml-list T) = inj₂ (not-ml-int (ml-list T))
ml-type-eq-dec-b ml-int ml-char = inj₂ (not-ml-int ml-char)
ml-type-eq-dec-b ml-int (ml-arrow T1 T2) = inj₂ (not-ml-int (ml-arrow T1 T2))
ml-type-eq-dec-b (ml-list u) ml-int = inj₂ (not-ml-list ml-int)
ml-type-eq-dec-b (ml-list u) ml-char = inj₂ (not-ml-list ml-char)
ml-type-eq-dec-b (ml-list u) (ml-arrow T1 T2) = inj₂ (not-ml-list (ml-arrow T1 T2))
ml-type-eq-dec-b ml-char ml-int = inj₂ (not-ml-char ml-int)
ml-type-eq-dec-b ml-char (ml-list T) = inj₂ (not-ml-char (ml-list T))
ml-type-eq-dec-b ml-char (ml-arrow T1 T2) = inj₂ (not-ml-char (ml-arrow T1 T2))
ml-type-eq-dec-b (ml-arrow u v) ml-int = inj₂ (not-ml-arrow ml-int)
ml-type-eq-dec-b (ml-arrow u v) ml-char = inj₂ (not-ml-arrow ml-char)
ml-type-eq-dec-b (ml-arrow u v) (ml-list T) = inj₂ (not-ml-arrow (ml-list T))


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

interleaved mutual

  odd : ℕ → Bool
  even : ℕ → Bool

  odd 0 = false
  odd (suc n) = (even n)

  even 0 = true
  even (suc n) = (odd n)

t : Bool
t = even 2











{-case ml-type-eq-dec-b T1 T2 of λ {
                                                    (inj₁ a) → inj₁ (cong ml-list a)
                                                    ; (inj₂ b) → {!b ?!} }-}
 --int≢list : {A : ml-type} → ml-int ≢ (ml-list A)
--int≢list ()

--list≢int : {A : ml-type} → (ml-list A) ≢ ml-int
--list≢int ()

--int≢char : ml-int ≢ ml-char
--int≢char ()

--w : (T : ml-type) → (ml-int ≢ ml-list T)
--w T = not-ml-int (ml-list T)

--y : (ml-int ≡ ml-int) → ⊤
--y = not-ml-int ml-int

{- Trial to generalize over ml-int
 Won't probably work because I would need decidable equality to define g

g : (T : ml-type) → ml-type → Set
g T = ⊤
g _ = ⊥

not-this-type : (T : ml-type) (y : ml-type) → (T ≡ y) → (g T y)
not-this-type T y = eq-ind T (g T) tt y -}



--is-ml-int : (T : ml-type) → (T ≡ ml-int)
--is-ml-int ml-int p = {!!}
