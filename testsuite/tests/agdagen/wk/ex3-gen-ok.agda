open import base

-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
--   The traduction of a type declaration with a GADT constructor and a non-GADT
-- constructor
--   The code below was automatically generated with agdagen
-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

data Q : Set → Set₁ where
    Q1 : {a : Set} → (a) → Q a
    Q2 : {b : Set} → {c : Set} → {a-1 : Set} → (b) → (a-1) → (c) → Q a-1
