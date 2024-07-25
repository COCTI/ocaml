open import base

data EXPR : Set → Set₁ where
    EBinop : EXPR (ℤ → M (ℤ → M ℤ))
    EApp : {a-1 : Set} → {b : Set} → (EXPR (a-1 → M b)) → (EXPR a-1) → EXPR b
    EInt : (ℤ) → EXPR ℤ
    EBool : (Bool) → EXPR Bool
