open import base

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
    }
