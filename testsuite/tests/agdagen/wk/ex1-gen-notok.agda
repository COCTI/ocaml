open import base

-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
--   Unification problem
--   Not sure using the tag will solve this because we need to unify something
-- with the result of coq-type
--   Maybe with the pragma {-# INJECTIVE_FOR_INFERENCE #-} once it is released:
-- https://agda.readthedocs.io/en/latest/language/pragmas.html#injective-for-inference-pragma
-- the pragma is in the doc of Agda 2.7. which has not been released yet
-- see ex1-hand-ok.agda for a version slightly modified that works
-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

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
      }
