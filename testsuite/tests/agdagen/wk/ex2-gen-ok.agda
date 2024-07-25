open import base

-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
-- Basic instantation of a GADT value
-- The code below was automatically generated with agdagen
-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

e1 : expr M ℤ
e1 = EApp (EApp EBinop (EInt (+ 5))) (EInt (+ 8))
