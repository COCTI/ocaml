open import Data.Nat using (ℕ; zero; suc; _∸_; _+_) renaming (_<ᵇ_ to _ℕ<?_; _≡ᵇ_ to _ℕ≡?_)
open import Data.Integer using (ℤ; 0ℤ; -_ ; +_; _-_; _*_) renaming (_<?_ to _ℤ<?_ ;  _≟_ to _ℤ≡?_)
open import Data.Integer.DivMod using (_%_ ; _/_)
open import Data.Float using (Float) renaming (_<ᵇ_ to _ℝ<?_ ; _≡ᵇ_ to _ℝ≡?_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.String renaming (_++_ to _cat_; length to Slength; _<?_ to _s<?_; _≈?_ to _s≡?_)
open import Data.Char using (toℕ; Char)
open import Data.Bool using (true; false; Bool; if_then_else_) renaming (_<?_ to _b<?_; _≟_ to _b≡?_)
open import Data.List using (List; _∷_; []; _++_; length)
open import Data.Unit using ( ⊤ ; tt)
open import Data.Empty
open import Data.Maybe using (just ; nothing; Maybe)
-- open import Agda.Builtin.Float
-- open import Agda.Builtin.Nat using (_<_)
open import Data.Product using (_×_ ; _,_; proj₁ ; proj₂; _,′_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable.Core using (_because_; isYes; Dec; yes; no)
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)
open import Agda.Primitive
open import Function.Base using (case_of_)
-- Utils for the file

--case_of_ : {l : Level} {A B : Set l} → A → (A → B) → B
--case x of f = f x

maxℕ : (p q : ℕ) → ℕ
maxℕ 0 q = q
maxℕ p 0 = p
maxℕ (suc u) (suc v) = 1 + maxℕ u v

size : {A : Set} → (List A) → ℕ
size [] = 0
size (x ∷ q) = 1 + size q

rcons : {A : Set} → List A → A → List A
rcons [] x = x ∷ []
rcons (y ∷ q) x = y ∷ (rcons q x)

nth-opt : {A : Set} → List A → ℕ → Maybe A
nth-opt [] _ = nothing
nth-opt (x ∷ q) 0 = just x
nth-opt (x ∷ q) (suc n) = nth-opt q n

nth : {A : Set} → A → List A → ℕ → A
nth x [] n = x
nth x (y ∷ s) zero = y
nth x (y ∷ s) (suc n) = nth x s n

ncons : {A : Set} → ℕ → A → List A
ncons zero x = []
ncons (suc n) x = x ∷ ncons n x

-- set_nth x0 s i y == s where item i has been changed to y;
-- if s does not have an item i, it is first padded with copies
-- of x0 to size i+1.
-- (https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html)
set-nth : {T : Set} → T → List T → ℕ → T → List T
set-nth x0 [] i y = (ncons i x0) ++ (y ∷ [])
set-nth x0 (x ∷ s) zero y = y ∷ s
set-nth x0 (x ∷ s) (suc i) y = x ∷ (set-nth x0 s i y)


{-(* Equality *)
Section eqtype.

  Variable T : Type.
  Variable eq_dec : comparable T.
  Definition compareb x y : bool := eq_dec x y.
  Definition comparePc x y :=
    match eq_dec x y as s return reflect (x = y) s with
    | left a => ReflectT (x = y) a
    | right b => ReflectF (x = y) b
    end.
  Definition eqPc (E : eqType) : Equality.axiom (@eq_op E) :=
    match E with EqType sort (EqMixin op a) => a end.

End eqtype.-}


data array_t (A : Set) : Set where
  ArrayVal : List A → array_t A {- array contents -}

-- Comparison

data comparator : Set where
  Eq : comparator
  Lt : comparator
  Gt : comparator

compare-int : (n1 n2 : ℕ) → comparator
compare-int n1 n2 = case (n1 ℕ<? n2) of λ {
                            true → Lt
                            ; false → case (n1 ℕ≡? n2) of λ {
                                           true → Eq
                                           ; _ → Gt } }

compare-bool : (b1 b2 : Bool) → comparator
compare-bool b1 b2 =
  case isYes (b1 b<? b2) of λ {
    true → Lt
    ; _ → case isYes (b1 b≡? b2) of λ {
      true → Eq
      ; _ → Gt }
 }

compare-ascii : (c1 c2 : Char) → comparator
compare-ascii c1 c2 = compare-int (toℕ c1) (toℕ c2)

compare-float : (f1 f2 : Float) → comparator
compare-float f1 f2 =
   case (f1 ℝ<? f2) of λ {
     true → Lt
     ; _ → case (f1 ℝ≡? f2) of λ {
            true → Eq
            ; _ → Gt } }

compare-integer : (n m : ℤ) → comparator
compare-integer n m =
  case isYes (n ℤ<? m) of λ {
    true → Lt
    ; _ → case isYes (m ℤ≡? n) of λ {
           true → Eq
            ; _ → Gt } }

compare-string : (s1 s2 : String) → comparator
compare-string s1 s2 = case isYes (s1 s<? s2) of λ {
                            true → Lt
                            ; false → case isYes (s1 s≡? s2) of λ {
                                           true → Eq
                                           ; _ → Gt } }

-- ErrorStateMonad
W0 : (Env Exn TY : Set) → Set
W0 Env Exn TY = ⊤ ⊎ ((Exn ⊎ TY) × Env)

M0 : (Env Ex TY : Set) → Set
M0 Env Exn TY = Env → W0 Env Exn TY


-- MTYPE
record ENV : Set₁ where
  field
    Env : Set
    Exn : Set

-- MFUNC
record EFmonad (EnvM : ENV) : Set₁ where
  open ENV EnvM

  W : (TY : Set) → Set
  W TY = W0 Env Exn TY

  M : (TY : Set) → Set
  M TY = Env → W TY

  Fail : {A : Set} → M A
  Fail env = inj₁ tt

  Raise : {A : Set} → (e : Exn) → M A
  Raise e env = inj₂ (inj₁ e , env)

  Ret : {A : Set} (x : A) → M A
  Ret x env = inj₂ (inj₂ x , env)

  Bind : {A B : Set} (x : M A) (f : A → M B) → M B
  Bind x f env = case (x env) of λ {
      (inj₂ (inj₂ a , env')) → f a env' ;
      (inj₂ (inj₁ e , env')) → inj₂ (inj₁ e , env') ;
      (inj₁ tt) → inj₁ tt }

  --infix -1 Bind _ _

  -- Could be necessary if I want to use a syntactic
  --   declaration to define '>>='
  Bind2 : {A B : Set} (x : M A) (f : A → M B) → M B
  Bind2 x f env = Bind x f env

  BindW : {A B : Set} (x : W A) (f : A -> M B) → W B
  BindW x f = case x of λ {
    (inj₂ (_ , env)) → Bind (λ _ → x) f env ;
    (inj₁ tt) → inj₁ tt }

--  Strict version
--  Restart : {A B : Set} (x : W A) (f : M B) → W B
--  Restart x f = BindW x (λ _ → f)

-- Allow to restart after exception
  Restart : {A B : Set} (x : W A) (f : M B) → W B
  Restart x f = case x of λ {
    (inj₂ (_ , env)) → f env ;
    _ → inj₁ tt }

  FromW : {A : Set} (x : W A) → M A
  FromW x = λ {env → case x of λ {
    (inj₂ (y , _)) → inj₂(y , env) ;
    _ → inj₁ tt } }

  _>>=_ : {A B : Set} (f : M A) (f : A → M B) → M B
  m >>= f = Bind m f

  -- Do_←_//_ : {A B : Set} (x : A) (m : M A) (e : M B) → M B
  -- Do x ← m // e = Bind m (λ x → e)

  -- syntax Bind2 m f = m >>= f
  infix -1 Bind
  syntax Bind m (λ x → e) = Do x ← m // e
  --infix -1 Do_←_//

  _>>_ : {A B : Set} (m : M A) (f : M B) → M B
  m >> f = Bind m (λ _ → f)

  Delay : {A : Set} (f : M A) → M A
  Delay f = (Ret tt >> f)

  App : {A B : Set} (f : M (A → M B)) (x : M A) → M B
  App f x = Do y ← x // Do g ← f // g y
  -- App f x = Bind x (λ y → Bind f (λ g → g y))


  AppM : {A B : Set} (f : M (A → M B)) (x : A) → M B
  AppM f x =  Do f ← f // f x


  AppM2 : {A B C : Set} (f : M (A → M (B → M C))) (x : A) (y : B) → M C
  AppM2 f x y = Do f ← f // Do f ← f x // f y


data loc-b (ml-type : Set) : ml-type → Set where
  mkloc : (T : ml-type) (n : ℕ) → loc-b ml-type T


-- Equality

record eqType (A : Set) : Set₁ where
  field
    eq-dec : DecidableEquality A
  compareb : (x y : A) → Bool
  compareb x y = case eq-dec x y of λ {
                      (true because _) → true
                      ; _ → false }
  comparePc = eq-dec

open eqType {{...}} public

eqPc : (A : Set) → {{eqA : eqType A}} → DecidableEquality A
eqPc A = eq-dec

eq-rect : {A : Set} → (x : A) → (P : A → Set) → P x → (y : A) → (x ≡ y) → P y
eq-rect x P u .x refl = u


-- MTYPE
record MLTY : Set₁ where
  field
    ml-type : Set
    {{ml-type-is-eq-dec}} : eqType ml-type
    ml-exn : ml-type
    coq-type-b : (Set → Set) → ml-type → Set


-- λ-lifting : potentially non-terminating definitions are outside the monad
-- so that the bypassing of positivity-check can also be outside the monad

record bind-ext (MLT : Set) (CT : (Set → Set) → MLT → Set) (M2 : Set → Set) : Set where
    inductive
    constructor mkbind
    field
      bind-type : MLT
      bind-val : CT M2 bind-type

interleaved mutual

  {-# NO_POSITIVITY_CHECK #-}
  data Env-ext {ml-type : Set} (binder : (Set → Set) → Set) (coq-type : (Set → Set) → ml-type → Set) (ml-exn : ml-type) : Set
  {-# NO_POSITIVITY_CHECK #-}
  data Exn-ext {ml-type : Set} (binder : (Set → Set) → Set) (coq-type : (Set → Set) → ml-type → Set) (ml-exn : ml-type) : Set

  data Env-ext binder coq-type ml-exn where
    mkEnv : List (binder (M0 (Env-ext binder coq-type ml-exn) (Exn-ext binder coq-type ml-exn))) → Env-ext binder coq-type ml-exn

  data Exn-ext binder coq-type ml-exn where
    GasExhausted : Exn-ext binder coq-type ml-exn
    BoundedNat : Exn-ext binder coq-type ml-exn
    Catchable : coq-type (M0 (Env-ext binder coq-type ml-exn) (Exn-ext binder coq-type ml-exn)) ml-exn → Exn-ext binder coq-type ml-exn


record REFmonad (MLtypes : MLTY) : Set₁ where
  open MLTY MLtypes

  binding = bind-ext ml-type coq-type-b

  Env2 = Env-ext binding coq-type-b ml-exn
  Exn2 = Exn-ext binding coq-type-b ml-exn

  -- MDEF
  EnvM : ENV
  EnvM = record {Env = Env2; Exn = Exn2}

  -- MAPP
  EFmonadENV : EFmonad EnvM
  EFmonadENV = record {}

  open EFmonad EFmonadENV public

  coq-type = coq-type-b M
  bindingM = binding M
  loc = loc-b ml-type

  loc-id : {T : ml-type} (l : loc T) → ℕ
  loc-id (mkloc x n) = n

  cnew : (T : ml-type) (v : coq-type T) → M (loc T)
  cnew T v st = case st of λ {
                  (mkEnv l) → inj₂ (inj₂ (mkloc T (size l)), mkEnv (rcons l (mkbind T v))) }

  coerce : (T1 T2 : ml-type) (v : coq-type T1) → Maybe (coq-type T2)
  coerce T1 T2 v = case (eqPc ml-type T1 T2) of λ {
                            (_because_ true (ofʸ x)) → just (eq-rect T1 coq-type v T2 x)
                            ; _ → nothing }

  cget : (T : ml-type) (r : loc T) → M (coq-type T)
  cget T r (mkEnv x) = case nth-opt x (loc-id r) of λ {
                         (just (mkbind T2 v)) → case coerce _ T v of λ {
                                                  (just u) → inj₂ (inj₂ u , mkEnv x)
                                                  ; _ → inj₁ tt }
                         ; _ → inj₁ tt }

  cput : (T : ml-type) (r : loc T) → (v : coq-type T) → M ⊤
  cput T r v (mkEnv x) =  let n : ℕ
                              n = loc-id r in
    case nth-opt x n of λ {
      (just (mkbind T2 _)) → (case coerce T T2 v of λ {
                               (just u) → let b : binding M
                                              b = mkbind T2 u in inj₂ (inj₂ tt , mkEnv (set-nth b x n b))
                               ; _ → inj₁ tt })
          ; _ → inj₁ tt }

  FailGas : {A : Set} → M A
  FailGas = Raise GasExhausted

  raise : (T : ml-type) (e : coq-type ml-exn) → M (coq-type T)
  raise T e = Raise (Catchable e)

  handle : (T : ml-type) (c : M (coq-type T)) (h : coq-type ml-exn → M (coq-type T)) → M (coq-type T)
  handle T c h env = case c env of λ {
                       (inj₂ (inj₁ (Catchable e) , env2)) → h e env2
                       ; r → r }

  -- Section Comparison
  lexi-compare : (cmp1 cmp2 : M comparator) → M comparator
  lexi-compare cmp1 cmp2 = Do x ← cmp1 // case x of λ {
                                            Eq → cmp2
                                            ; _ → Ret x }

  --variable
  --compare-rec : {T : ml-type} → coq-type T → coq-type T → M comparator

  compare-list : {compare-rec : {T : ml-type} → coq-type T → coq-type T → M comparator} → {T : ml-type} → (l1 l2 : List (coq-type T)) → M comparator
  compare-list [] [] = Ret Eq
  compare-list [] (x ∷ l2) = Ret Lt
  compare-list (x ∷ l1) [] = Ret Gt
  compare-list {compare-rec} (a1 ∷ t1) (a2 ∷ t2) = lexi-compare (compare-rec a1 a2) (Delay (compare-list {compare-rec} t1 t2))

  compare-ref : {compare-rec : {T : ml-type} → coq-type T → coq-type T → M comparator} → (T : ml-type) (r1 r2 : loc T) → M comparator
  compare-ref {compare-rec} T r1 r2 = Do x ← cget T r1 // Do y ← cget T r2 // compare-rec x y

  -- End Comparison

  iter : {A : Set} (n : ℕ) (f : A → A) (x : A) → A
  iter zero f x = x
  iter (suc m) f x = f (iter m f x)

  forloop : (n1 n2 : ℕ) (b : ℕ → M ⊤) → M ⊤
  forloop n1 n2 b = if (n2 Data.Nat.<ᵇ n1) then Ret tt else
    let g : M ℕ → M ℕ
        g m = Do i ← m // Do _ ← b i // Ret (i + 1) in
          (iter (n2 ∸ n1 + 1) g (Ret n1)) >> Ret tt

  downforloop : (n1 n2 : ℕ) (b : ℕ → M ⊤) → M ⊤
  downforloop n1 n2 b = if (n1 Data.Nat.<ᵇ n2) then Ret tt else
    let g : M ℕ → M ℕ
        g m = Do i ← m // Do _ ← b i // Ret (i ∸ 1) in
          (iter (n1 ∸ n2 + 1) g (Ret n1)) >> Ret tt

  whileloop : (h : ℕ) (f : M Bool) (b : M ⊤) → M ⊤
  whileloop zero f b = FailGas
  whileloop (suc h) f b = Do v ← f // (if v then (Do _ ← b // whileloop h f b) else Ret tt)

  cast-empty : (T : ml-type) (v : ⊥) → coq-type T
  cast-empty T ()

  cast-list : (T1 T2 : Set) → (T1 → T2) → List T1 → List T2
  cast-list T1 T2 = Data.List.map


K : {A B : Set} (x : A) (y : B) → A
K x y = x


-- For the proof that ml-type is an eqType

eq-ind : {A : Set} (x : A) (P : A → Set) (f : P x) (a : A) (e : x ≡ a) → P a
eq-ind x P f .x refl = f


record up3 (A B C : Set) : Set where
  constructor _,,_,,_
  field
    proj₁ : A
    proj₂ : B
    proj₃ : C

record up4 (A B C D : Set) : Set where
  constructor _,,,_,,,_,,,_
  field
    proj₁ : A
    proj₂ : B
    proj₃ : C
    proj₄ : D

record up5 (A B C D E : Set) : Set where
  constructor _,,,,_,,,,_,,,,_,,,,_
  field
    proj₁ : A
    proj₂ : B
    proj₃ : C
    proj₄ : D
    proj₅ : E

record up6 (A B C D E F : Set) : Set where
  constructor _,,,,,_,,,,,_,,,,,_,,,,,_,,,,,_
  field
    proj₁ : A
    proj₂ : B
    proj₃ : C
    proj₄ : D
    proj₅ : E
    proj₆ : F

open up3 public
open up4 public
open up5 public
open up6 public

variable
  A B C D E F : Set

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

