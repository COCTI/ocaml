From mathcomp Require Import all_ssreflect.
Require Sint63.
Require Import PrimInt63 BinNums Ascii String ZArith Floats.
#[global] Arguments eqVneq {T} x y.

(* Equality *)
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
End eqtype.

(* Extra predefined types *)
Inductive empty :=. (* for the value restriction *)
Inductive array_t T := ArrayVal (_ : list T). (* array contents *)

(* ErrorStateMonad *)
Definition W0 Env Exn T : Type := unit + ((Exn + T) * Env).
Definition M0 Env Exn T := Env -> W0 Env Exn T.

Module Type ENV.
Parameter Env : Type.
Parameter Exn : Type.
End ENV.

Module EFmonad (Env : ENV).
Import Env.

Definition W T := W0 Env Exn T.
Definition M T := Env -> W T.

Definition Fail {A} : M A := fun env => inl tt.
Definition Raise {A} (e : Exn) : M A := fun env => inr (inl e, env).
Definition Ret {A} (x : A) : M A := fun env => inr (inr x, env).

Definition Bind {A B} (x : M A) (f : A -> M B) : M B := fun env =>
  match x env with
  | inr (inr a, env') => f a env'
  | inr (inl e, env') => inr (inl e, env')
  | inl tt => inl tt
  end.

Definition BindW {A B} (x : W A) (f : A -> M B) : W B :=
  if x is inr (_,env) then Bind (fun _ => x) f env else inl tt.

(* Strict version
Definition Restart {A B} (x : W A) (f : M B) : W B := BindW x (fun _ => f).
*)

(* Allow to restart after exception *)
Definition Restart {A B} (x : W A) (f : M B) : W B :=
  if x is inr (_,env) then f env else inl tt.

(* Definition RunW {A} (x : W A) : A + Exn := snd x. *)

Definition FromW {A} (x : W A) : M A :=
  fun env => if x is inr (y,_) then inr (y,env) else inl tt.

Declare Scope do_notation.
Declare Scope monae_scope.
Delimit Scope monae_scope with monae.
Delimit Scope do_notation with Do.

Notation "m >>= f" := (Bind m f) (at level 49).
Notation "'do' x <- m ; e" := (Bind m (fun x => e))
  (at level 60, x name, m at level 200, e at level 60).
Notation "'do' x : T <- m ; e" := (Bind m (fun x : T => e))
  (at level 60, x name, m at level 200, e at level 60).
Notation "m >> f" := (Bind m (fun _ => f)) (at level 49).
Notation "'Delay' f" := (Ret tt >> f) (at level 200).

Definition App {A B} (f : M (A -> M B)) (x : M A) := do x <- x; do f <- f; f x.
Definition AppM {A B} (f : M (A -> M B)) (x : A) := do f <- f; f x.
Definition AppM2 {A B C} (f : M (A -> M (B -> M C))) (x : A) (y : B) :=
  do f <- f; do f <- f x; f y.
End EFmonad.

Variant loc ml_type : ml_type -> Type := mkloc T : nat -> loc ml_type T.

Module Type MLTY.
Parameter ml_type : eqType.
Parameter ml_exn : ml_type.
Parameter coq_type : forall M : Type -> Type, ml_type -> Type.
End MLTY.

Module REFmonad(MLtypes : MLTY).
Import MLtypes.

Record binding (M : Type -> Type) :=
  mkbind { bind_type : ml_type; bind_val : coq_type M bind_type }.
Arguments mkbind {M}.

#[bypass_check(positivity)]
Inductive Env := mkEnv : seq (binding (M0 Env Exn)) -> Env
with Exn :=
  | GasExhausted
  | BoundedNat
  | Catchable of coq_type (M0 Env Exn) ml_exn.

Module Env. Definition Env := Env. Definition Exn := Exn. End Env.
Module EFmonadEnv := EFmonad(Env).
Export EFmonadEnv.

Section monadic_operations.
Let coq_type := coq_type M.
Let binding := binding M.
Let loc := @loc ml_type.
Definition loc_id {T} (l : loc T) := let: mkloc _ n := l in n.
Let mkloc := @mkloc ml_type.

Definition cnew T (v : coq_type T) : M (loc T) :=
  fun st =>
    let: mkEnv st := st in
    let n := size st in
    inr (inr (mkloc T n), mkEnv (rcons st (mkbind T (v : coq_type T)))).

Definition coerce T1 T2 (v : coq_type T1) : option (coq_type T2) :=
  match eqPc _ T1 T2 with
  | ReflectT H => Some (eq_rect _ _ v _ H)
  |  _ => None
  end.

Local Notation nth_error := List.nth_error.

Definition cget T (r : loc T) : M (coq_type T) :=
  fun st =>
    let: mkEnv bs := st in
    if nth_error bs (loc_id r) is Some (mkbind T' v) then
      if coerce _ T v is Some u then inr (inr u, st) else inl tt
    else inl tt.

Definition cput T (r : loc T) (v : coq_type T) : M unit :=
  fun st =>
    let: mkEnv st := st in
    let n := loc_id r in
    if nth_error st n is Some (mkbind T' _) then
      if coerce _ T' v is Some u then
        let b := mkbind T' (u : coq_type _) in
        inr (inr tt, mkEnv (set_nth b st n b))
      else inl tt
    else inl tt.

Definition FailGas {A} : M A := Raise GasExhausted.

Definition raise T (e : coq_type ml_exn) : M (coq_type T) :=
  Raise (Catchable e).

Definition handle T (c : M (coq_type T))
           (h : coq_type ml_exn -> M (coq_type T)) : M (coq_type T) :=
  fun env =>
    match c env with
    | inr (inl (Catchable e), env') => h e env'
    | r => r
    end.

Section Comparison.
Definition lexi_compare (cmp1 cmp2 : M comparison) :=
  do x <- cmp1; match x with Eq => cmp2 | _ => Ret x end.

Variable compare_rec : forall T, coq_type T -> coq_type T -> M comparison.

Fixpoint compare_list T (l1 l2 : list (coq_type T)) : M comparison :=
  match l1, l2 with
  | nil, nil => Ret Eq
  | nil, _   => Ret Lt
  | _  , nil => Ret Gt
  | a1 :: t1, a2 :: t2 =>
    lexi_compare (compare_rec T a1 a2) (Delay (compare_list T t1 t2))
  end.

Variable T : ml_type.

Definition compare_ref T (r1 r2 : loc T) :=
  do x <- cget T r1; do y <- cget T r2; compare_rec T x y.
End Comparison.

Definition nat_of_int (n : int) : M nat :=
  match Sint63.to_Z n with
  | Z0 => Ret 0
  | Zpos pos => Ret (Pos.to_nat pos)
  | Zneg _ => Raise BoundedNat
  end.

Definition bounded_nat_of_int (m : nat) (n : int) : M nat :=
  do n <- nat_of_int n;
  if n < m then Ret n else Raise BoundedNat.

Definition uint2N (n : int) : nat :=
  if Uint63.to_Z n is Zpos pos then Pos.to_nat pos else 0.

Definition forloop (n_1 n_2 : int) (b : int -> M unit) : M unit :=
  if Sint63.ltb n_2 n_1 then Ret tt else
  ssrnat.iter (uint2N (PrimInt63.sub n_2 n_1)).+1
    (fun (m : M int) => do i <- m; do _ <- b i; Ret (Uint63.succ i))
    (Ret n_1) >> Ret tt.

Fixpoint downforloop (h : nat) (n_1 n_2 : int ) (b : int -> M unit) : M unit :=
  if Sint63.ltb n_1 n_2 then Ret tt else
  ssrnat.iter (uint2N (PrimInt63.sub n_1 n_2)).+1
    (fun (m : M int) => do i <- m; do _ <- b i; Ret (Uint63.pred i))
    (Ret n_1) >> Ret tt.

Fixpoint whileloop (h : nat) (f : M bool) (b : M unit) : M unit :=
  if h is h.+1 then
    do v <- f;
    if v then
        (do _ <- b; whileloop h f b)
    else Ret tt
  else FailGas.

(* Subtyping for encoding the relaxed value restriction *)
Definition cast_empty T (v : empty) : coq_type T :=
  match v with end.

Definition cast_list {T1} {T2} := @map T1 T2.

End monadic_operations.
End REFmonad.

Section Comparison.
Definition compare_ascii (c d : ascii) :=
  BinNat.N.compare (N_of_ascii c) (N_of_ascii d).

Fixpoint compare_string (s1 s2 : string) :=
  match s1, s2 with
  | EmptyString, EmptyString => Eq
  | EmptyString, _ => Lt
  | _, EmptyString => Gt
  | String c1 s1, String c2 s2 =>
    match compare_ascii c1 c2 with
    | Eq => compare_string s1 s2
    | cmp => cmp
    end
  end.

Definition compare_float (x1 x2 : float) :=
  match compare x1 x2 with 
  | FEq | FNotComparable => Eq
  | FLt => Lt
  | FGt => Gt
  end.
End Comparison.

Section Helpers.
Definition K {A B} (x : A) (y : B) := x.
End Helpers.
