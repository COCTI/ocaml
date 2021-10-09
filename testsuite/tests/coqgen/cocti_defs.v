From mathcomp Require Import all_ssreflect.
Require Import Int63 BinNums Ascii String ZArith.

(* Extra predefined types *)
Inductive empty :=. (* for the value restriction *)
Inductive array_t T := ArrayVal (_ : list T). (* array contents *)

(* ErrorStateMonad *)
Definition W0 Env Exn T : Type := Env * (T + Exn).
Definition M0 Env Exn T := Env -> W0 Env Exn T.

Module Type ENV.
Parameter Env : Type.
Parameter Exn : Type.
End ENV.

Module EFmonad (Env : ENV).
Import Env.

Definition W T := W0 Env Exn T.
Definition M T := Env -> W T.

Definition Fail {A} (e : Exn) : M A := fun env => (env, inr e).

Definition Ret {A} (x : A) : M A := fun env => (env, inl x).

Definition Bind {A B} (x : M A) (f : A -> M B) : M B := fun env =>
  match x env with
  | (env', inl a) => f a env'
  | (env', inr e) => (env', inr e)
  end.

Definition BindW {A B} (x : W A) (f : A -> M B) : W B :=
  Bind (fun _ => x) f (fst x).  (* (fst x) could be anything *)

Definition Restart {A B} (x : W A) (f : M B) : W B :=
  BindW x (fun _ => f).

Definition RunW {A} (x : W A) : A + Exn := snd x.

Definition FromW {A} (x : W A) : M A := fun env => (env, RunW x).

Declare Scope do_notation.
Declare Scope monae_scope.
Delimit Scope monae_scope with monae.
Delimit Scope do_notation with Do.

Notation "m >>= f" := (Bind m f) (at level 49).
Notation "'do' x <- m ; e" := (Bind m (fun x => e))
  (at level 60, x name, m at level 200, e at level 60).
Notation "'do' x : T <- m ; e" := (Bind m (fun x : T => e))
  (at level 60, x name, m at level 200, e at level 60).
Notation "m >> f" := (Bind m (fun _ => f)).
Notation "'Delay' f" := (Ret tt >> f) (at level 200).

Definition App {A B} (f : M (A -> M B)) (x : M A) := do x <- x; do f <- f; f x.
Definition AppM {A B} (f : M (A -> M B)) (x : A) := do f <- f; f x.
Definition AppM2 {A B C} (f : M (A -> M (B -> M C))) (x : A) (y : B) :=
  do f <- f; do f <- f x; f y.
End EFmonad.

Module Type MLTY.
Parameter ml_type : Set.
Parameter ml_type_eq_dec : forall x y : ml_type, {x=y}+{x<>y}.
Record key := mkkey {key_id : int; key_type : ml_type}.
Variant loc : ml_type -> Type :=
  mkloc : forall k : key, loc (key_type k).
Parameter coq_type : forall M : Type -> Type, ml_type -> Type.
Parameter ml_exns : Type.
End MLTY.

Module REFmonad(MLtypes : MLTY).
Import MLtypes.

Inductive Exn :=
  | GasExhausted
  | RefLookup
  | BoundedNat
  | Catchable of ml_exns.

Record binding (M : Type -> Type) :=
  mkbind { bind_key : key; bind_val : coq_type M (key_type bind_key) }.
Arguments mkbind {M}.

#[bypass_check(positivity)]
Inductive Env := mkEnv : int -> seq (binding (M0 Env Exn)) -> Env.

Module Env. Definition Env := Env. Definition Exn := Exn. End Env.
Module EFmonadEnv := EFmonad(Env).
Export EFmonadEnv.

Definition FailGas {A} : M A := fun env => (env, inr GasExhausted).

Section monadic_operations.
Let coq_type := coq_type M.
Let binding := binding M.

Definition newref (T : ml_type) (val : coq_type T) : M (loc T) :=
  fun env =>
    let: mkEnv c refs := env in
    let key := mkkey c T in
    Ret (mkloc key) (mkEnv (succ c) (mkbind key val :: refs)).

Definition coerce (T1 T2 : ml_type) (v : coq_type T1) : option (coq_type T2) :=
  match ml_type_eq_dec T1 T2 with
  | left H => Some (eq_rect _ _ v _ H)
  | right _ => None
  end.

Fixpoint lookup key env :=
  match env with
  | nil => None
  | mkbind k v :: rest =>
    if Int63.eqb (key_id key) (key_id k) then
      coerce (key_type k) (key_type key) v
    else lookup key rest
  end.

Definition getref T (l : loc T) : M (coq_type T) := fun env =>
  let: mkloc key := l in
  let: mkEnv _ refs := env in
  match lookup key refs with
  | None => Fail RefLookup env
  | Some x => Ret x env
  end.

Fixpoint update b (env : seq binding) :=
  match env with
  | nil => None
  | mkbind k v :: rest =>
    let: mkbind k' _ := b in
    if Int63.eqb (key_id k') (key_id k) then
      if ml_type_eq_dec (key_type k') (key_type k)
      then Some (b :: rest)
      else None
    else
      Option.map (cons (mkbind k v)) (update b rest)
  end.

Definition setref T (l : loc T) (val : coq_type T) : M unit := fun env =>
  let: mkEnv c refs := env in
  let b :=
      match l in loc T return coq_type T -> binding with
        mkloc key => mkbind key
      end val
  in
  match update b refs with
  | None => Fail RefLookup env
  | Some refs' => Ret tt (mkEnv c refs')
  end.

Definition raise T (e : ml_exns) : M (coq_type T) :=
  Fail (Catchable e).

Definition handle T (c : M (coq_type T))
           (h : ml_exns -> M (coq_type T)) : M (coq_type T) :=
  fun env =>
    match c env with
    | (env', inr (Catchable e)) => h e env'
    | (env', r) => (env', r)
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
  do x <- getref T r1; do y <- getref T r2; compare_rec T x y.
End Comparison.

Definition nat_of_int (n : int) : M nat :=
  match to_Z n with
  | Z0 => Ret 0
  | Zpos pos => Ret (Pos.to_nat pos)
  | Zneg _ => Fail BoundedNat
  end.

Definition bounded_nat_of_int (m : nat) (n : int) : M nat :=
  do n <- nat_of_int n;
  if n < m then Ret n else Fail BoundedNat.

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
End Comparison.

Section Helpers.
Definition K {A B} (x : A) (y : B) := x.
End Helpers.
