From mathcomp Require Import all_ssreflect.
Require Import Int63 BinNums Ascii String ZArith.

(* failStateMonad *)
Definition M0 Env T := Env -> option (Env * T).

Module Type ENV.
Parameter Env : Type.
End ENV.

Module EFmonad (Env : ENV).
Import Env.

Definition M := M0 Env.
Definition Res T := option (Env * T).

Definition Fail {A} : M A := fun _ => None.

Definition Ret {A} (x : A) : M A :=
  fun env => Some (env, x).

Definition Bind {A B} (x : M A) (f : A -> M B) : M B := fun env =>
  match x env with
  | None => None
  | Some (env, a) => f a env
  end.

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
End MLTY.

Module REFmonad(MLtypes : MLTY).
Import MLtypes.

Record binding (M : Type -> Type) :=
  mkbind { bind_key : key; bind_val : coq_type M (key_type bind_key) }.
Arguments mkbind {M}.

#[bypass_check(positivity)]
Inductive Env := mkEnv : int -> seq (binding (M0 Env)) -> Env.

Module Env. Definition Env := Env. End Env.
Module EFmonadEnv := EFmonad(Env).
Export EFmonadEnv.

Section monadic_operations.
Let coq_type := coq_type M.
Let binding := binding M.

Definition newref (T : ml_type) (val : coq_type T) : M (loc T) :=
  fun env =>
    let: mkEnv c refs := env in
    let key := mkkey c T in
    Some (mkEnv (succ c) (mkbind key val :: refs), mkloc key).

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
  | None => None
  | Some x => Some (env, x)
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
  in Option.bind (fun refs' => Some (mkEnv c refs', tt))
                 (update b refs).

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
  | Zneg _ => Fail
  end.

Definition bounded_nat_of_int (m : nat) (n : int) : M nat :=
  do n <- nat_of_int n;
  if n < m then Ret n else Fail.

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
