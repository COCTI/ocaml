From mathcomp Require Import all_ssreflect.
Require Import Sint63 BinNums Ascii String ZArith Floats.

(* Extra predefined types *)
Inductive empty :=. (* for the value restriction *)
Inductive array_t T := ArrayVal (_ : list T). (* array contents *)

(* ErrorStateMonad *)
Definition W0 Env Exn T : Type := Env * (T + Exn).
Definition M0 Env Exn (P : Env -> Env -> bool) T :=
  {f : Env -> W0 Env Exn T | forall env, P env (f env).1}.
Module Type ENV.
Parameter Env : Type.
Parameter Exn : Type.
Parameter env_incl : Env -> Env -> bool.
Parameter env_incl_refl : reflexive env_incl.
Parameter env_incl_trans : transitive env_incl.
End ENV.

Module EFmonad (Env : ENV).
Import Env.

Definition W T := W0 Env Exn T.
Definition M T := {f : Env -> W T | forall env, env_incl env (f env).1}.

Definition Fail {A} (e : Exn) : M A :=
  exist _ (fun env => (env, inr e)) env_incl_refl.

Definition Ret {A} (x : A) : M A :=
  exist _ (fun env => (env, inl x)) env_incl_refl.

Definition BindW {A B} (x : W A) (f : A -> M B) : W B :=
  match x with
  | (env', inl a) => sval (f a) env'
  | (env', inr e) => (env', inr e)
  end.

Definition Bind {A B} (x : M A) (f : A -> M B) : M B.
refine (let: exist g ee' := x in _).
exists (fun env => BindW (g env) f).
abstract
  (move=> env;
   apply (env_incl_trans _ _ _ (ee' env));
   case: (g env) => env' [] a /=; by [case: (f a) | apply env_incl_refl]).
Defined.

(* Strict version
Definition Restart {A B} (x : W A) (f : M B) : W B := BindW x (fun _ => f).
*)

(* Allow to restart after exception *)
Definition Restart {A B} (x : W A) (f : M B) : W B := sval f (fst x).

Definition RunW {A} (x : W A) : A + Exn := snd x.

Definition FromW {A} (x : W A) : M A :=
  exist _ (fun env => (env, RunW x)) env_incl_refl.

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
Parameter ml_exn : ml_type.
Record key := mkkey {key_id : nat; key_type : ml_type}.
Variant loc : ml_type -> Type :=
  mkloc : forall k : key, loc (key_type k).
Parameter coq_type : forall M : Type -> Type, ml_type -> Type.
End MLTY.

Module REFmonad(MLtypes : MLTY).
Import MLtypes.

(*
Inductive Exn :=
  | GasExhausted
  | RefLookup
  | BoundedNat
  | Catchable of ml_exns.
*)

Record binding (M : Type -> Type) :=
  mkbind { bind_key : key; bind_val : coq_type M (key_type bind_key) }.
Arguments mkbind {M}.

Definition uniq_bindings M env :=
 forall c, count (fun b => key_id (bind_key M b) =? c) env <= 1.

Definition envok M keys c refs :=
  map (bind_key M) refs = keys /\ uniq_bindings M refs /\
  all (fun b => key_id (bind_key M b) < c) refs.

Definition key_eqb (k1 k2 : key) :=
  (key_id k1 =? key_id k2) &&
  (ml_type_eq_dec (key_type k1) (key_type k2)).

Lemma eq_keyP : Equality.axiom key_eqb.
Proof.
rewrite /key_eqb => -[] n1 T1 [] n2 T2 /=.
apply: (iffP idP) => /=.
- case/andP => /Nat.eqb_spec <-.
  by case: ml_type_eq_dec => // H _; rewrite H.
- move=> [] <- <-.
  apply/andP. apply conj. by apply/Nat.eqb_spec.
  by case: ml_type_eq_dec.
Qed.

Definition eq_key_mixin := EqMixin eq_keyP.
Canonical key_eqType := Eval hnf in EqType _ eq_key_mixin.

Definition mem_bindings M k :=
  has (fun b => bind_key M b == k).

Definition incl_bindings (k1 k2 : seq key) : bool :=
  all (fun k => k \in k2) k1.

Definition incl_env {Env : seq key -> Type} (env1 env2 : sigT Env) :=
  incl_bindings (projT1 env1) (projT1 env2).

#[bypass_check(positivity)]
Inductive Env : seq key -> Type :=
  mkEnv keys (c : nat) (refs : seq (binding (M0 (sigT Env) Exn incl_env)))
    : envok _ keys c refs -> Env keys
with Exn :=
  | GasExhausted
  | RefLookup
  | BoundedNat
  | Catchable of coq_type (M0 (sigT Env) Exn incl_env) ml_exn.

Definition env_bindings (env : sigT Env) :=
  let: mkEnv _ _ refs _ := projT2 env in refs.

(*
Definition mem_env k env := mem_bindings _ k (env_bindings env).

Definition env_incl (env env' : sigT Env) :=
  forall k, mem_env k env -> mem_env k env'.
*)

Definition env_incl (e1 e2 : sigT Env) := incl_bindings (projT1 e1) (projT1 e2).
Lemma env_incl_refl : reflexive env_incl.
Proof. rewrite /env_incl /incl_bindings => x. by apply/allP. Qed.
Lemma env_incl_trans : transitive env_incl.
Proof.
rewrite /env_incl /incl_bindings => x y z /allP xy /allP yz.
by apply/allP => k /xy /yz.
Qed.

Module Env.
Definition Env := sigT Env.
Definition Exn := Exn.
Definition env_incl := env_incl.
Definition env_incl_refl := env_incl_refl.
Definition env_incl_trans := env_incl_trans.
End Env.
Module EFmonadEnv := EFmonad(Env).
Export EFmonadEnv.

Section monadic_operations.
Let coq_type := coq_type M.
Let binding := binding M.

Lemma newref_envok {T} (val : coq_type T) keys n refs :
  envok M keys n refs ->
  envok M (mkkey n T :: keys) (n + 1) (mkbind (mkkey n T) val :: refs).
Proof.
  rewrite /envok => -[] Hkeys [] Huniq Hltn.
  split => /=.
  - by rewrite Hkeys.
  split.
  - rewrite /uniq_bindings /= => c.
    case Hnc : (n =? c) => //=.
    + move/eqP : Hnc => <-.
      rewrite ltnS.
      move:Hltn.
      rewrite all_count; move/eqP.
      rewrite -(count_predC (fun b : binding => key_id (bind_key M b) < n)).
      rewrite -[LHS]addn0; move/eqP; rewrite eqn_add2l; move/eqP.
      under eq_count => b /=.
        rewrite -leqNgt.
      over.
      move=> ->.
      apply sub_count.
      rewrite /subpred => b.
      move/eqP /esym.
      by apply eq_leq.
    + by apply Huniq.
  - rewrite addn1.
    apply/andP; split => //.
    move:Hltn.
    apply sub_all.
    rewrite /subpred => b H.
    by apply (@ltn_trans n).
Qed.

Definition exEnv {keys} (env : Env keys) : sigT Env := existT _ keys env.
Definition mkEnv' {keys c refs} (prf : envok _ keys c refs) :=
  exEnv (mkEnv _ _ _ prf).

Definition newref (T : ml_type) (val : coq_type T) : M (loc T).
exists
  (fun env =>
    let: existT _ (mkEnv keys c refs prf) := env in
    let key := mkkey c T in
    (mkEnv' (newref_envok val keys c refs prf), inl (mkloc key))).
abstract (case => _ [] keys c /= refs prf;
          apply/allP => k /=; by rewrite in_cons orbC => ->).
Defined.

Definition coerce (T1 T2 : ml_type) (v : coq_type T1) : option (coq_type T2) :=
  match ml_type_eq_dec T1 T2 with
  | left H => Some (eq_rect _ _ v _ H)
  | right _ => None
  end.

Fixpoint lookup key env :=
  match env with
  | nil => None
  | mkbind k v :: rest =>
    if Nat.eqb (key_id key) (key_id k) then
      coerce (key_type k) (key_type key) v
    else lookup key rest
  end.

Definition getref T (l : loc T) : M (coq_type T).
exists
  (fun env =>
  let: mkloc key := l in
  match lookup key (env_bindings env) with
  | None => (env, inr RefLookup)
  | Some x => (env, inl x)
  end).
abstract (case: l => k env; by case: lookup => *; apply env_incl_refl).
Defined.

Fixpoint update b (env : seq binding) :=
  match env with
  | nil => None
  | mkbind k v :: rest =>
    let: mkbind k' _ := b in
    if Nat.eqb (key_id k') (key_id k) then
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

Definition FailGas {A} : M A := Fail GasExhausted.

Definition raise T (e : coq_type ml_exn) : M (coq_type T) :=
  Fail (Catchable e).

Definition handle T (c : M (coq_type T))
           (h : coq_type ml_exn -> M (coq_type T)) : M (coq_type T) :=
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

Fixpoint forloop (h : nat) (n_1 n_2 : int) (b : int -> M unit) : M unit :=
  if h is h.+1 then
    if ltsb n_2 n_1 then Ret tt
    else (do _ <- b n_1; forloop h (n_1 + 1)%sint63 n_2 b)
  else FailGas.

Fixpoint downforloop (h : nat) (n_1 n_2 : int ) (b : int -> M unit) : M unit :=
  if h is h.+1 then
    if ltsb n_1 n_2 then Ret tt
    else (do _ <- b n_1; downforloop h (n_1 - 1)%sint63 n_2 b)
  else FailGas.

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
