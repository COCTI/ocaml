From mathcomp Require Import ssreflect ssrnat eqtype seq.
Require Import PrimInt63 Ascii String Floats coqgen_defs.

(* Generated representation of all ML types *)
Inductive ml_type :=
  | ml_int
  | ml_char
  | ml_float
  | ml_bool
  | ml_unit
  | ml_exn
  | ml_array (_ : ml_type)
  | ml_list (_ : ml_type)
  | ml_lazy (_ : ml_type)
  | ml_string
  | ml_empty
  | ml_array_t (_ : ml_type)
  | ml_rlist (_ : ml_type)
  | ml_lazy_val (_ : ml_type)
  | ml_ref (_ : ml_type)
  | ml_arrow (_ : ml_type) (_ : ml_type).

(* Module argument for monadic functor *)
Module MLtypes.
Definition ml_type_eq_dec (T1 T2 : ml_type) : {T1=T2}+{T1<>T2}.
revert T2; induction T1; destruct T2;
  try (right; intro; discriminate); try (now left);
  try (case (IHT1_5 T2_5); [|right; injection; intros; contradiction]);
  try (case (IHT1_4 T2_4); [|right; injection; intros; contradiction]);
  try (case (IHT1_3 T2_3); [|right; injection; intros; contradiction]);
  try (case (IHT1_2 T2_2); [|right; injection; intros; contradiction]);
  (case (IHT1 T2) || case (IHT1_1 T2_1)); try (left; now subst);
    right; injection; intros; contradiction.
Defined.

Definition ml_type_eq_mixin := EqMixin (comparePc _ ml_type_eq_dec).
Canonical ml_type_eqType := Eval hnf in EqType _ ml_type_eq_mixin.

Local Definition ml_type := ml_type_eqType.
Local Notation loc := (@loc ml_type).

Section with_monad.
Context [M : Type -> Type].

(* Generated type definitions *)
Inductive ml_exns :=
  | Invalid_argument (_ : string)
  | Failure (_ : string)
  | Not_found.

Inductive rlist (a : Type) (a_1 : ml_type) :=
  | Nil
  | Cons (_ : a) (_ : loc (ml_rlist a_1)).


Inductive lazy_val (a : Type) :=
  LzVal of a | LzThunk of M a | LzExn of ml_exns.
Inductive lazy_t a a1 := Lval of a | Lref of (loc (ml_lazy_val a1)).

Local (* Generated type translation function *)
Fixpoint coq_type (T : ml_type) : Type :=
  match T with
  | ml_int => PrimInt63.int
  | ml_char => Ascii.ascii
  | ml_float => float
  | ml_bool => bool
  | ml_unit => unit
  | ml_exn => ml_exns
  | ml_array T1 => loc (ml_array_t T1)
  | ml_list T1 => list (coq_type T1)
  | ml_lazy T1 => lazy_t (coq_type T1) T1
  | ml_string => String.string
  | ml_empty => empty
  | ml_array_t T1 => array_t (coq_type T1)
  | ml_rlist T1 => rlist (coq_type T1) T1
  | ml_lazy_val T1 => lazy_val (coq_type T1)
  | ml_ref T1 => loc T1
  | ml_arrow T1 T2 => coq_type T1 -> M (coq_type T2)
  end.

End with_monad.
Local Definition ml_exn := ml_exn.
End MLtypes.
Export MLtypes.

Module REFmonadML := REFmonad (MLtypes).
Export REFmonadML.

Definition coq_type := @MLtypes.coq_type M.
Definition empty_env := mkEnv nil.
Definition it : W unit := inr (inr tt, empty_env).

(* Generated comparison function *)
Fixpoint compare_rec (h : nat) (T : ml_type)
  : coq_type T -> coq_type T -> M comparison :=
  if h is h.+1 then
    let compare_rec := compare_rec h in
    match T as T return coq_type T -> coq_type T -> M comparison with
    | ml_int => fun x y => Ret (Sint63.compare x y)
    | ml_char => fun x y => Ret (compare_ascii x y)
    | ml_float => fun x y => Ret (compare_float x y)
    | ml_bool => fun x y => Ret (Bool.compare x y)
    | ml_unit => fun x y => Ret Eq
    | ml_exn =>
      fun x y =>
        match x, y with
        | Not_found, Not_found => Ret Eq
        | Invalid_argument x1, Invalid_argument y1 =>
          compare_rec ml_string x1 y1
        | Failure x1, Failure y1 => compare_rec ml_string x1 y1
        | Not_found, _ => Ret Lt
        | _, Not_found => Ret Gt
        | Invalid_argument _, _ => Ret Lt
        | _, Invalid_argument _ => Ret Gt
        end
    | ml_array T1 => fun x y => compare_ref compare_rec (ml_array_t T1) x y
    | ml_list T1 => fun x y => compare_list compare_rec T1 x y
    | ml_lazy T1 =>
      fun x y => Raise (Catchable (Invalid_argument "compare"%string))
    | ml_string => fun x y => Ret (compare_string x y)
    | ml_empty => fun x y => match x with end
    | ml_array_t T1 =>
      fun x y =>
        match x, y with
        | ArrayVal x1, ArrayVal y1 => compare_rec (ml_list T1) x1 y1
        end
    | ml_rlist T1 =>
      fun x y =>
        match x, y with
        | Nil, Nil => Ret Eq
        | Cons x1 x2, Cons y1 y2 =>
          lexi_compare (compare_rec T1 x1 y1)
            (Delay (compare_rec (ml_ref (ml_rlist T1)) x2 y2))
        | Nil, _ => Ret Lt
        | _, Nil => Ret Gt
        end
    | ml_lazy_val T1 =>
      fun x y => Raise (Catchable (Invalid_argument "compare"%string))
    | ml_ref T1 => fun x y => compare_ref compare_rec T1 x y
    | ml_arrow T1 T2 =>
      fun x y => Raise (Catchable (Invalid_argument "compare"%string))
    end
  else fun _ _ => FailGas.

Definition ml_compare := compare_rec.

Definition wrap_compare wrap T h x y : M bool :=
  do c <- compare_rec T h x y; Ret (wrap c).

Definition ml_eq := wrap_compare (fun c => if c is Eq then true else false).
Definition ml_lt := wrap_compare (fun c => if c is Lt then true else false).
Definition ml_gt := wrap_compare (fun c => if c is Gt then true else false).
Definition ml_ne := wrap_compare (fun c => if c is Eq then false else true).
Definition ml_ge := wrap_compare (fun c => if c is Lt then false else true).
Definition ml_le := wrap_compare (fun c => if c is Gt then false else true).

(* Array operations *)
Definition newarray T len (x : coq_type T) :=
  do len <- nat_of_int len; cnew (ml_array_t T) (ArrayVal _ (nseq len x)).
Definition getarray T (a : coq_type (ml_array T)) n : M (coq_type T) :=
  do s <- cget (ml_array_t T) a;
  let: ArrayVal s := s in
  do n <- bounded_nat_of_int (seq.size s) n;
  if s is x :: _ then Ret (nth x s n) else
  raise _ (Invalid_argument "getarray").
Definition setarray T (a : coq_type (ml_array T)) n (x : coq_type T) :=
  do s <- cget (ml_array_t T) a;
  let: ArrayVal s := s in
  do n <- bounded_nat_of_int (seq.size s) n;
  cput (ml_array_t T) a (ArrayVal _ (set_nth x s n x)).

(* Lazy values *)
Definition force a (lz : coq_type (ml_lazy a)) :=
  match lz with
  | Lval x => Ret x
  | Lref r =>
    do r' <- cget (ml_lazy_val a) r;
    match r' with
    | LzVal x => Ret x
    | LzExn e => raise _ e
    | LzThunk f => handle _
        (do x <- f; do _ <- cput (ml_lazy_val a) r (LzVal _ x); Ret x)
        (fun e => do _ <- cput _ r (LzExn _ e); raise _ e)
    end
  end.
Definition make_lazy a (b : M (coq_type a)) : M (coq_type (ml_lazy a)) :=
  do x <- cnew (ml_lazy_val a) (LzThunk _ b); Ret (Lref _ _ x).
Definition make_lazy_val a (b : coq_type a) : coq_type (ml_lazy a) :=
  Lval _ _ b.

(* Default amount of gas *)
Definition h := 100000.

(* Translated code *)

Definition cycle (T : ml_type) (a b : coq_type T)
  : M (coq_type (ml_rlist T)) :=
  do r <- cnew (ml_rlist T) (Nil (coq_type T) T);
  do l <-
  (do v <- cnew (ml_rlist T) (Cons (coq_type T) T b r);
   Ret (Cons (coq_type T) T a v));
  do _ <- cput (ml_rlist T) r l; Ret l.

Definition l := Restart it (cycle ml_bool true false).

Definition hd (T : ml_type) (def : coq_type T)
  (param : coq_type (ml_rlist T)) : coq_type T :=
  match param with | Nil => def | Cons a _ => a end.

Definition tl (T : ml_type) (param : coq_type (ml_rlist T))
  : M (coq_type (ml_rlist T)) :=
  match param with
  | Nil => Ret (Nil (coq_type T) T)
  | Cons _ t => cget (ml_rlist T) t
  end.

