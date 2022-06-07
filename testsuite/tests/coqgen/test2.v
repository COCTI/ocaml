From mathcomp Require Import ssreflect ssrnat seq.
Require Import Sint63 Ascii String Floats cocti_defs.

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
  | ml_string
  | ml_empty
  | ml_array_t (_ : ml_type)
  | ml_t
  | ml_t0
  | ml_t1
  | ml_t2
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

Local Definition ml_type := ml_type.
Record key := mkkey {key_id : int; key_type : ml_type}.
Variant loc : ml_type -> Type := mkloc : forall k : key, loc (key_type k).

Section with_monad.
Context [M : Type -> Type].

(* Generated type definitions *)
Inductive ml_exns :=
  | T (_ : t)
  | Invalid_argument (_ : string)
  | Failure (_ : string)
  | Not_found
with t := E (_ : ml_exns).

Inductive t2 := T0 (_ : t0)
with t0 := | O | T1_1 (_ : t1)
with t1 := T2_1 (_ : t2).

Local (* Generated type translation function *)
Fixpoint coq_type (T : ml_type) : Type :=
  match T with
  | ml_int => Int63.int
  | ml_char => Ascii.ascii
  | ml_float => float
  | ml_bool => bool
  | ml_unit => unit
  | ml_exn => ml_exns
  | ml_array T1 => loc (ml_array_t T1)
  | ml_list T1 => list (coq_type T1)
  | ml_string => String.string
  | ml_empty => empty
  | ml_array_t T1 => array_t (coq_type T1)
  | ml_t => t
  | ml_t0 => t0
  | ml_t1 => t1
  | ml_t2 => t2
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
Definition empty_env := mkEnv 0%int63 nil.
Definition it : W unit := (empty_env, inl tt).

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
        | T x1, T y1 => compare_rec ml_t x1 y1
        | Invalid_argument x1, Invalid_argument y1 =>
          compare_rec ml_string x1 y1
        | Failure x1, Failure y1 => compare_rec ml_string x1 y1
        | Not_found, _ => Ret Lt
        | _, Not_found => Ret Gt
        | T _, _ => Ret Lt
        | _, T _ => Ret Gt
        | Invalid_argument _, _ => Ret Lt
        | _, Invalid_argument _ => Ret Gt
        end
    | ml_array T1 => fun x y => compare_ref compare_rec (ml_array_t T1) x y
    | ml_list T1 => fun x y => compare_list compare_rec T1 x y
    | ml_string => fun x y => Ret (compare_string x y)
    | ml_empty => fun x y => match x with end
    | ml_array_t T1 =>
      fun x y =>
        match x, y with
        | ArrayVal x1, ArrayVal y1 => compare_rec (ml_list T1) x1 y1
        end
    | ml_t =>
      fun x y => match x, y with | E x1, E y1 => compare_rec ml_exn x1 y1 end
    | ml_t0 =>
      fun x y =>
        match x, y with
        | O, O => Ret Eq
        | T1_1 x1, T1_1 y1 => compare_rec ml_t1 x1 y1
        | O, _ => Ret Lt
        | _, O => Ret Gt
        end
    | ml_t1 =>
      fun x y =>
        match x, y with | T2_1 x1, T2_1 y1 => compare_rec ml_t2 x1 y1 end
    | ml_t2 =>
      fun x y =>
        match x, y with | T0 x1, T0 y1 => compare_rec ml_t0 x1 y1 end
    | ml_ref T1 => fun x y => compare_ref compare_rec T1 x y
    | ml_arrow T1 T2 =>
      fun x y => Fail (Catchable (Invalid_argument "compare"%string))
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
  do len <- nat_of_int len; newref (ml_array_t T) (ArrayVal _ (nseq len x)).
Definition getarray T (a : coq_type (ml_array T)) n : M (coq_type T) :=
  do s <- getref (ml_array_t T) a;
  let: ArrayVal s := s in
  do n <- bounded_nat_of_int (seq.size s) n;
  if s is x :: _ then Ret (nth x s n) else
  raise _ (Invalid_argument "getarray").
Definition setarray T (a : coq_type (ml_array T)) n (x : coq_type T) :=
  do s <- getref (ml_array_t T) a;
  let: ArrayVal s := s in
  do n <- bounded_nat_of_int (seq.size s) n;
  setref (ml_array_t T) a (ArrayVal _ (set_nth x s n x)).

(* Default amount of gas *)
Definition h := 100000.

(* Translated code *)

Definition x := T0 O.

Eval vm_compute in T2_1 x.

Definition failwith (T_1 : ml_type) (s : coq_type ml_string)
  : M (coq_type T_1) := raise T_1 (Failure s).

Fixpoint length_aux (h : nat) (T_1 : ml_type) (len : coq_type ml_int)
  (param : coq_type (ml_list T_1)) : M (coq_type ml_int) :=
  if h is h.+1 then
    match param with
    | @nil _ => Ret len
    | _ :: l => length_aux h T_1 (Int63.add len 1%int63) l
    end
  else FailGas.

Definition length (h : nat) (T_1 : ml_type) (l : coq_type (ml_list T_1))
  : M (coq_type ml_int) := length_aux h T_1 0%int63 l.

Definition cons_1 (T_1 : ml_type) (a : coq_type T_1)
  (l : coq_type (ml_list T_1)) : coq_type (ml_list T_1) := a :: l.

Definition hd (T_1 : ml_type) (param : coq_type (ml_list T_1))
  : M (coq_type T_1) :=
  match param with | @nil _ => failwith T_1 "hd"%string | a :: _ => Ret a end.

