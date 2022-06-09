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
  | ml_color
  | ml_tree (_ : ml_type) (_ : ml_type)
  | ml_point
  | ml_ref_vals (_ : ml_type)
  | ml_endo (_ : ml_type)
  | ml_option (_ : ml_type)
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
Inductive color := | Red | Green | Blue.

Inductive tree (a : Type) (b : Type) :=
  | Leaf (_ : a)
  | Node (_ : tree a b) (_ : b) (_ : tree a b).

Inductive point := Point (_ : loc ml_int) (_ : loc ml_int).

Inductive ref_vals (a : Type) (a_1 : ml_type) :=
  RefVal (_ : loc a_1) (_ : list a).

Inductive endo (a : Type) := Endo (_ : a -> M a).

Inductive option (a : Type) := | Some (_ : a) | None.

Inductive ml_exns :=
  | Restart_1 (_ : unit -> M Int63.int)
  | Invalid_argument (_ : string)
  | Failure (_ : string)
  | Not_found.

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
  | ml_color => color
  | ml_tree T1 T2 => tree (coq_type T1) (coq_type T2)
  | ml_point => point
  | ml_ref_vals T1 => ref_vals (coq_type T1) T1
  | ml_endo T1 => endo (coq_type T1)
  | ml_option T1 => option (coq_type T1)
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
    | ml_int => fun x y => Ret (Int63.compare x y)
    | ml_char => fun x y => Ret (compare_ascii x y)
    | ml_float => fun x y => Ret (compare_float x y)
    | ml_bool => fun x y => Ret (Bool.compare x y)
    | ml_unit => fun x y => Ret Eq
    | ml_exn =>
      fun x y =>
        match x, y with
        | Not_found, Not_found => Ret Eq
        | Restart_1 x1, Restart_1 y1 =>
          compare_rec (ml_arrow ml_unit ml_int) x1 y1
        | Invalid_argument x1, Invalid_argument y1 =>
          compare_rec ml_string x1 y1
        | Failure x1, Failure y1 => compare_rec ml_string x1 y1
        | Not_found, _ => Ret Lt
        | _, Not_found => Ret Gt
        | Restart_1 _, _ => Ret Lt
        | _, Restart_1 _ => Ret Gt
        | Invalid_argument _, _ => Ret Lt
        | _, Invalid_argument _ => Ret Gt
        end
    | ml_array T1 => fun x y => compare_ref compare_rec (ml_array_t T1) x y
    | ml_list T1 => fun x y => compare_list compare_rec T1 x y
    | ml_string => fun x y => Ret (compare_string x y)
    | ml_empty =>
      fun x y => Fail (Catchable (Invalid_argument "compare"%string))
    | ml_array_t T1 =>
      fun x y =>
        match x, y with
        | ArrayVal x1, ArrayVal y1 => compare_rec (ml_list T1) x1 y1
        end
    | ml_color =>
      fun x y =>
        match x, y with
        | Red, Red => Ret Eq
        | Green, Green => Ret Eq
        | Blue, Blue => Ret Eq
        | Red, _ => Ret Lt
        | _, Red => Ret Gt
        | Green, _ => Ret Lt
        | _, Green => Ret Gt
        end
    | ml_tree T1 T2 =>
      fun x y =>
        match x, y with
        | Leaf x1, Leaf y1 => compare_rec T1 x1 y1
        | Node x1 x2 x3, Node y1 y2 y3 =>
          lexi_compare (compare_rec (ml_tree T1 T2) x1 y1)
            (Delay
               (lexi_compare (compare_rec T2 x2 y2)
                  (Delay (compare_rec (ml_tree T1 T2) x3 y3))))
        | Leaf _, _ => Ret Lt
        | _, Leaf _ => Ret Gt
        end
    | ml_point =>
      fun x y =>
        match x, y with
        | Point x1 x2, Point y1 y2 =>
          lexi_compare (compare_rec (ml_ref ml_int) x1 y1)
            (Delay (compare_rec (ml_ref ml_int) x2 y2))
        end
    | ml_ref_vals T1 =>
      fun x y =>
        match x, y with
        | RefVal x1 x2, RefVal y1 y2 =>
          lexi_compare (compare_rec (ml_ref T1) x1 y1)
            (Delay (compare_rec (ml_list T1) x2 y2))
        end
    | ml_endo T1 =>
      fun x y =>
        match x, y with
        | Endo x1, Endo y1 => compare_rec (ml_arrow T1 T1) x1 y1
        end
    | ml_option T1 =>
      fun x y =>
        match x, y with
        | None, None => Ret Eq
        | Some x1, Some y1 => compare_rec T1 x1 y1
        | None, _ => Ret Lt
        | _, None => Ret Gt
        end
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
Definition h := 100.

(* jikken *)

Definition fact (n : int) : M int :=
  do r <- newref ml_int 1%sint63 ;
  do _ <- forloop h 2 n
   (fun i => do v <- getref ml_int r ; setref ml_int r (v * i)%sint63) ;
   getref ml_int r.

Print fact.

Eval compute in fact 5 empty_env.
Check whileloop.

Definition fact' (n : int) : M int :=
  do i <- newref ml_int n; do v <- newref ml_int 1%sint63;
  do _ <- whileloop h
          (do x <- getref ml_int i; Ret (if Sint63.compare x 0%sint63 is Gt then true else false))
          (do x <- getref ml_int v; do y <- getref ml_int i; do _ <- setref ml_int v (x * y)%sint63;
           setref ml_int i (y - 1)%sint63);
  getref ml_int v.

Eval compute in fact' 5 empty_env.

Definition newton (n : float) : M float :=
  do r <- newref ml_float 1.0%float ;
  do _ <- forloop h 1 10
    (fun i => do v <- getref ml_float r;
      setref ml_float r ((v * v + n) / (2 * v))%float);
    getref ml_float r.

Eval compute in newton 2.0 empty_env.
Eval compute in newton 100.0 empty_env.

Definition newton' (e x_0 : float) (f : float -> float) : M float :=
  let diff (e : float) (f : float -> float) 
    := fun x => (((f (x + e)) - (f x)) / e)%float in
  do r <- newref ml_float x_0%float;
  do _ <- forloop h 1 10
    (fun i => do v <- getref ml_float r;
       setref ml_float r (v - (f v / diff e f v))%float);
    getref ml_float r.

Definition e := (1 / 1000000)%float.

Eval compute in newton' e 1.0 (fun x => (x * x - 2)%float) empty_env.
Eval compute in newton' e 1.0 (fun x => (x * x - 100)%float) empty_env.
Eval compute in newton' e 1.0 (fun x => (x * x * x - 5)%float) empty_env.
Eval compute in newton' e 1.0 (fun x => (x * x * x - 8)%float) empty_env.
