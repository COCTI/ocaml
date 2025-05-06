From mathcomp Require Import ssreflect ssrnat eqtype seq.
From HB Require Import structures.
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
  | ml_color
  | ml_tree (_ : ml_type) (_ : ml_type)
  | ml_point
  | ml_ref_vals (_ : ml_type)
  | ml_endo (_ : ml_type)
  | ml_option (_ : ml_type)
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

Definition ml_type_eq_mixin := hasDecEq.Build _ (comparePc _ ml_type_eq_dec).
HB.instance Definition ml_type_eqType := ml_type_eq_mixin.

Local Definition ml_type : eqType := ml_type.
Local Notation loc := (@loc ml_type).

Section with_monad.
Context [M : Type -> Type].

(* Generated type definitions *)
Inductive ml_exns :=
  | Restart_1 (_ : unit -> M PrimInt63.int)
  | Invalid_argument (_ : string)
  | Failure (_ : string)
  | Not_found.

Inductive option (a : Type) := | Some (_ : a) | None.

Inductive endo (a : Type) := Endo (_ : a -> M a).

Inductive ref_vals (a : Type) (a_1 : ml_type) :=
  RefVal (_ : loc a_1) (_ : list a).

Inductive point := Point (_ : loc ml_int) (_ : loc ml_int).

Inductive tree (a : Type) (b : Type) :=
  | Leaf (_ : a)
  | Node (_ : tree a b) (_ : b) (_ : tree a b).

Inductive color := | Red | Green | Blue.


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
  | ml_color => color
  | ml_tree T1 T2 => tree (coq_type T1) (coq_type T2)
  | ml_point => point
  | ml_ref_vals T1 => ref_vals (coq_type T1) T1
  | ml_endo T1 => endo (coq_type T1)
  | ml_option T1 => option (coq_type T1)
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
    | ml_lazy T1 =>
      fun x y => Raise (Catchable (Invalid_argument "compare"%string))
    | ml_string => fun x y => Ret (compare_string x y)
    | ml_empty => fun x y => match x with end
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

Definition div (x y : coq_type ml_float) : coq_type ml_float :=
  div%float x y.

Definition harmonic (x y : coq_type ml_float) : coq_type ml_float :=
  div%float (2.0%float)
    (add%float (div%float (1.0%float) x) (div%float (1.0%float) y)).

Fixpoint float_sum (h : nat) (l : coq_type (ml_list ml_float))
  : M (coq_type ml_float) :=
  if h is h.+1 then
    match l with
    | @nil _ => Ret (0.0%float)
    | first :: rest => do v <- float_sum h rest; Ret (add%float first v)
    end
  else FailGas.

Definition newton's_method (e : coq_type ml_float)
  (f : coq_type (ml_arrow ml_float ml_float)) : M (coq_type ml_float) :=
  let diff (e_1 : coq_type ml_float)
  (f_1 : coq_type (ml_arrow ml_float ml_float)) (x : coq_type ml_float)
  : M (coq_type ml_float) :=
    do v <-
    (do v <- f_1 x; do v_1 <- f_1 (add%float x e_1); Ret (sub%float v_1 v));
    Ret (div%float v e_1) in
  do r <- cnew ml_float (1.0%float);
  do _ <-
  (do u <- Ret 1%int63;
   do v <- Ret 10%int63;
   forloop u v
     (fun i =>
        do v <-
        (do v <-
         (do v <- (do v <- cget ml_float r; diff e f v);
          do v_1 <- (do v <- cget ml_float r; f v); Ret (div%float v_1 v));
         do v_1 <- cget ml_float r; Ret (sub%float v_1 v));
        cput ml_float r v));
  cget ml_float r.

Definition fact (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  do i <- cnew ml_int n;
  do v <- cnew ml_int 1%int63;
  do _ <-
  whileloop h (do v_1 <- cget ml_int i; ml_gt h ml_int v_1 0%int63)
    (do _ <-
     (do v_1 <-
      (do v_1 <- cget ml_int i;
       do v_2 <- cget ml_int v; Ret (PrimInt63.mul v_2 v_1));
      cput ml_int v v_1);
     do v_1 <- (do v_1 <- cget ml_int i; Ret (PrimInt63.sub v_1 1%int63));
     cput ml_int i v_1);
  cget ml_int v.

Definition ref' (T : ml_type) := cnew T.

Definition foo1 (T : ml_type) (x : coq_type T) : M (coq_type T) :=
  let id (T_1 : ml_type) (y : coq_type T_1) : coq_type T_1 := y in
  id (ml_arrow T T) (fun x_1 => Ret (id T x_1)) x.

Definition id (T : ml_type) (h_1 : coq_type T) : coq_type T := h_1.

Definition foo2 (x : coq_type ml_int) : coq_type (ml_arrow ml_int ml_int) :=
  let y := PrimInt63.add x 1%int63 in
  id (ml_arrow ml_int ml_int)
    (fun z : coq_type ml_int => Ret (PrimInt63.add y z : coq_type ml_int)).

Definition foo3 (x : coq_type ml_int)
  : M (coq_type (ml_arrow ml_int ml_int)) :=
  id (ml_arrow ml_int (ml_arrow ml_int ml_int)) (fun x_1 => Ret (foo2 x_1)) x.

Definition incr (r : coq_type (ml_ref ml_int)) : M (coq_type ml_unit) :=
  do x <- cget ml_int r; cput ml_int r (PrimInt63.add x 1%int63).

Definition it_1 := Eval compute in
  Restart it (do r <- cnew ml_int 1%int63; incr r).
Print it_1.
Definition lazy_counter (c : coq_type (ml_ref ml_int))
  : M (coq_type (ml_lazy ml_int)) :=
  make_lazy ml_int (do _ <- incr c; cget ml_int c).

Definition it_2 := Eval compute in
  Restart it_1
    (do c <- cnew ml_int 0%int63;
     do m <- lazy_counter c;
     do n <- lazy_counter c;
     do n_1 <- force ml_int n;
     do m_1 <- force ml_int m; Ret (m_1 :: n_1 :: @nil (coq_type ml_int))).
Print it_2.
Definition it_3 := Eval compute in
  Restart it_2
    (do x <- cnew (ml_list ml_empty) (@nil (coq_type ml_empty));
     cget (ml_list ml_empty) x).
Print it_3.
Definition nil_1 :=
  Restart it_3
    ((fun T : ml_type =>
        do x <- cnew (ml_list T) (@nil (coq_type T)); cget (ml_list T) x)
       ml_empty).

Fixpoint loop (h : nat) (T T_1 : ml_type) (h_1 : coq_type T_1)
  : M (coq_type T) := if h is h.+1 then loop h T T_1 h_1 else FailGas.

Fixpoint fib (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_le h ml_int n 1%int63;
    if v then Ret 1%int63 else
      do v <- fib h (PrimInt63.sub n 2%int63);
      do v_1 <- fib h (PrimInt63.sub n 1%int63); Ret (PrimInt63.add v_1 v)
  else FailGas.

Definition it_4 := Eval compute in Restart nil_1 (fib h 10%int63).
Print it_4.
Fixpoint ack (h : nat) (m n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_le h ml_int m 0%int63;
    if v then Ret (PrimInt63.add n 1%int63) else
      do v <- ml_le h ml_int n 0%int63;
      if v then ack h (PrimInt63.sub m 1%int63) 1%int63 else
        do v <- ack h m (PrimInt63.sub n 1%int63);
        ack h (PrimInt63.sub m 1%int63) v
  else FailGas.

Definition it_5 := Eval compute in Restart it_4 (ack h 3%int63 7%int63).
Print it_5.
Definition it_6 := Eval compute in
  Restart it_5 (ml_lt h ml_string "hellas"%string "hello"%string).
Print it_6.
Definition cmp := Restart it_6 (ml_lt h ml_char "a"%char "A"%char).

Fixpoint map (h : nat) (T T_1 : ml_type) (f : coq_type (ml_arrow T_1 T))
  (l : coq_type (ml_list T_1)) : M (coq_type (ml_list T)) :=
  if h is h.+1 then
    match l with
    | @nil _ => Ret (@nil (coq_type T))
    | a :: l_1 =>
      do v <- map h T T_1 f l_1;
      do v_1 <- f a; Ret (@cons (coq_type T) v_1 v)
    end
  else FailGas.

Fixpoint map' (h : nat) (T T_1 : ml_type) (f : coq_type (ml_arrow T_1 T))
  (param : coq_type (ml_list T_1)) : M (coq_type (ml_list T)) :=
  if h is h.+1 then
    match param with
    | @nil _ => Ret (@nil (coq_type T))
    | a :: l =>
      do v <- map' h T T_1 f l; do v_1 <- f a; Ret (@cons (coq_type T) v_1 v)
    end
  else FailGas.

Definition it_7 := Eval compute in
  Restart cmp
    (map h ml_int ml_int
       (fun x : coq_type ml_int =>
          Ret (PrimInt63.add x 1%int63 : coq_type ml_int))
       (3%int63 :: 2%int63 :: 1%int63 :: @nil (coq_type ml_int))).
Print it_7.
Definition one := Restart it_7 (do r <- cnew ml_int 1%int63; cget ml_int r).

Fixpoint map3 (h : nat) (T : ml_type) (f : coq_type (ml_arrow T ml_int))
  (param : coq_type (ml_list T)) : M (coq_type (ml_list ml_int)) :=
  do one <- FromW one;
  if h is h.+1 then
    match param with
    | @nil _ => Ret (@nil (coq_type ml_int))
    | a :: l =>
      do v <- map3 h T f l;
      do v_1 <- (do v <- f a; Ret (PrimInt63.add one v));
      Ret (@cons (coq_type ml_int) v_1 v)
    end
  else FailGas.

Definition it_8 := Eval compute in
  Restart one
    (map3 h ml_int
       (fun x : coq_type ml_int =>
          Ret (PrimInt63.add x 1%int63 : coq_type ml_int))
       (3%int63 :: 2%int63 :: 1%int63 :: @nil (coq_type ml_int))).
Print it_8.
Fixpoint append (h : nat) (T : ml_type) (l1 l2 : coq_type (ml_list T))
  : M (coq_type (ml_list T)) :=
  if h is h.+1 then
    match l1 with
    | @nil _ => Ret l2
    | a :: l => do v <- append h T l l2; Ret (@cons (coq_type T) a v)
    end
  else FailGas.

Definition arr := Restart it_8 (newarray ml_int 3%int63 5%int63).

Definition it_9 := Eval compute in
  Restart arr (do arr <- FromW arr; setarray ml_int arr 1%int63 6%int63).
Print it_9.
Definition it_10 := Eval compute in
  Restart it_9 (ml_ge h ml_color Green Blue).
Print it_10.
Definition mknode (T : ml_type) (t1 t2 : coq_type (ml_tree T ml_int))
  : coq_type (ml_tree T ml_int) :=
  Node (coq_type T) (coq_type ml_int) t1 0%int63 t2.

Definition it_11 := Eval compute in
  Restart it_10
    (ml_lt h (ml_tree ml_string ml_int)
       (mknode ml_string
          (Leaf (coq_type ml_string) (coq_type ml_int) "a"%string)
          (Leaf (coq_type ml_string) (coq_type ml_int) "b"%string))
       (mknode ml_string
          (Leaf (coq_type ml_string) (coq_type ml_int) "a"%string)
          (mknode ml_string
             (Leaf (coq_type ml_string) (coq_type ml_int) "b"%string)
             (Leaf (coq_type ml_string) (coq_type ml_int) "b"%string)))).
Print it_11.
Fixpoint iter_int (h : nat) (T : ml_type) (n : coq_type ml_int)
  (f : coq_type (ml_arrow T T)) (x : coq_type T) : M (coq_type T) :=
  if h is h.+1 then
    do v <- ml_lt h ml_int n 1%int63;
    if v then Ret x else
      do v <- f x; iter_int h T (PrimInt63.sub n 1%int63) f v
  else FailGas.

Definition fib2 (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  do l1 <- cnew ml_int 1%int63;
  do l2 <- cnew ml_int 1%int63;
  do _ <-
  iter_int h ml_unit n
    (fun _ =>
       do x <- cget ml_int l1;
       do y <- cget ml_int l2;
       do _ <- cput ml_int l1 y; cput ml_int l2 (PrimInt63.add x y))
    tt;
  cget ml_int l1.

Definition it_12 := Eval compute in Restart it_11 (fib2 h 1000%int63).
Print it_12.
Fixpoint iota (h : nat) (m n : coq_type ml_int)
  : M (coq_type (ml_list ml_int)) :=
  if h is h.+1 then
    do v <- ml_le h ml_int n 0%int63;
    if v then Ret (@nil (coq_type ml_int)) else
      do v <- iota h (PrimInt63.add m 1%int63) (PrimInt63.sub n 1%int63);
      Ret (@cons (coq_type ml_int) m v)
  else FailGas.

Definition it_13 := Eval compute in Restart it_12 (iota h 1%int63 10%int63).
Print it_13.
Definition r :=
  Restart it_13 (cnew (ml_list ml_int) (3%int63 :: @nil (coq_type ml_int))).

Definition z :=
  Restart r
    (do r <- FromW r;
     do _ <-
     (do v <-
      (do v <- cget (ml_list ml_int) r;
       Ret (@cons (coq_type ml_int) 1%int63 v));
      cput (ml_list ml_int) r v);
     cget (ml_list ml_int) r).

Definition it_14 := Eval compute in
  Restart z (do r <- FromW r; cget (ml_list ml_int) r).
Print it_14.
Definition z' := Restart it_14 (do z <- FromW z; Ret z).

Definition it_15 := Eval compute in
  Restart z'
    (do r <- FromW r;
     let r_1 := r in
     do _ <-
     (do v <-
      (do v <- cget (ml_list ml_int) r_1;
       Ret (@cons (coq_type ml_int) 1%int63 v));
      cput (ml_list ml_int) r_1 v);
     cget (ml_list ml_int) r_1).
Print it_15.
Definition f (v : coq_type ml_unit) :=
  do z' <- FromW z';
  Ret (match v with | tt => z' end : coq_type (ml_list ml_int)).

Definition f2 (h : nat) (v : coq_type ml_unit)
  : M (coq_type (ml_list ml_int)) :=
  match v with
  | tt => do v_1 <- f tt; do v_2 <- f tt; append h ml_int v_2 v_1
  end.

Fixpoint g (h : nat) (x : coq_type ml_int) : M (coq_type (ml_list ml_int)) :=
  do z <- FromW z;
  if h is h.+1 then
    do v <- ml_gt h ml_int x 0%int63; if v then Ret z else g h 1%int63
  else FailGas.

Definition double_r (v : coq_type ml_unit) : M (coq_type ml_unit) :=
  do r <- FromW r;
  match v with
  | tt =>
    do v_1 <-
    (do v_1 <- cget (ml_list ml_int) r;
     Ret (@cons (coq_type ml_int) 4%int63 v_1));
    cput (ml_list ml_int) r v_1
  end.

Definition it_16 := Eval compute in
  Restart it_15
    (do r <- FromW r; do _ <- double_r tt; cget (ml_list ml_int) r).
Print it_16.
Fixpoint mccarthy_m (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_gt h ml_int n 100%int63;
    if v then Ret (PrimInt63.sub n 10%int63) else
      do v <- mccarthy_m h (PrimInt63.add n 11%int63); mccarthy_m h v
  else FailGas.

Definition it_17 := Eval compute in Restart it_16 (mccarthy_m h 10%int63).
Print it_17.
Fixpoint tarai (h : nat) (x y z_1 : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_lt h ml_int y x;
    if v then
      do v <- tarai h (PrimInt63.sub z_1 1%int63) x y;
      do v_1 <- tarai h (PrimInt63.sub y 1%int63) z_1 x;
      do v_2 <- tarai h (PrimInt63.sub x 1%int63) y z_1; tarai h v_2 v_1 v
    else Ret y
  else FailGas.

Definition it_18 := Eval compute in
  Restart it_17 (tarai h 1%int63 2%int63 3%int63).
Print it_18.
Definition failwith (T : ml_type) (s : coq_type ml_string)
  : M (coq_type T) := raise T (Failure s).

Definition it_19 := Eval compute in
  Restart it_18 (failwith ml_empty "Bad"%string).
Print it_19.
Definition it_20 := Eval compute in
  Restart it_19
    (handle ml_string
       (if true then failwith ml_string "a"%string else Ret "b"%string)
       (fun v => if v is Failure x then Ret x else raise ml_string v)).
Print it_20.
Definition it_21 := Eval compute in
  Restart it_20
    ((fun x : coq_type ml_exn => raise ml_empty x) (Failure "Hello"%string)).
Print it_21.
Definition it_22 := Eval compute in
  Restart it_21
    (handle ml_int
       (do v <-
        raise ml_int
          (Restart_1
             (fun x : coq_type ml_unit => Ret (3%int63 : coq_type ml_int)));
        Ret (id ml_int v))
       (fun v => if v is Restart_1 f_1 then f_1 tt else raise ml_int v)).
Print it_22.
Definition omega (T : ml_type) (n : coq_type T) : M (coq_type T) :=
  do r_1 <- cnew (ml_arrow T T) (fun x : coq_type T => Ret (x : coq_type T));
  let delta (i : coq_type T) : M (coq_type T) :=
    AppM (cget (ml_arrow T T) r_1) i in
  do _ <- cput (ml_arrow T T) r_1 delta; delta n.

Definition fixpt (h : nat) (T T_1 : ml_type)
  (f_1 : coq_type (ml_arrow (ml_arrow T_1 T) (ml_arrow T_1 T)))
  : M (coq_type (ml_arrow T_1 T)) :=
  do r_1 <- cnew (ml_arrow T_1 T) (fun x : coq_type T_1 => loop h T T_1 x);
  let delta (i : coq_type T_1) : M (coq_type T) :=
    do v <- cget (ml_arrow T_1 T) r_1; AppM (f_1 v) i in
  do _ <- cput (ml_arrow T_1 T) r_1 delta; Ret delta.

Definition fib_1 :=
  Restart it_22
    (fixpt h ml_int ml_int
       (fun fib_2 : coq_type (ml_arrow ml_int ml_int) =>
          Ret
            (fun n : coq_type ml_int =>
               do v <- ml_le h ml_int n 1%int63;
               if v then Ret 1%int63 else
                 do v <- fib_2 (PrimInt63.sub n 2%int63);
                 do v_1 <- fib_2 (PrimInt63.sub n 1%int63);
                 Ret (PrimInt63.add v_1 v)))).

Definition it_23 := Eval compute in
  Restart fib_1 (do fib_1 <- FromW fib_1; fib_1 10%int63).
Print it_23.
Definition it_24 := Eval compute in Restart it_23 (omega ml_int 1%int63).
Print it_24.
Definition it_25 := Eval compute in
  Restart it_24
    (AppM
       (fixpt h ml_empty ml_int
          (fun f_1 : coq_type (ml_arrow ml_int ml_empty) =>
             Ret (f_1 : coq_type (ml_arrow ml_int ml_empty))))
       0%int63).
Print it_25.
