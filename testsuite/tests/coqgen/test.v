From mathcomp Require Import ssreflect ssrnat seq.
Require Import Int63 Ascii String cocti_defs.

(* Generated representation of all ML types *)
Inductive ml_type :=
  | ml_int
  | ml_char
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


Inductive ml_exns :=
  | Invalid_argument (_ : string)
  | Failure (_ : string)
  | Not_found.

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
Local Definition ml_exns := ml_exns.
Record key := mkkey {key_id : int; key_type : ml_type}.
Variant loc : ml_type -> Type := mkloc : forall k : key, loc (key_type k).

Section with_monad.
Variable M : Type -> Type.

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

Local (* Generated type translation function *)
Fixpoint coq_type (T : ml_type) : Type :=
  match T with
  | ml_int => Int63.int
  | ml_char => Ascii.ascii
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
End MLtypes.
Export MLtypes.

Module REFmonadML := REFmonad (MLtypes).
Export REFmonadML.

Definition coq_type := MLtypes.coq_type M.
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
Definition h := 100000.

(* Translated code *)

Definition ref' (T : ml_type) := newref T.

Definition id (T : ml_type) (h_1 : coq_type T) : coq_type T := h_1.

Definition incr (r : coq_type (ml_ref ml_int)) : M (coq_type ml_unit) :=
  do x <- getref ml_int r; setref ml_int r (Int63.add x 1%int63).

Definition it_1 := Restart it (do r <- newref ml_int 1%int63; incr r).
Eval vm_compute in it_1.

Definition it_2 :=
  Restart it_1
    (do x <- newref (ml_list ml_empty) (@nil (coq_type ml_empty));
     getref (ml_list ml_empty) x).
Eval vm_compute in it_2.

Definition nil_1 :=
  Restart it_2
    ((fun T : ml_type =>
        do x <- newref (ml_list T) (@nil (coq_type T)); getref (ml_list T) x)
       ml_empty).

Fixpoint loop (h : nat) (T T_1 : ml_type) (h_1 : coq_type T_1)
  : M (coq_type T) := if h is h.+1 then loop h T T_1 h_1 else FailGas.

Fixpoint fib (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_le h ml_int n 1%int63;
    if v then Ret 1%int63 else
      do v <- fib h (Int63.sub n 2%int63);
      do v_1 <- fib h (Int63.sub n 1%int63); Ret (Int63.add v_1 v)
  else FailGas.

Definition it_3 := Restart nil_1 (fib h 10%int63).
Eval vm_compute in it_3.

Fixpoint ack (h : nat) (m n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_le h ml_int m 0%int63;
    if v then Ret (Int63.add n 1%int63) else
      do v <- ml_le h ml_int n 0%int63;
      if v then ack h (Int63.sub m 1%int63) 1%int63 else
        do v <- ack h m (Int63.sub n 1%int63); ack h (Int63.sub m 1%int63) v
  else FailGas.

Definition it_4 := Restart it_3 (ack h 3%int63 7%int63).
Eval vm_compute in it_4.

Definition it_5 :=
  Restart it_4 (ml_lt h ml_string "hellas"%string "hello"%string).
Eval vm_compute in it_5.

Definition cmp := Restart it_5 (ml_lt h ml_char "a"%char "A"%char).

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

Definition it_6 :=
  Restart cmp
    (map h ml_int ml_int
       (fun x : coq_type ml_int =>
          Ret (Int63.add x 1%int63 : coq_type ml_int))
       (3%int63 :: 2%int63 :: 1%int63 :: @nil (coq_type ml_int))).
Eval vm_compute in it_6.

Definition one :=
  Restart it_6 (do r <- newref ml_int 1%int63; getref ml_int r).

Fixpoint map3 (h : nat) (T : ml_type) (f : coq_type (ml_arrow T ml_int))
  (param : coq_type (ml_list T)) : M (coq_type (ml_list ml_int)) :=
  do one <- FromW one;
  if h is h.+1 then
    match param with
    | @nil _ => Ret (@nil (coq_type ml_int))
    | a :: l =>
      do v <- map3 h T f l;
      do v_1 <- (do v <- f a; Ret (Int63.add one v));
      Ret (@cons (coq_type ml_int) v_1 v)
    end
  else FailGas.

Definition it_7 :=
  Restart one
    (map3 h ml_int
       (fun x : coq_type ml_int =>
          Ret (Int63.add x 1%int63 : coq_type ml_int))
       (3%int63 :: 2%int63 :: 1%int63 :: @nil (coq_type ml_int))).
Eval vm_compute in it_7.

Fixpoint append (h : nat) (T : ml_type) (l1 l2 : coq_type (ml_list T))
  : M (coq_type (ml_list T)) :=
  if h is h.+1 then
    match l1 with
    | @nil _ => Ret l2
    | a :: l => do v <- append h T l l2; Ret (@cons (coq_type T) a v)
    end
  else FailGas.

Definition arr := Restart it_7 (newarray ml_int 3%int63 5%int63).

Definition it_8 :=
  Restart arr (do arr <- FromW arr; setarray ml_int arr 1%int63 6%int63).
Eval vm_compute in it_8.

Definition it_9 := Restart it_8 (ml_ge h ml_color Green Blue).
Eval vm_compute in it_9.

Definition mknode (T : ml_type) (t1 t2 : coq_type (ml_tree T ml_int))
  : coq_type (ml_tree T ml_int) :=
  Node (coq_type T) (coq_type ml_int) t1 0%int63 t2.

Definition it_10 :=
  Restart it_9
    (ml_lt h (ml_tree ml_string ml_int)
       (mknode ml_string
          (Leaf (coq_type ml_string) (coq_type ml_int) "a"%string)
          (Leaf (coq_type ml_string) (coq_type ml_int) "b"%string))
       (mknode ml_string
          (Leaf (coq_type ml_string) (coq_type ml_int) "a"%string)
          (mknode ml_string
             (Leaf (coq_type ml_string) (coq_type ml_int) "b"%string)
             (Leaf (coq_type ml_string) (coq_type ml_int) "b"%string)))).
Eval vm_compute in it_10.

Fixpoint iter_int (h : nat) (T : ml_type) (n : coq_type ml_int)
  (f : coq_type (ml_arrow T T)) (x : coq_type T) : M (coq_type T) :=
  if h is h.+1 then
    do v <- ml_lt h ml_int n 1%int63;
    if v then Ret x else do v <- f x; iter_int h T (Int63.sub n 1%int63) f v
  else FailGas.

Definition fib2 (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  do l1 <- newref ml_int 1%int63;
  do l2 <- newref ml_int 1%int63;
  do _ <-
  iter_int h ml_unit n
    (fun _ =>
       do x <- getref ml_int l1;
       do y <- getref ml_int l2;
       do _ <- setref ml_int l1 y; setref ml_int l2 (Int63.add x y))
    tt;
  getref ml_int l1.

Definition it_11 := Restart it_10 (fib2 h 1000%int63).
Eval vm_compute in it_11.

Fixpoint iota (h : nat) (m n : coq_type ml_int)
  : M (coq_type (ml_list ml_int)) :=
  if h is h.+1 then
    do v <- ml_le h ml_int n 0%int63;
    if v then Ret (@nil (coq_type ml_int)) else
      do v <- iota h (Int63.add m 1%int63) (Int63.sub n 1%int63);
      Ret (@cons (coq_type ml_int) m v)
  else FailGas.

Definition it_12 := Restart it_11 (iota h 1%int63 10%int63).
Eval vm_compute in it_12.

Definition omega (T : ml_type) (n : coq_type T) : M (coq_type T) :=
  do r <- newref (ml_arrow T T) (fun x : coq_type T => Ret (x : coq_type T));
  let delta (i : coq_type T) : M (coq_type T) :=
    AppM (getref (ml_arrow T T) r) i in
  do _ <- setref (ml_arrow T T) r delta; delta n.

Definition fixpt (h : nat) (T T_1 : ml_type)
  (f : coq_type (ml_arrow (ml_arrow T_1 T) (ml_arrow T_1 T)))
  : M (coq_type (ml_arrow T_1 T)) :=
  do r <- newref (ml_arrow T_1 T) (fun x : coq_type T_1 => loop h T T_1 x);
  let delta (i : coq_type T_1) : M (coq_type T) :=
    do v <- getref (ml_arrow T_1 T) r; AppM (f v) i in
  do _ <- setref (ml_arrow T_1 T) r delta; Ret delta.

Definition fib_1 :=
  Restart it_12
    (fixpt h ml_int ml_int
       (fun fib_1 : coq_type (ml_arrow ml_int ml_int) =>
          Ret
            (fun n : coq_type ml_int =>
               do v <- ml_le h ml_int n 1%int63;
               if v then Ret 1%int63 else
                 do v <- fib_1 (Int63.sub n 2%int63);
                 do v_1 <- fib_1 (Int63.sub n 1%int63); Ret (Int63.add v_1 v)))).

Definition it_13 := Restart fib_1 (do fib_1 <- FromW fib_1; fib_1 10%int63).
Eval vm_compute in it_13.

Definition r :=
  Restart it_13 (newref (ml_list ml_int) (3%int63 :: @nil (coq_type ml_int))).

Definition z :=
  Restart r
    (do r <- FromW r;
     do _ <-
     (do v <-
      (do v <- getref (ml_list ml_int) r;
       Ret (@cons (coq_type ml_int) 1%int63 v));
      setref (ml_list ml_int) r v);
     getref (ml_list ml_int) r).

Definition it_14 := Restart z (do r <- FromW r; getref (ml_list ml_int) r).
Eval vm_compute in it_14.

Definition z' := Restart it_14 (do z <- FromW z; Ret z).

Definition it_15 :=
  Restart z'
    (do r <- FromW r;
     let r_1 := r in
     do _ <-
     (do v <-
      (do v <- getref (ml_list ml_int) r_1;
       Ret (@cons (coq_type ml_int) 1%int63 v));
      setref (ml_list ml_int) r_1 v);
     getref (ml_list ml_int) r_1).
Eval vm_compute in it_15.

Definition f (v : coq_type ml_unit) :=
  do z' <- FromW z';
  Ret (match v with | tt => z' end : coq_type (ml_list ml_int)).

Definition f2 (h : nat) (v : coq_type ml_unit)
  : M (coq_type (ml_list ml_int)) :=
  match v with
  | tt => do v <- f tt; do v_1 <- f tt; append h ml_int v_1 v
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
    do v <-
    (do v <- getref (ml_list ml_int) r;
     Ret (@cons (coq_type ml_int) 4%int63 v));
    setref (ml_list ml_int) r v
  end.

Definition it_16 :=
  Restart it_15
    (do r <- FromW r; do _ <- double_r tt; getref (ml_list ml_int) r).
Eval vm_compute in it_16.

Fixpoint mccarthy_m (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_gt h ml_int n 100%int63;
    if v then Ret (Int63.sub n 10%int63) else
      do v <- mccarthy_m h (Int63.add n 11%int63); mccarthy_m h v
  else FailGas.

Definition it_17 := Restart it_16 (mccarthy_m h 10%int63).
Eval vm_compute in it_17.

Fixpoint tarai (h : nat) (x y z_1 : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_lt h ml_int y x;
    if v then
      do v <- tarai h (Int63.sub z_1 1%int63) x y;
      do v_1 <- tarai h (Int63.sub y 1%int63) z_1 x;
      do v_2 <- tarai h (Int63.sub x 1%int63) y z_1; tarai h v_2 v_1 v
    else Ret y
  else FailGas.

Definition it_18 := Restart it_17 (tarai h 1%int63 2%int63 3%int63).
Eval vm_compute in it_18.

Definition it_19 := Restart it_18 (omega ml_int 1%int63).
Eval vm_compute in it_19.

Definition it_20 :=
  Restart it_19
    (AppM
       (fixpt h ml_empty ml_int
          (fun f_1 : coq_type (ml_arrow ml_int ml_empty) =>
             Ret (f_1 : coq_type (ml_arrow ml_int ml_empty))))
       0%int63).
Eval vm_compute in it_20.

