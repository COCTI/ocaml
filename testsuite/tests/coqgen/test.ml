(* TEST
flags = "-coq"
compile_only = "true"
* setup-ocamlc.byte-build-env
** ocamlc.byte
*)
(* ../../../ocamlc -c -coq -I ../../../stdlib test.ml *)

(* float *)
let div x y = x /. y;;
let harmonic x y = 2. /. ((1. /. x) +. (1. /. y));;

(*  float loop *)
let rec float_sum l = match l with
  | [] -> 0.0
  | first :: rest -> first +. float_sum rest;;

let newton's_method e f =
  let diff e f = fun x -> ((f (x +. e) -. f x)) /. e in
  let r = ref 1.0 in
  for i = 1 to 10 do
    r := !r -. (f !r /. diff e f !r)
  done;
  !r;;

(* for loop *)
(*let fact n =
  let v = ref 1 in
  for i = 2 to n do
    v := !v * i
  done;
  !v
*)
(* while loop *)
let fact n =
  let i = ref n in
  let v = ref 1 in
  while !i > 0 do
    v := !v * !i;
    i := !i - 1
  done;
  !v

(* redefinition *)
let ref' = ref;;

(* let polymorphism *)
let foo1 x =
  let id y = y in id id x;;

(* pure arity *)
let id h = h;;

let foo2 x = let y = x + 1 in id (fun z -> y + z);;

let foo3 x = id foo2 x;;

(* references *)
let incr r =
  let x = !r in r := x + 1;;

let r = ref 1 in incr r;;

(* lazy *)
let lazy_counter c = lazy (incr c; !c);;
let c = ref 0 in let m = lazy_counter c in let n = lazy_counter c in
let n = Lazy.force n in let m = Lazy.force m in [m; n];;

(* relaxed value restriction? *)
let x = ref [] in !x;;
let nil = let x = ref [] in !x;;
(* let onel = 1 :: nil;;  requires subtyping *)

(* Recursion *)
let rec loop h = loop h;;

let rec fib n =
  if n <= 1 then 1 else fib (n-1) + fib (n-2);;

fib 10;;

let rec ack m n =
  if m <= 0 then n + 1 else
  if n <= 0 then ack (m-1) 1 else
  ack (m-1) (ack m (n-1)) ;;

ack 3 7;;

(* string and char *)
"hellas" < "hello";;
let cmp = 'a' < 'A';;

(* Lists *)

let rec map f l =
  match l with
  | [] -> []
  | a :: l -> f a :: map f l
;;

let rec map' f = function
  | [] -> []
  | a :: l -> f a :: map' f l
;;
map (fun x -> x + 1) [3;2;1] ;;

let one = let r = ref 1 in !r;;
let rec map3 f = function
  | [] -> []
  | a :: l -> one + f a :: map3 f l
;;
map3 (fun x -> x + 1) [3;2;1] ;;

let rec append l1 l2 =
  match l1 with
  | [] -> l2
  | a :: l -> a :: append l l2
;;

(* Arrays *)

let arr = Array.make 3 5;;

arr.(1) <- 6;;

(* Datatypes *)

type color = Red | Green | Blue ;;

Green >= Blue ;;

type ('a,'b) tree = Leaf of 'a | Node of ('a,'b) tree * 'b * ('a,'b) tree ;;

let mknode t1 t2 = Node (t1, 0, t2) ;;

mknode (Leaf "a") (Leaf "b") < mknode (Leaf "a") (mknode (Leaf "b") (Leaf "b"))
;;

type point = Point of int ref * int ref ;;

type 'a ref_vals = RefVal of 'a ref * 'a list ;;

type 'a endo = Endo of ('a -> 'a);;

type 'a option = Some of 'a | None;;

(* Recursion *)

let rec iter_int n f x =
  if n < 1 then x else iter_int (n-1) f (f x);;

(*
let fib2 n =
  let l1 = ref 1 and l2 = ref 1 in
  iter_int n (fun _z -> let x = !l1 and y = !l2 in l1 := y; l2 := x+y; !l1) 1;;
*)

let fib2 n =
  let l1 = ref 1 in let l2 = ref 1 in
  iter_int n
    (fun _ -> let x = !l1 in let y = !l2 in l1 := y; l2 := x+y)
    ();
  !l1 ;;

fib2 1000 ;;

let rec iota m n =
  if n <= 0 then [] else m :: iota (m+1) (n-1) ;;

iota 1 10;;

(* need to fix the semantics of toplevel side effects *)
let r = ref [3] ;;
let z = r := 1 :: !r; !r;;
!r;;
let z' = z;;
let r = r in r := 1 :: !r; !r;;
let f () = z';;
let f2 () = append (f()) (f());;

let rec g x = if x > 0 then z else g 1;;

(* use toplevel value *)
let double_r () = r := 4 :: !r;;
double_r (); !r;;

(*
(* local recursion *)
let rev xs =
  let rec iter acc = function
    | [] -> acc
    | x::xs -> iter (x::acc) xs
  in
  iter [] xs;;
r := rev !r;;
*)

(* McCarthy 91 *)
let rec mccarthy_m n =
  if n > 100 then n - 10
  else mccarthy_m (mccarthy_m (n + 11));;

mccarthy_m 10;;

(* Takeuchi tarai *)
let rec tarai x y z =
  if y < x then tarai (tarai (x - 1) y z) (tarai (y - 1) z x) (tarai (z - 1) x y)
  else y;;

tarai 1 2 3;;

(* Exceptions *)

let failwith s = raise (Failure s);;
failwith "Bad";;

try if true then failwith "a" else "b" with Failure x -> x;;

(fun x -> raise x) (Failure "Hello");;

exception Restart of (unit -> int);;

try id (raise (Restart (fun x -> 3))) with Restart f -> f ();;

(* Fixpoints (without gas) *)

let omega n =
  let r = ref (fun x -> x) in
  let delta i = !r i in
  r := delta; delta n ;;

let fixpt f =
  let r = ref (fun x -> loop x) in
  let delta i = f !r i in
  r := delta; delta ;;

let fib =
  fixpt (fun fib n -> if n <= 1 then 1 else fib (n-1) + fib (n-2));;

fib 10;;

(* loops *)
omega 1;;

(* loops *)
fixpt (fun f -> f) 0;;
