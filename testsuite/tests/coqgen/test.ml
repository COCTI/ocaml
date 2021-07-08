(* TEST
flags = "-coq"
compile_only = "true"
* setup-ocamlc.byte-build-env
** ocamlc.byte
*)
(* ../../../ocamlc -c -coq -I ../../../stdlib test.ml *)

let ref' = ref;;

let id h = h;;

let incr r =
  let x = !r in r := x + 1;;

let r = ref 1 in incr r;;

let rec loop h = loop h;;

let rec fib n =
  if n <= 1 then 1 else fib (n-1) + fib (n-2);;

fib 10;;

let rec ack m n =
  if m <= 0 then n + 1 else
  if n <= 0 then ack (m-1) 1 else
  ack (m-1) (ack m (n-1)) ;;

ack 3 7;;

"hellas" < "hello";;
let cmp = 'a' < 'A';;

let rec map f l =
  match l with
  | [] -> []
  | a :: l -> f a :: map f l
;;

map (fun x -> x + 1) [3;2;1] ;;

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

(* need to fix the semantics of toplevel side effects *)
let r = ref [3] ;;
let z = r := 1 :: !r; !r;;
!r;;
z;;
let r = r in r := 1 :: !r; !r;;

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

(* loops *)
omega 1;;

(* loops *)
fixpt (fun f -> f) 0;;
