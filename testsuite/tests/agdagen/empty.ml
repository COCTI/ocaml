(*type t1 = T1 of t2
and t2 = T2 of int;;

type ('a,'b) t3 = T3 of ('a, 'b) t4 * 'a * 'b
and ('a, 'b) t4 = T4 of ('a, 'b) t3 * 'a;;

let id x = x*)
(*
type t1 = T1 of t2
and t2 = T2 of t1;;

type t3 = T3 of t4
and t4 = T4 of int;;


let id x = x

let rec absurd x = absurd x;;

type 'a empty = |;;

type ('a, 'b, 'c) empty2 = |;;

(*let fake : int empty = absurd ();;*)

type hoo = 
  F of int

let u : hoo = F 7;;

let x : int = 5;;

let rec fac n = match n with
	| 0 -> 1
	| p -> p * fac (p-1);;

exception Zero_int

let add_non_zero n p = 
	match p with
		| 0 -> raise Zero_int
		| _ -> n + p;;

let add_non_zero2 n p =
	try 
		add_non_zero n p
	with
		Zero_int -> -1;;

let add x y = x + y

let b = if 3 < 5 then true else false;;

let g = ref 5;;

g := 7
*)



let max_v x y = if x < y then x else y

let abs_v x = if x < 0 then -x else x

type point = P of int * int

let norm p = match p with
	 P(x,y) -> max_v(abs_v(x)) (abs_v(y))

let distance p1 p2 = match p1 with
	| P(x1,y1) -> (match p2 with P(x2,y2) -> norm (P(x1-x2, y1-y2)));;


let square x = x * x













