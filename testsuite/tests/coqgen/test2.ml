(* Some more tests *)

type t = E of exn

exception T of t

type t0 = O | T1 of t1
and t1 = T2 of t2
and t2 = T0 of t0

let x = T0 O;;

T2 x;;

let failwith s = raise (Failure s);;

let rec length_aux len = function
    [] -> len
  | _::l -> length_aux (len + 1) l

let length l = length_aux 0 l

let cons a l = a::l

let hd = function
    [] -> failwith "hd"
  | a::_ -> a

(*type student = { name: string; mutable year: int }

Record student_val := { name: string; year: int }.
Definition student := loc student_val.

type _ tag = Int : int tag | Bool : bool tag

let rec f : type a. a tag -> bool list -> a = fun tag l ->
  match tag with
  | Int -> 3
  | Bool -> true
*)
