(* Some more tests *)

type t = E of exn

exception T of t

type t0 = O | T1 of t1
and t1 = T2 of t2
and t2 = T0 of t0

let x = T0 O;;

T2 x;;
