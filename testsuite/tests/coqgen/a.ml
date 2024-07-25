type point = Point of int * int;;

type t1 = T1 of t2
and t2 = T2 of t3
and t3 = T3 of t4
and t4 = T4 of t5
and t5 = T5 of t6
and t6 = T6 of t3

exception Return1 of string;;
exception Return2 of (unit -> string);;
exception Return3 of (string -> unit);;

