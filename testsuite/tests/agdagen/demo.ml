let x = 7;;

let rec fac n = match n with
 | 0 -> 1
 | n -> n * fac (n-1)

exception EqualTo7

let id_if_not_7 x = match x with
	| 7 -> raise EqualTo7
	| x -> x

let u = ref 3;;

u := !u + 1

type ('a,'b) tree = Leaf of 'a | Node of ('a,'b) tree * 'b * ('a,'b) tree ;;

let mknode t1 t2 = Node (t1, 0, t2) ;;