(*

let add x y = x + y

type 'a m =
	| E
	| C of 'a * 'a m

let tf lis = match lis with
	| E -> C(0, C(0, E))
	| C (x, E) -> C(x, C(0, E))
	| C (x, C(y, _)) -> C(x, C(y, E))

let x = match 0 with
	| 0 -> 1
	| 1 -> 2
	| 2 -> 3
	| _ -> 5

let x = let g y = match y with
	| 0 -> 1
	| 1 -> 2
	| 2 -> 3
	| _ -> 5 in g 0

let f6 u v =
	add 3 4;
	add u v

;;
*)



(*

let id h = h;;

let foo2 x = fun z -> x + z;;

let foo3 = id foo2;;

*)



let u = ref 3;;
