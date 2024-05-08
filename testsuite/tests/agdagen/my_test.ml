let add x y = x + y

let mult_2 x y = 2 * x * y

type 'a my_opt = 
	| My_none
	| My_some of 'a

type even_int = 
	| Zorro
	| DoubleZ of even_int
	| D of int


type ('a, 'b, 'c, 'd) quadruplet = 
   | Quatuor of 'a * 'b * 'c * 'd


let arrow () = 
	"huhu"

type 'a my_list =
	| E
	| Cons of 'a * 'a my_list

let two_first lis = match lis with
	| E -> Cons(0, Cons(0, E))
	| Cons (x, E) -> Cons(x, Cons(0, E))
	| Cons (x, Cons(y, _)) -> Cons(x, Cons(y, E))


let f1 x = x

let f2 x y z u = x + y * (fun t v -> 2*t*v) z u

let ignore _ = ()

let g x =
	let u = 2 in x + u

let g2 x =
	let u = 5 in x - u


let f3 x y =
	ignore x;
	ignore y;
	()
;;