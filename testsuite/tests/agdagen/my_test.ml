
let add x y = x + y

let mult_2 x y = 2 * x * y

type 'a my_opt = 
	| My_none
	| My_some of 'a

type even_int = 
	| Zorro
	| DoubleZ of even_int
	| Ddd of int


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

let add5 x =
	let aux y = y + 5 in
	aux x


let add7ifnon3 x = 
	let helper y = match y with
		| 4 -> 3
		| n -> n + 7
	in helper (x+1)

let f3 x = 
	let h y = match y with
		| 0 -> 0
		| n -> n+1
	in h x



let div x y = x /. y;;
let harmonic x y = 2. /. ((1. /. x) +. (1. /. y));;



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

let fact n =
  let i = ref n in
  let v = ref 1 in
  while !i > 0 do
    v := !v * !i;
    i := !i - 1
  done;
  !v


let ref' = ref;;


(* let polymorphism *)
let foo1 x =
  let id y = y in id id x;;

(* pure arity *)

let id h = h;;

let foo2 x = fun z -> x + z;;

let foo3 = id foo2;;

let foo2 x = id (fun y -> x);;

	

let incr r =
  let x = !r in r := x + 1;;

let oo = let r = ref 1 in incr r;;

let f x y z = x + y + z








let r = ref 5;;

let g x = x + !r;;

r := 1;;

let f y = y - !r
;;

let c = g 7;;

4;;

let rec concat l1 l2 = match l1 with
	| [] -> l2
	| x :: q -> concat q (x :: l2)



let u = ref [];;

let app l = concat l !u;;

u := 1 :: !u ;;

app [7]


let rec concat l1 l2 = match l1 with
	| [] -> l2
	| x :: q -> concat q (x :: l2)

let hy = concat

let ref2 = ref;;

let raise2 = raise;;

let emp _ = []
;;
type ('a, 'b) point = 
	| Point of 'a * 'b
;;

let scor7 = fun x -> Point (x, 7);;

let scorbis = scor7

let hoo = 7;;

let hoo2 _ = 7;;


let g = let y = ref 5 in !y;;

let carre x = x * x

let yy = carre 2;;

let rr = (if true then 4 else 5);;

(*let gsz = (while true do  u := !u done);;*)

let a x = x;;

let u = ref 3;;

u := !u + 1;;

let wz = u := !u + 1

let u = ref 3;;

let icr = u := !u + 1


let f1 x = ()

let f2 () = icr;;

let f3 x = wz 

let f6 () () = ()

let mm = ref 1;;

let wii = mm := 2 * !mm; 4;;

let f x = match x with
	| 1 -> "soleil"
	| 2 -> "soleil"
	| 3 -> "soleil"
	| _ -> "lune";;

let x = -7 + 5;;





;;