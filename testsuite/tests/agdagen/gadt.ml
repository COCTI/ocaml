type 'a expr =
	| EBinop : (int -> int -> int) expr
	| EApp : ('a -> 'b) expr * 'a expr -> 'b expr
	| EInt : int -> int expr
	| EBool : bool -> bool expr
;;


let rec eval : type a. a expr -> a = function
	| EInt n -> n
	| EBool b -> b
	| EBinop -> (fun x y -> x + y)
	| EApp (f,x) -> (eval f) (eval x);;

let e1 = EApp (EApp (EBinop, EInt 5), EInt 8);;

(*eval e1;;

type ('a, 'b) tu =
	T of 'a * 'b;;

let f (x : ('a, 'b) tu) = match x with
	| _ -> 1;;

*)
;;
type 'uu uu =
    UU of 'uu;;


type 'a lisT =
  | E
  | C of 'a * 'a lisT

type 'a gadt_lisT =
  | E_g : 'r gadt_lisT
  | C_g : 'r * 'r gadt_lisT -> 'r gadt_lisT;;



type ('a, 'b) point =
  | NNpoint : int * int -> (int, int) point
  | FFpoint : float * float -> (float, float) point
  | NFpoint : int * float -> (int, float) point
  | FNpoint : float * int -> (float, int) point
  | OOpoint : 'a * 'b -> ('a, 'b) point;;

(*type 'a q =
	| Q1 : 'a * 'b * 'c -> 'a q
	| Q2 : 'b * 'a * 'c -> 'a q;;*)

type 'a q =
  | Q1 of 'a
  | Q2 : 'b * 'a * 'c -> 'a q

(*type ('a, 'b) uh =
  | Ch of 'a * (int, int) uh*)

type 'a twi =
  | TW of 'a * int * int

let f x = match x with
  | TW (_, m, n) -> m + n

type recu =
  | R of recu

let u = Q1 5

let add_int i1 i2 = match i1 with
  | EInt a -> begin match i2 with
    | EInt b -> a + b
    | _ -> 0 end
  | _ -> 0
