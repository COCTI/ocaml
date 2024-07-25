(* type1 *)
type 'a expr =
  | EBinop : (int -> int -> int) expr
  | EApp : ('a -> 'b) expr * 'a expr -> 'b expr
  | EInt : int -> int expr
  | EBool : bool -> bool expr
;;

(* ex1 *)
let rec eval : type a. a expr -> a = function
  | EInt n -> n
  | EBool b -> b
  | EBinop -> (fun x y -> x + y)
  | EApp (f,x) -> (eval f) (eval x)
;;

(* ex2 *)
let e1 = EApp (EApp (EBinop, EInt 5), EInt 8)
;;

(* ex3 *)
type 'a q =
  | Q1 of 'a
  | Q2 : 'b * 'a * 'c -> 'a q
;;

