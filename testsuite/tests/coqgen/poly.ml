let g x = ()
let f () =  g [] ;;

let h () =
  let r = ref [] in
  r := [];
  r := [] ;;

type ('a,'b) pair = Pair of 'a * 'b

let k () =
  match (fun x -> x) with
  | f -> Pair (f 1, f true) ;;
