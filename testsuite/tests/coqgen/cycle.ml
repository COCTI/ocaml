type 'a rlist = Nil | Cons of 'a * 'a rlist ref

let cycle a b =
  let r = ref Nil in
  let l = Cons (a, ref (Cons (b, r))) in
  r := l;
  l

let hd x = function Nil -> x | Cons (a, _) -> a
let tl = function Nil -> Nil | Cons (_, l) -> !l

let rec iappend l1 l2 =
  match l1 with
  | Nil -> l2
  | Cons (a, l1') -> l1' := iappend !l1' l2; l1
