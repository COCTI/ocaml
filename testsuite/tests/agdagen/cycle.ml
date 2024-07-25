type 'a rlist = Nil | Cons of 'a * 'a rlist ref

let cycle a b =
  let r = ref Nil in
  r := Cons (a, ref (Cons (b, r)));
  r

let rhd x r = match !r with Nil -> x | Cons (a, _) -> a
let rtl r = match !r with Nil -> r | Cons (_, l) -> l
let rec rdrop n l = if n <= 0 then l else rtl l
let rec mkrlist l r =
  match l with [] -> r | a :: l -> ref (Cons (a, mkrlist l r))

let cyclel a l =
  let r = ref Nil in
  r := Cons (a, mkrlist l r);
  r

let rec iappend l1 l2 =
  match l1 with
  | Nil -> l2
  | Cons (a, l1') -> l1' := iappend !l1' l2; l1
