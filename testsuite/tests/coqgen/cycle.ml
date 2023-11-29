type 'a rlist = Nil | Cons of 'a * 'a rlist ref

let cycle a b =
  let r = ref Nil in
  r := Cons (a, ref (Cons (b, r)));
  r

let hd x r = match !r with Nil -> x | Cons (a, _) -> a
let tl r = match !r with Nil -> r | Cons (_, l) -> l
let rec drop n l = if n <= 0 then l else tl l
let rec rseqn n a r =
  if n <= 0 then r else ref (Cons (a, rseqn (n-1) a r))

let cyclen n a b =
  let r = ref Nil in
  r := Cons (a, rseqn n b r);
  r

let rec iappend l1 l2 =
  match l1 with
  | Nil -> l2
  | Cons (a, l1') -> l1' := iappend !l1' l2; l1
