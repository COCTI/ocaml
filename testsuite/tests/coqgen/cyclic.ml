type 'a rlist = Nil | Cons of 'a * 'a rlist ref

let cycle a b =
  let r = ref Nil in
  let l = Cons (a, ref (Cons (b, r))) in
  r := l;
  l

let l = cycle true false

let hd def = function
  | Nil -> def
  | Cons (a, _) -> a

let tl = function
  | Nil -> Nil
  | Cons (_, t) -> !t
