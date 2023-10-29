type 'a rlist = Nil | Cons of 'a * 'a rlist ref

let cycle a b =
  let r = ref Nil in
  let l = Cons (a, ref (Cons (b, r))) in
  r := l;
  l

let hd x = function Nil -> x | Cons (a, _) -> a
