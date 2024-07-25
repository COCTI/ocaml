(* TEST
flags = "-coq"
compile_only = "true"
* setup-ocamlc.byte-build-env
** ocamlc.byte
*)
(* ../../../ocamlc -c -coq -I ../../../stdlib test.ml *)

let id x = x;;
let add m n = m+n;;

let comp f g = (f (g+1));;

let tuple_example a b c d = (a, (b, c), d);;

add 2 3;;