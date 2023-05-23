(* fact by forloop *)
let fact_for63 n =
  let v = ref 1 in
  for i = 1 to n do
    v := !v * i
  done;
  !v;;

fact_for63 10;;
