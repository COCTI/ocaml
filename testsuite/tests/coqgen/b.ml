type point = Point of float * float;;

let y = A.Point (2, 3);;
let z = Point (2., 3.);;

let f x = x;;

let g x = match x with
  | A.Point (_, _) -> f x

let h y = match y with
  | Point (_, _) -> f y