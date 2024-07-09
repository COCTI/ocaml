type 'a point = Point of 'a * 'a;;


let x = A.Point (2, 3);;
let y = B.Point (2., 3.);;
let z = Point ("2", "3");;

let f x = x

let g x = match x with
  | A.Point (_, _) -> f x

let h y = match y with
  | B.Point (_, _) -> f y

let i z = match z with
  | Point (_, _) -> f z