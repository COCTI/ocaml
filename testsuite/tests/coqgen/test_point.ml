type point = Point of int * int;;

let make_point x y = Point (x, y);;

let add_point = function
  | Point (x, y) -> x + y;;

add_point (Point (2, 3));;