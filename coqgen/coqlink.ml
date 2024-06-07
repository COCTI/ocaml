open Coqdef

let open_vlib (s : string) = 
  let vlib_channel = open_in s in 
  let type_map = input_value vlib_channel in
  let _ = input_value vlib_channel in
  let typedefs = input_value vlib_channel in 
  close_in vlib_channel;
  (type_map, typedefs)

let _print_inductive (i : inductive) = print_endline ("inductive : "^i.name);;

let rec concat_lists l1 l2 = match l2 with
  | [] -> l1
  | e :: l -> if List.exists (fun x -> x = e) l then e :: concat_lists l1 l else concat_lists l1 l


let _print_vernacular = function 
  | CTdefinition _ -> print_endline "no segfault"; print_endline "CTdefinition"
  | CTfixpoint _ -> print_endline "no segfault"; print_endline "CTfixpoint"
  | CTeval _ -> print_endline "no segfault"; print_endline "CTeval"
  | CTinductive _ -> print_endline "no segfault"; print_endline "CTinductive"
  | CTverbatim _ -> print_endline "no segfault"; print_endline "CTverbatim"

(* vernacular list -> vernacular list -> vernacular*)
let concat_mlexns e1 e2 = 
  let cases = (match e1, e2 with 
               | [CTinductive [t1]], [CTinductive [t2]] -> concat_lists t1.cases t2.cases
               | [CTinductive [t1]], [] -> t1.cases (*print_vernacular t1; print_vernacular t2; t1,*)  (*apparently the list has strictly more (or less) than one element *)
               | _ -> print_endline ("e1 length : " ^ Int.to_string (List.length e1)); print_endline ("e2 length : " ^ Int.to_string (List.length e2)); assert false) in
  (*let cases1 = t1.cases in
  let cases2 = t2.cases in*)
  CTinductive [{ name = "ml_exns"; args = []; kind = CTsort Type; cases = cases (*concat_lists cases1 cases2*)}]

(*vernacular list -> unit*)
let rec _printlist (l : vernacular list) = match l with
  | [] -> ()
  | t :: l -> (match t with | CTinductive i_list -> List.iter (_print_inductive) i_list | _ -> assert false); _printlist l

(*vernacular -> unit*)


let _aux _key a _b = Some a

let _print_map (m : coq_type_desc Path.Map.t) = List.iter (fun x -> print_endline (snd x).ct_name) (Path.Map.bindings m)


(*vernacular -> bool*)
let is_exn v = match v with 
  | CTinductive [i] -> (i.name = "ml_exns")
  | _ -> false

let remove_exns t = List.partition is_exn t

let concat_vlib (m1, t1) (m2, t2) = 
  let m = Path.Map.union (fun _ a _ -> Some a) m1 m2 in
  (*print_endline "t1 : "; List.iter print_vernacular t1; *)
  let e1, t1 = remove_exns t1 in
  (*print_endline "t2 : "; List.iter print_vernacular t2; *)
  let e2, t2 = remove_exns t2 in 
  let t = List.append t1 t2 in
  let t = (concat_mlexns e1 e2) :: t in

  (m, t)

(*string list -> Coqdef.coq_type_desc Path.Map.t * Coqdef.vernacular list*)
let rec merge_vlibs = function
  | [] -> (Path.Map.empty, [])
  | s :: l -> concat_vlib (open_vlib s) (merge_vlibs l)
(*string list -> Coqdef.vernacular list*)
let to_gallina vlib_list =
  match (merge_vlibs vlib_list) with
  | (type_map, typedefs) -> Coqgen.make_v type_map typedefs 

(*string list -> unit*)
let emit_gallina vlib_list = 
  let cwd = Sys.getcwd () in (*pretty bad, but good enough for the moment*)
  let v_name = cwd ^ "/project_lib.v" in
  print_endline v_name;
  let vfile = open_out v_name in
  let open Format in
  let ppf = formatter_of_out_channel vfile in
  fprintf ppf "@[<v>";
  Coqprint.emit_gallina "Project_lib" ppf (to_gallina vlib_list); 
  fprintf ppf "@]@.";
  close_out vfile


(*let emit_gallina i ct =
    let v_name = i.output_prefix ^ ".v" in
    let vfile = open_out v_name in
    let open Format in
    let ppf = formatter_of_out_channel vfile in
    fprintf ppf "@[<v>";
    Coqprint.emit_gallina i.module_name ppf ct;
    fprintf ppf "@]@.";
    close_out vfile
*)