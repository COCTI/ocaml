open Coqdef

(*string -> ((coq_type_desc Path.Map.t) * (vernacular list)*)
let open_vlib (s : string) = 
  let vlib_channel = open_in s in 
  let type_map = input_value vlib_channel in
  let _ = input_value vlib_channel in
  let typedefs = input_value vlib_channel in 
  (*let type_list = List.map (fun (_, x) -> x) (Path.Map.bindings) in*)
  close_in vlib_channel;
  (type_map, typedefs)
(*just opens "s.vlib" and gets the type_map and typedefs stored in it*)

let _print_inductive (i : inductive) = print_endline ("inductive : "^i.name);;
(*useful for tests*)

let rec concat_lists l1 l2 = match l2 with
  | [] -> l1
  | e :: l -> if List.exists (fun x -> x = e) l then e :: concat_lists l1 l else concat_lists l1 l

(*let rec concat_constructor_lists l1 l2 = match l2 with
  |
*)

(*vernacular -> unit*)
let _print_vernacular = function 
  | CTdefinition _ -> print_endline "CTdefinition"
  | CTfixpoint _ -> print_endline "CTfixpoint"
  | CTeval _ -> print_endline "CTeval"
  | CTinductive _ -> print_endline "CTinductive"
  | CTverbatim _ -> print_endline "CTverbatim"
(*useful for tests*)

(* vernacular list -> vernacular list -> vernacular*)
let concat_mlexns e1 e2 = 
  let cases = (match e1, e2 with 
               | [CTinductive [t1]], [CTinductive [t2]] -> concat_lists t1.cases t2.cases
               | [CTinductive [t1]], [] -> t1.cases (*print_vernacular t1; print_vernacular t2; t1,*)  (*apparently the list has strictly more (or less) than one element *)
               | [], [CTinductive [t2]] -> t2.cases
               | [], [] -> []
               | _ -> assert false) in
  CTinductive [{ name = "ml_exns"; args = []; kind = CTsort Type; cases = cases}]
(*used in a very particular setting, we assume that the two lists have at most one element, and just debug prints if not
  The function is used to create a new "ml_exns" definition from two, in the case where there is an exception defined in one of the two files*)

(*vernacular list -> unit*)
let rec _printlist (l : vernacular list) = match l with
  | [] -> ()
  | t :: l -> (match t with | CTinductive i_list -> List.iter (_print_inductive) i_list | _ -> assert false); _printlist l
(*useful for tests*)


(*coq_type_desc Path.Map.t -> unit*)
let _print_map (m : coq_type_desc Path.Map.t) = List.iter (fun x -> print_endline (snd x).ct_name) (Path.Map.bindings m)
(*useful for tests*)

(*vernacular -> bool*)
let is_exn v = match v with 
  | CTinductive [i] -> (i.name = "ml_exns")
  | _ -> false

let remove_exns t = List.partition is_exn t
(*this makes sure that ml_exn is only defined once, this is probably a temporary solution, but it works for now (I think?)*)

(*coq_type_desc -> coq_type_desc -> coq_type_desc*)
(*let merge_exns c1 c2 = failwith "TODO"
*)

let concat_vlib (m1, t1) (m2, t2) = 
  (*let m1_exn = Path.Map.find Predef.path_exn m1 in
  let m2_exn = Path.Map.find Predef.path_exn m2 in
  let m1 = Path.Map.remove Predef.path_exn m1 in
  let m2 = Path.Map.remove Predef.path_exn m2 in
  *)
  let m = Path.Map.union (fun _ a _ -> Some a) m1 m2 in (*this is a source of bug, since when two types have the same name, but in different files, we might want to keep the two arguments...*)
  (*since we made modifications on the stdlib access, there should not be any conflict anymore*)
  (*let type_list = List.map (fun (_, x) -> x) (Path.Map.bindings m) in*)

  (*print_endline "t1 : "; List.iter print_vernacular t1; *)
  let e1, t1 = remove_exns t1 in
  (*print_endline "t2 : "; List.iter print_vernacular t2; *)
  let e2, t2 = remove_exns t2 in 
  let t = List.append t1 t2 in
  let t = (concat_mlexns e1 e2) :: t in

  (m, t)

(*string list -> (Coqdef.coq_type_desc Path.Map.t) * (Coqdef.vernacular list)*)
let rec merge_vlibs = function (*could have used fold_left here*)
  | [] -> (Path.Map.empty, [])
  | s :: l -> concat_vlib (open_vlib s) (merge_vlibs l)
(*string list -> Coqdef.vernacular list*)
let to_gallina vlib_list =
  match (merge_vlibs vlib_list) with
  | (type_map, typedefs) -> Coqgen.make_v (Path.Map.union (fun _ a _ -> Some a) Coqlib.lib_vars.type_map type_map) typedefs 

(*string list -> unit*)
let emit_gallina vlib_list = 
  let cwd = Sys.getcwd () in (*maybe later change this to match the -o flag?*)
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