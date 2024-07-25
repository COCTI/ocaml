open Coqdef

(*coq_env*)
let lib_vars = Coqinit.lib_vars

let dep_list_ref : string list ref = ref []
(*is updated whenever a new dependence is needed.
vars.dep_list is overwritten before every return of transl_structure to makes sure it stays up to date for "coqgen.ml".*)

(*string -> string list*)
let update_dep_list (s : string) = if List.exists (fun x -> x = s) !dep_list_ref then !dep_list_ref else s :: (!dep_list_ref)
(*dep_list_ref := update_dep_list s; when you need add a new element*)

(*coq_env -> coq_env*)
let overwrite_dep_list (vars : coq_env) = {vars with dep_list = !dep_list_ref}
(*called at the end of any return in transl_structure*)

let env : (string, coq_type_desc Path.Map.t * coq_term_desc Path.Map.t)Hashtbl.t = Hashtbl.create 42;;
(*table linking the name of files with their ".vlib".
used to do separate compilation*)

(*
(*string -> (coq_type_desc Path.Map.t * vernacular list)*)
let open_vlib (s : string) = 
  let vlib_channel = open_in s in 
  let type_map = input_value vlib_channel in
  let _ = input_value vlib_channel in
  let typedefs = input_value vlib_channel in 
  close_in vlib_channel;
  (type_map, typedefs)
(*just opens "s.vlib" and gets the type_map and typedefs stored in it*)
*)

(*Path.t -> string list*)
let rec split_path_aux (p : Path.t) = match p with
    | Pident i -> [(Ident.name i)]
    | Pdot (m, s) -> s :: (split_path_aux m)
    | _ -> assert false

(*Path.t -> string * (string list)*)
let split_path (p : Path.t) = 
  let l =  List.rev (split_path_aux p) in
  (match l with 
  | file_name :: elt -> file_name, elt 
  | _ -> assert false)
(*separated the path into the corresponding (file_name * (submodule arborescence list))*)

(*string -> unit*)
let add_env (file_name : string) =
  (*print_endline (String.concat "; " (Load_path.get_paths ()));*)
  let vlib_channel = open_in (Load_path.find_uncap ((file_name) ^ ".vlib")) in
  let type_map = input_value vlib_channel in
  let term_map = input_value vlib_channel in
  Hashtbl.add env file_name (type_map, term_map);
  close_in vlib_channel
(*adds the "file_name.vlib" maps to the environment*)

(*string -> (coq_type_desc Path.Map.t * coq_term_desc Path.Map.ts)*)
let get_env (file_name : string) = 
  dep_list_ref := update_dep_list (String.lowercase_ascii file_name); 
  try (Hashtbl.find env file_name) with Not_found -> 
    add_env file_name;
    Hashtbl.find env file_name
(*gets the corresponding maps, and adds it if necessary. In both cases, calls update_dep_list to add it to the dependence list.*)

(*coq_type_desc Path.Map.t -> string -> coq_type_desc*)
let find_type (type_map : coq_type_desc Path.Map.t) (elt : string list) = 
  (*print_endline ("current type_map : "); List.iter print_endline (List.map (fun (a, _) -> Path.name a) (Path.Map.bindings type_map));*)
  List.assoc (String.concat "." elt) (List.map (fun (a, b) -> (Path.name a, b)) (Path.Map.bindings type_map))
(*coq_env -> string -> coq_term_desc*)
let find_term (term_map : coq_term_desc Path.Map.t) (elt : string list) = 
  List.assoc (String.concat "." elt) (List.map (fun (a, b) -> (Path.name a, b)) (Path.Map.bindings term_map))
(*these functions use strings to match the path map*)
(*compares the path name and the string list corresponding to a "module path". raises Not_found if it doesn't find the element.*)

(*Path.t -> coq_type_desc*)
let find_type_stdlib (p : Path.t) = Path.Map.find p lib_vars.type_map
(*Path.t -> coq_term_desc*)
let find_term_stdlib (p : Path.t) = Path.Map.find p lib_vars.term_map
(*not written yet, should look at the translated stdlib folder for the moment*)
  
(*Path.t -> coq_env -> coq_type_desc*)
let find_types (p : Path.t) (vars : coq_env) = 
  try (Path.Map.find p vars.type_map)
  with Not_found -> (match p with 
    | Pident _ -> find_type_stdlib p
    | Pdot _ -> (try 
      let file_name, elt = split_path p in
      find_type (fst (get_env file_name)) elt 
      with Not_found -> find_type_stdlib p)
    | _ -> assert false)

(*Idea : handling lists instead of the maps. Do you think there will be any problem with that?
- The goal is to just extract the bindings, and only handle the paths. But I would have a problem with the exceptions then. Since I need to modify typedefs right? No I don't.*)
(*look at how the exceptions are defined, Do I need the existance of ml_exns to handle the exceptions? I don't think so, I think no one verifies if the "ml_" version of a type exists...*)
(**)

(*Path.t -> coq_env -> coq_term_desc*)
let find_terms (p : Path.t) (vars : coq_env) = 
  try (Path.Map.find p vars.term_map)
  with Not_found -> (match p with 
    | Pident _ -> find_term_stdlib p
    | Pdot _ -> (try 
      let file_name, elt = split_path p in
      {(find_term (snd (get_env file_name)) elt) with ce_name = (String.uncapitalize_ascii (Path.name p))} (*probably add "file_name." at the beginning, to avoid ambiguity *)
      with Not_found -> find_term_stdlib p)
    | _ -> assert false)
(*both functions follow the following algorithm:
  - look in current environment
  - if not found, look in the environment of the corresponding first module
  - if not found, look in standard library
  - if not found, raise Not_found*)

