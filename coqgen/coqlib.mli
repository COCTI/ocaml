open Coqdef

val lib_vars : coq_env

val update_dep_list : string -> string list

val overwrite_dep_list : coq_env -> coq_env

val env : (string, coq_type_desc Path.Map.t * coq_term_desc Path.Map.t)Hashtbl.t

val find_types : Path.t -> coq_env -> coq_type_desc

val find_terms : Path.t -> coq_env -> coq_term_desc