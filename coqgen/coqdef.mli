(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Jacques Garrigue, Nagoya University                        *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type error = Not_allowed of string
exception Error of Location.t * error

val not_allowed : ?loc:Location.t -> string -> 'a

type coq_sort = Type | Set | Prop

type coq_term =
    CTid of string
  | CTcstr of string
  | CTapp of coq_term * coq_term list
  | CTabs of string * coq_term option * coq_term
  | CTsort of coq_sort
  | CTprod of string option * coq_term * coq_term
  | CTmatch of coq_term * (string * coq_term) option *
      (coq_term * coq_term) list
  | CTann of coq_term * coq_term
  | CTlet of string * coq_term option * coq_term * coq_term
  | CTif of coq_term * coq_term * coq_term

type vernacular =
    CTdefinition of string * coq_term
  | CTfixpoint of string * coq_term
  | CTeval of coq_term
  | CTinductive of { name : string; args : (string * coq_term) list;
      kind : coq_term;
      cases : (string * (string * coq_term) list * coq_term option) list;
    }
  | CTverbatim of string

module Names = Misc.Stdlib.String.Set
val coq_vars : ?skip:(coq_term -> bool) -> coq_term -> Names.t
val coq_term_subst : coq_term Types.Vars.t -> coq_term -> coq_term

val ctid : string -> coq_term
val ctapp : coq_term -> coq_term list -> coq_term
val ctcstr : string -> coq_term list -> coq_term
val ctRet : coq_term -> coq_term
val ctBind : coq_term -> coq_term -> coq_term
val ctpair : coq_term -> coq_term -> coq_term

val ml_type : string
val ml_tid : coq_term
val mkcoqty : coq_term -> coq_term

type coq_type_desc = {
    ct_name: string;
    ct_arity: int; (* ML type arity *)
    ct_args: (int * string) list; (* Type vars *)
    ct_mlargs: (int * string) list; (* ML vars *)
    ct_type: coq_term;
    ct_def: (string list * (string * coq_term list) list) option;
       (* cases for comparison *)
    ct_constrs: (string * string) list;
    ct_compare: coq_term option;
    ct_maps: (int * string) list;
  }

type coq_term_desc = {
  ce_name : string;
  ce_type : Types.type_expr;
  ce_vars : Types.type_expr list;
  ce_rec : Asttypes.rec_flag;
  ce_purary : int;
}

type coq_env = {
  type_map : coq_type_desc Path.Map.t;
  term_map : coq_term_desc Path.Map.t;
  tvar_map : string Btype.TypeMap.t;
  ctvar_map : string Btype.TypeMap.t;
  top_exec : string list;
  coq_names : Names.t;
}

val empty_vars : coq_env
val add_type : Path.t -> coq_type_desc -> coq_env -> coq_env
val add_exception : Path.t -> string -> coq_term list -> coq_env -> coq_env
val add_term :
  ?toplevel:bool -> Path.t -> coq_term_desc -> coq_env -> coq_env
val add_tvar : Types.type_expr -> Names.elt -> coq_env -> coq_env
val add_ctvar : Types.type_expr -> Names.elt -> coq_env -> coq_env
val add_reserved : Names.elt -> coq_env -> coq_env
val refresh_tvars : coq_env -> coq_env
type tvar_map
val get_tvars : coq_env -> tvar_map
val set_tvars : coq_env -> tvar_map -> coq_env
val fresh_name : vars:coq_env -> Names.elt -> Names.elt
val fresh_opt_name : ?name:Names.elt -> coq_env -> Names.elt
val fresh_var_name : vars:coq_env -> Names.elt option -> Names.elt

val may_app : ('a -> 'b -> 'b) -> 'a option -> 'b -> 'b

