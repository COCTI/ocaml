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

open Types
open Agdadef

val transl_type :
  loc:Location.t ->
  env:Env.t ->
  vars:coq_env -> ?def:bool -> type_expr -> coq_term
val transl_coq_type :
  loc:Location.t ->
  env:Env.t -> vars:coq_env -> type_expr -> coq_term

val make_subst :
  mkcoq:('a -> coq_term) ->
  mkml: ('a -> coq_term) ->
  coq_type_desc -> 'a list -> coq_term Vars.t

val find_instantiation :
  loc:Location.t ->
  env:Env.t ->
  vars:coq_env ->
  coq_term_desc -> type_expr -> coq_term list

val transl_typedecls :
  env:Env.t ->
  vars:coq_env ->
  Typedtree.type_declaration list -> vernacular * coq_env

val transl_exception :
  loc:Location.t ->
  env:Env.t ->
  vars:coq_env ->
  Typedtree.extension_constructor -> coq_env

val close_type : type_expr -> unit

val enter_free_variables :
  loc:Location.t ->
  vars:coq_env ->
  type_expr ->
  type_expr list * Names.elt list * coq_env
