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

val make_v :
  Coqdef.coq_type_desc Path.Map.t (*Coqdef.coq_type_desc list*) -> Coqdef.vernacular list -> Coqdef.vernacular list 

val transl_implementation :
  string -> Typedtree.structure -> (*Coqdef.vernacular list * *)Coqdef.vernacular list * string list (*the string list corresponds to the dependence list of the translated file*)
