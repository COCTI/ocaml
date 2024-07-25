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

type term_props = {
  pterm : Agdadef.coq_term;
  prec : Asttypes.rec_flag;
  pary : int;
}

val transl_structure :
  vars:Agdadef.coq_env -> final_env:Env.t ->
  Typedtree.structure_item list -> Agdadef.vernacular list * Agdadef.coq_env 
