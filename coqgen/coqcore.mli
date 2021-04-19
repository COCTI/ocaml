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
  pterm : Coqdef.coq_term;
  prec : Asttypes.rec_flag;
  pary : int;
}

val transl_structure :
  vars:Coqdef.coq_env ->
  Typedtree.structure_item list -> Coqdef.vernacular list * Coqdef.coq_env
