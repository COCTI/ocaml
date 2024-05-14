(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2002 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Misc
open Compile_common

let tool_name = "ocamlc"

let with_info =
  Compile_common.with_info ~native:false ~tool_name

let interface ~source_file ~output_prefix =
  with_info ~source_file ~output_prefix ~dump_ext:"cmi" @@ fun info ->
  Compile_common.interface info

(** Bytecode compilation backend for .ml files. *)

let to_bytecode i Typedtree.{structure; coercion; _} =
  (structure, coercion)
  |> Profile.(record transl)
    (Translmod.transl_implementation i.module_name)
  |> Profile.(record ~accumulate:true generate)
    (fun { Lambda.code = lambda; required_globals } ->
       lambda
       |> print_if i.ppf_dump Clflags.dump_rawlambda Printlambda.lambda
       |> Simplif.simplify_lambda
       |> print_if i.ppf_dump Clflags.dump_lambda Printlambda.lambda
       |> Bytegen.compile_implementation i.module_name
       |> print_if i.ppf_dump Clflags.dump_instr Printinstr.instrlist
       |> fun bytecode -> bytecode, required_globals
    )

let emit_bytecode i (bytecode, required_globals) =
  let cmofile = cmo i in
  let oc = open_out_bin cmofile in
  Misc.try_finally
    ~always:(fun () -> close_out oc)
    ~exceptionally:(fun () -> Misc.remove_file cmofile)
    (fun () ->
       bytecode
       |> Profile.(record ~accumulate:true generate)
         (Emitcode.to_file oc i.module_name cmofile ~required_globals);
    )

let to_gallina i Typedtree.{structure; _} =
  Coqgen.transl_implementation i.module_name structure

let emit_gallina i ct =
  let v_name = i.output_prefix ^ ".v" in
  let vfile = open_out v_name in
  let open Format in
  let ppf = formatter_of_out_channel vfile in
  fprintf ppf "@[<v>";
  Coqprint.emit_gallina i.module_name ppf ct;
  fprintf ppf "@]@.";
  close_out vfile

(*let emit_gallina_lib i ct =
  let v_name = i.output_prefix ^ ".vlib" in
  let vfile = open_out v_name in
  let open Format in
  let ppf = formatter_of_out_channel vfile in
  fprintf ppf "@[<v>";
  Coqprint.emit_gallina i.module_name ppf ct;
  fprintf ppf "@]@.";
  close_out vfile
*)

(*
  let rec end_of_list l = match l with
    | [] -> ""
    | [s] -> s
    | _ :: l -> end_of_list l

  let relative_path s = end_of_list (String.split_on_char '/' s) (*returns name of the file, in its directory*)
*)

let implementation ~start_from ~source_file ~output_prefix =
  let backend info typed =
    if !Clflags.compile_to_coq then 
      let gallina_lib, gallina, dep_list = to_gallina info typed in (*would be easy here to give the dependencies, like a list of strings or something, just the names of the files I want to add*)
      let lib_name = info.output_prefix ^"_lib" in
      emit_gallina info ((List.map (fun s -> Coqdef.CTverbatim ("Require Import " ^ s ^ ".")) dep_list) @ gallina); (*adding all of the necessary dependencies at the start here*) (*probably should also add the "project_lib" file at some point?*)
      emit_gallina {info with output_prefix = lib_name} gallina_lib;
    else
      let bytecode = to_bytecode info typed in
      emit_bytecode info bytecode
  in
  with_info ~source_file ~output_prefix ~dump_ext:"cmo" @@ fun info ->
  match (start_from : Clflags.Compiler_pass.t) with
  | Parsing -> Compile_common.implementation info ~backend
  | _ -> Misc.fatal_errorf "Cannot start from %s"
           (Clflags.Compiler_pass.to_string start_from)
