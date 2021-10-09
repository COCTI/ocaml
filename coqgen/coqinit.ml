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

open Asttypes
open Types
open Btype
open Coqdef

let stdlib = Path.Pident (Ident.create_persistent "Stdlib")
let coqgen = Path.Pident (Ident.create_persistent "coqgen")
let stdlib_ref = Path.Pdot (stdlib, "ref")
let newgenconstr p tl = newgenty (Tconstr (p, tl, ref Mnil))
let newgenarrow t1 t2 = newgenty (Tarrow (Nolabel, t1, t2, Cok))
let ident_empty = Ident.create_predef "empty"
let path_empty = Path.Pident ident_empty

let xy = [CTid"x"; CTid"y"]

let ctd = { ct_name = ""; ct_arity = 0; ct_args = []; ct_mlargs = [];
            ct_type = CTid ""; ct_def = None; ct_constrs = [];
            ct_compare = None }

let init_type_map vars =
  List.fold_left
    (fun map (rt, lid, desc) ->
      let path = List.fold_left (fun m s -> Path.Pdot (m, s)) rt lid in
      add_type path desc map)
    vars
  [
   (stdlib, ["ref"],
    {ctd with ct_name = "ml_ref";
     ct_arity = 1; ct_mlargs = [0, "a"];
     ct_type = CTapp (CTid "loc", [CTid "a"]);
     ct_compare =
     Some (CTapp (CTid"compare_ref", CTid"compare_rec" :: CTid"T1" :: xy))});
   (path_empty, [],
    {ctd with ct_name = "ml_empty"; ct_type = CTid "empty"});
   (Predef.path_int, [],
    {ctd with ct_name = "ml_int";
     ct_type = CTid "Int63.int";
     ct_compare = Some (ctRet (CTapp (CTid"Int63.compare", xy)))});
   (Predef.path_char, [],
    {ctd with ct_name = "ml_char";
     ct_type = CTid "Ascii.ascii";
     ct_compare = Some (ctRet (CTapp (CTid"compare_ascii", xy)))});
   (Predef.path_string, [],
    {ctd with ct_name = "ml_string";
     ct_type = CTid "String.string";
     ct_compare = Some (ctRet (CTapp (CTid"compare_string", xy)))});
   (Predef.path_unit, [],
    {ctd with ct_name = "ml_unit";
     ct_type = CTid "unit";
     ct_def = Some ([], ["tt", []]);
     ct_constrs = ["()", "tt"];
     ct_compare = None});
   (Predef.path_bool, [],
    {ctd with ct_name = "ml_bool";
     ct_type = CTid "bool";
     ct_constrs = List.map (fun x -> (x,x)) ["true"; "false"];
     ct_compare = Some (ctRet (CTapp (CTid"Bool.compare", xy)))});
   (Predef.path_list, [],
    {ctd with ct_name = "ml_list";
     ct_arity = 1; ct_args = [0, "a"];
     ct_constrs = [("[]", "@nil"); ("::", "@cons")];
     ct_type = CTapp (CTid "list", [CTid "a"]); ct_def = None;
     ct_compare = Some
       (CTapp (CTid"compare_list",
               CTid"compare_rec" :: CTid "T1" :: xy))});
   (Predef.path_array, [],
    {ctd with ct_name = "ml_array";
     ct_arity = 1; ct_mlargs = [0, "a"];
     ct_type = CTapp (CTid"loc", [CTapp (CTid"ml_array_t", [CTid"a"])]);
     ct_compare = Some
       (CTapp (CTid"compare_ref",
               CTid"compare_rec" ::
               ctapp (CTid"ml_array_t") [CTid "T1"] :: xy))});
   (Path.Pident (Ident.create_predef "array_t"), [],
    {ctd with ct_name = "ml_array_t";
     ct_arity = 1; ct_args = [0, "a"];
     ct_constrs = [("ArrayVal", "ArrayVal")];
     ct_type = CTapp (CTid"array_t", [CTid"a"]);
     ct_def = Some (["a"], ["ArrayVal", [CTapp(CTid"ml_list", [CTid "a"])]])});
   (Predef.path_exn, [],
    {ctd with ct_name = "ml_exn";
     ct_type = CTid "ml_exns";
     ct_constrs = List.map (fun x -> (x,x))
       ["Invalid_argument"; "Failure"; "Not_found"];
     ct_def = Some ([], ["Invalid_argument", [CTid"ml_string"];
                         "Failure", [CTid"ml_string"]; "Not_found", []])});
   (coqgen, ["arrow"],
    {ctd with ct_name = "ml_arrow";
     ct_arity = 2; ct_args = [0, "a"; 1, "b"];
     ct_type = CTprod (None, CTid"a",
                       CTapp (CTid"M", [CTid"b"]))});
  ]

let init_term_map vars =
  let int_to_int = newgenarrow Predef.type_int Predef.type_int in
  let int_to_int_to_int = newgenarrow Predef.type_int int_to_int in
  List.fold_left
    (fun map (lid, desc) ->
      let path = List.fold_left (fun m s -> Path.Pdot (m, s)) stdlib lid in
      add_term path desc map)
    vars (
  [
   (["*h"],
    {ce_name = "h";
     ce_type = Predef.type_int;
     ce_vars = [];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   (["ref"],
    let tv = newgenvar () in
    {ce_name = "newref";
     ce_type = newgenarrow tv (newgenconstr stdlib_ref [tv]);
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   (["!"],
    let tv = newgenvar () in
    {ce_name = "getref";
     ce_type = newgenarrow (newgenconstr stdlib_ref [tv]) tv;
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   ([":="],
    let tv = newgenvar () in
    {ce_name = "setref";
     ce_type = newgenarrow (newgenconstr stdlib_ref [tv])
       (newgenarrow tv Predef.type_unit);
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 2});
   (["Array";"make"],
    let tv = newgenvar () in
    {ce_name = "newarray";
     ce_type = newgenarrow Predef.type_int
       (newgenarrow tv (Predef.type_array tv));
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 2});
   (["Array";"get"],
    let tv = newgenvar () in
    {ce_name = "getarray";
     ce_type = newgenarrow (Predef.type_array tv)
       (newgenarrow Predef.type_int tv);
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 2});
   (["Array";"set"],
    let tv = newgenvar () in
    {ce_name = "setarray";
     ce_type = newgenarrow (Predef.type_array tv)
       (newgenarrow Predef.type_int (newgenarrow tv Predef.type_unit));
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 3});
   (["failwith"],
    let tv = newgenvar () in
    {ce_name = "failwith";
     ce_type = newgenarrow Predef.type_string tv;
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   (["invalid_arg"],
    let tv = newgenvar () in
    {ce_name = "invalid_arg";
     ce_type = newgenarrow Predef.type_string tv;
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
  ] @
  List.map
    (fun (ml, coq) ->
      [ml],
      {ce_name = coq;
       ce_type = int_to_int_to_int;
       ce_vars = [];
       ce_rec = Nonrecursive;
       ce_purary = 3})
    [("+", "Int63.add"); ("-", "Int63.sub"); ("*", "Int63.mul");
     ("/", "Int63.div"); ("mod", "Int63.mod")]
  @ [
    (["~-"],
     {ce_name = "Int63.opp";
      ce_type = int_to_int;
      ce_vars = [];
      ce_rec = Nonrecursive;
      ce_purary = 2})
  ] @
  List.map
    (fun (ml, coq) ->
      [ml],
      let tv = newgenvar () in
      {ce_name = coq;
       ce_vars = [tv];
       ce_type = newgenarrow tv (newgenarrow tv Predef.type_bool);
       ce_rec = Recursive;
       ce_purary = 2})
    [("=", "ml_eq"); ("<>", "ml_ne");
     ("<", "ml_lt"); (">", "ml_gt");
     ("<=", "ml_le"); (">=", "ml_ge")]
 )

let init_reserved =
  [ "fix"; "Definition"; "Fixpoint"; "Inductive"; "unit"; "bool"; "int63";
    "M"; "Res"; "Fail"; "K"; "coq_type"; "S"; "Eq"; "Lt"; "Gt";
    "nil"; "cons"; "it" ]

let init_vars =
  init_type_map (
  init_term_map {empty_vars with
                 coq_names = Names.of_list init_reserved;
                 top_exec = ["it"]}
)
