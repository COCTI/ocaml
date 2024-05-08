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
open Agdadef

let stdlib = Path.Pident (Ident.create_persistent "Stdlib")
let agdagen = Path.Pident (Ident.create_persistent "coqgen")
let stdlib_ref = Path.Pdot (stdlib, "ref")
let newgenconstr p tl = newgenty (Tconstr (p, tl, ref Mnil))
let newgenarrow t1 t2 = newgenty (Tarrow (Nolabel, t1, t2, Cok))
let ident_empty = Ident.create_predef "empty"
let path_empty = Path.Pident ident_empty

let xy = [CTid"x"; CTid"y"]

let ctd = { ct_name = ""; ct_arity = 0; ct_args = []; ct_mlargs = [];
            ct_type = CTid ""; ct_def = None; ct_constrs = [];
            ct_compare = None; ct_maps = []; ct_coqdef = [] }

let init_type_map vars =
  List.fold_left
    (fun map (rt, lid, desc) ->
      let path = List.fold_left (fun m s -> Path.Pdot (m, s)) rt lid in
      add_type path desc map)
    vars
  [
   (stdlib, ["ref"],
    {ctd with ct_name = "ml-ref";
     ct_arity = 1; ct_mlargs = [0, "a"];
     ct_type = CTapp (CTid "loc", [CTid "a"]);
     ct_compare =
     Some (CTapp (CTid"compare-ref", CTid"compare-rec" :: CTid"T1" :: xy))});
   (path_empty, [],
    {ctd with ct_name = "ml-empty"; ct_type = CTid "empty";
     ct_compare = Some (CTmatch (CTid"x", None, []))});
   (Predef.path_int, [],
    {ctd with ct_name = "ml-int";
     ct_type = CTid "ℤ"; (* \bZ ; utf-8: 0x2124 *)
     ct_compare = Some (ctRet (CTapp (CTid"compare-integer", xy)))});
   (Predef.path_float, [],
    {ctd with ct_name = "ml-float";
     ct_type = CTid "Float";
     ct_compare = Some (ctRet (CTapp (CTid"compare-float", xy)))});
   (Predef.path_char, [],
    {ctd with ct_name = "ml-char";
     ct_type = CTid "Char";
     ct_compare = Some (ctRet (CTapp (CTid"compare-ascii", xy)))});
   (Predef.path_string, [],
    {ctd with ct_name = "ml-string";
     ct_type = CTid "String";
     ct_compare = Some (ctRet (CTapp (CTid"compare-string", xy)))});
   (Predef.path_unit, [],
    {ctd with ct_name = "ml-unit";
     ct_type = CTid "Unit";
     ct_def = Some ([], ["tt", []]);
     ct_constrs = ["()", "tt"];
     ct_compare = None});
   (Predef.path_bool, [],
    {ctd with ct_name = "ml-bool";
     ct_type = CTid "Bool";
     ct_constrs = List.map (fun x -> (x,x)) ["true"; "false"];
     ct_compare = Some (ctRet (CTapp (CTid"compare-bool", xy)))});
   (Predef.path_list, [],
    {ctd with ct_name = "ml-list";
     ct_arity = 1; ct_args = [0, "a"];
     ct_constrs = [("[]", "@nil"); ("∷", "@cons")]; (* :: ; utf-8: 0x2237 *)
     ct_type = CTapp (CTid "List", [CTid "a"]); ct_def = None;
     ct_maps = [1, "cast_list"];
     ct_compare = Some
       (CTapp (CTid"compare-list",
               CTid"compare-rec" :: CTid "T1" :: xy))});
   (Predef.path_array, [],
    {ctd with ct_name = "ml-array";
     ct_arity = 1; ct_mlargs = [0, "a"];
     ct_type = CTapp (CTid"loc", [CTapp (CTid"ml-array-t", [CTid"a"])]);
     ct_compare = Some
       (CTapp (CTid"compare-ref",
               CTid"compare-rec" ::
               ctapp (CTid"ml-array-t") [CTid "T1"] :: xy))});
   (Predef.path_lazy_t, [],
    {ctd with ct_name = "ml-lazy";
     ct_arity = 1;ct_args = [0, "a"];  ct_mlargs = [0, "a_1"];
     ct_type = CTapp (CTid"lazy-t", [CTid"a"; CTid"a_1"]);
     ct_compare = None
    });
   (stdlib, ["lazy-val"],
    {ctd with ct_name = "ml-lazy-val";
     ct_arity = 1; ct_args = [0, "a"];
     ct_type = CTapp (CTid"lazy-val", [CTid"a"]);
     ct_compare = None
    });
   (Path.Pident (Ident.create_predef "array-t"), [],
    {ctd with ct_name = "ml-array-t";
     ct_arity = 1; ct_args = [0, "a"];
     ct_constrs = [("ArrayVal", "ArrayVal")];
     ct_type = CTapp (CTid"array-t", [CTid"a"]);
     ct_def = Some (["a"], ["ArrayVal", [CTapp(CTid"ml-list", [CTid "a"])]])});
   (Predef.path_exn, [],
    {ctd with ct_name = "ml-exn";
     ct_type = CTid "ml-exns";
     ct_constrs = List.map (fun x -> (x,x))
       ["Invalid-argument"; "Failure"; "Not-found"];
     ct_coqdef = ["Invalid-argument", [CTid"string"];
                  "Failure", [CTid"string"]; "Not-found", []];
     ct_def = Some ([], ["Invalid-argument", [CTid"ml-string"];
                         "Failure", [CTid"ml-string"]; "Not-found", []])});
   (agdagen, ["arrow"],
    {ctd with ct_name = "ml-arrow";
     ct_arity = 2; ct_args = [0, "a"; 1, "b"];
     ct_type = CTprod (None, CTid"a",
                       CTapp (CTid"M", [CTid"b"]))});
  ]

let init_term_map vars =
  let int_to_int = newgenarrow Predef.type_int Predef.type_int in
  let int_to_int_to_int = newgenarrow Predef.type_int int_to_int in
  let float_to_float = newgenarrow Predef.type_float Predef.type_float in
  let float_to_float_to_float = newgenarrow Predef.type_float float_to_float in
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
    {ce_name = "cnew";
     ce_type = newgenarrow tv (newgenconstr stdlib_ref [tv]);
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   (["!"],
    let tv = newgenvar () in
    {ce_name = "cget";
     ce_type = newgenarrow (newgenconstr stdlib_ref [tv]) tv;
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   ([":="],
    let tv = newgenvar () in
    {ce_name = "cput";
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
   (["raise"],
    let tv = newgenvar () in
    {ce_name = "raise";
     ce_type = newgenarrow Predef.type_exn tv;
     ce_vars = [tv];
     ce_rec = Nonrecursive;
     ce_purary = 1});
   (["Lazy";"force"],
    let tv = newgenvar () in
    {ce_name = "force";
     ce_type = newgenarrow (Predef.type_lazy_t tv) tv;
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
    [("+", "_+_"); ("-", "_-_"); ("*", "_*_");
     ("/", "_/_"); ("mod", "_%_")]
  @ [
    (["~-"],
     {ce_name = "-_";
      ce_type = int_to_int;
      ce_vars = [];
      ce_rec = Nonrecursive;
      ce_purary = 2})
  ] @
  List.map
    (fun (ml, coq) ->
      [ml],
      {ce_name = coq^"%float";
       ce_type = float_to_float_to_float;
       ce_vars = [];
       ce_rec = Nonrecursive;
       ce_purary = 3})
    [("+.", "add"); ("-.", "sub"); ("*.", "mul");
     ("/.", "div")]
  @ [
    (["~-."],
     {ce_name = "opp";
      ce_type = float_to_float;
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
    [("=", "ml-eq"); ("<>", "ml-ne");
     ("<", "ml-lt"); (">", "ml-gt");
     ("<=", "ml-le"); (">=", "ml-ge")]
 )

let init_reserved =
  [ "fix"; "data"; "unit"; "bool"; "int63";
    "M"; "Res"; "Raise"; "Fail"; "K"; "coq-type"; "S"; "Eq"; "Lt"; "Gt";
    "nil"; "cons"; "it"; "Restart"; "T1"; "T2" ]

let init_vars =
  init_type_map (
  init_term_map {empty_vars with
                 coq_names = Names.of_list init_reserved;
                 top_exec = ["it"]}
)
