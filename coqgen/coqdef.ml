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

open Misc
open Asttypes
open Types
open Btype

module Names = Stdlib.String.Set

type error = Not_allowed of string

exception Error of Location.t * error

let not_allowed ?(loc = Location.none) s =
  raise (Error (loc, Not_allowed s))

type coq_sort = Type | Set | Prop

type coq_term =
    CTid of string
  | CTcstr of string
  | CTapp of coq_term * coq_term list
  | CTabs of string * coq_term option * coq_term
  | CTsort of coq_sort
  | CTprod of string option * coq_term * coq_term
  | CTmatch of
      coq_term * (string * coq_term) option * (coq_term * coq_term) list
  | CTann of coq_term * coq_term
  | CTlet of string * coq_term option * coq_term * coq_term
  | CTif of coq_term * coq_term * coq_term

type vernacular =
  | CTdefinition of string * coq_term
  | CTfixpoint of string * coq_term
  | CTeval of coq_term
  | CTinductive of
      { name: string; args: (string * coq_term) list; kind: coq_term;
        cases: (string * (string * coq_term) list * coq_term option) list }
  | CTverbatim of string

let may_app f o x =
  match o with
    None -> x
  | Some y -> f y x

let coq_vars ?(skip = fun _ -> false) =
  let rec coq_vars ct0 =
    if skip ct0 then Names.empty else
    match ct0 with
    | CTid x -> Names.singleton x
    | CTcstr _ -> Names.empty
    | CTapp (ct, ctl) ->
        List.fold_left Names.union (coq_vars ct) (List.map coq_vars ctl)
    | CTabs (x, cto, ct) ->
        Names.union (Names.remove x (coq_vars ct)) (coq_vars_opt cto)
    | CTsort _ -> Names.empty
    | CTprod (ox, ct1, ct2) ->
        let vars = may_app Names.remove ox (coq_vars ct2) in
        Names.union vars (coq_vars ct1)
    | CTmatch (ct, oret, cases) ->
        let case_ret =
          Option.to_list (Option.map (fun (v,ct) -> CTid v, ct) oret) in
        let cases_vars (lhs,rhs) = Names.diff (coq_vars rhs) (coq_vars lhs) in
        List.fold_left Names.union (coq_vars ct)
          (List.map cases_vars (case_ret @ cases))
    | CTann (ct1, ct2) ->
        Names.union (coq_vars ct1) (coq_vars ct2)
    | CTlet (x, cto, ct1, ct2) ->
        Names.union (coq_vars_opt cto)
          (Names.union (coq_vars ct1) (Names.remove x (coq_vars ct2)))
    | CTif (ct1, ct2, ct3) ->
        Names.union (coq_vars ct1) (Names.union (coq_vars ct2) (coq_vars ct3))

  and coq_vars_opt = function
    | None -> Names.empty
    | Some ct -> coq_vars ct

  in coq_vars

(* XXX should handle capture *)
let remove x subs =
  if Vars.mem x subs then (prerr_endline ("Removed " ^ x); Vars.remove x subs)
  else subs
let rec coq_term_subst subs = function
  | CTid x as ct ->
      if Vars.mem x subs then Vars.find x subs else ct
  | CTcstr _ as ct ->
      ct
  | CTapp (x, l) ->
      CTapp (coq_term_subst subs x, List.map (coq_term_subst subs) l)
  | CTabs (x, t, b) ->
      let subs' =
        if Vars.mem x subs then remove x subs else subs in
      CTabs (x, Option.map (coq_term_subst subs) t,
             coq_term_subst subs' b)
  | CTsort _ as ct -> ct
  | CTprod (ox, t, b) ->
      let subs' = may_app remove ox subs in
      CTprod (ox, coq_term_subst subs t, coq_term_subst subs' b)
  | CTmatch (ct, oret, cases) ->
      let subs_ret (v, ct) = v, coq_term_subst (remove v subs) ct in
      let subs_case (lhs, rhs) =
        let subs' = Names.fold remove (coq_vars lhs) subs in
        (lhs, coq_term_subst subs' rhs)
      in
      CTmatch (coq_term_subst subs ct, Option.map subs_ret oret,
               List.map subs_case cases)
  | CTann (ct1, ct2) ->
      CTann (coq_term_subst subs ct1, coq_term_subst subs ct2)
  | CTlet (x, cto, ct1, ct2) ->
      let subs' =
        if Vars.mem x subs then remove x subs else subs in
      CTlet (x, Option.map (coq_term_subst subs) cto,
             coq_term_subst subs ct1, coq_term_subst subs' ct2)
  | CTif (ct1, ct2, ct3) ->
      CTif (coq_term_subst subs ct1, coq_term_subst subs ct2,
            coq_term_subst subs ct3)

let ctid s = CTid s
let ctapp ct args = if args = [] then ct else CTapp (ct, args)
let ctcstr s args = ctapp (CTcstr s) args
let ctRet ct = CTapp (CTid "Ret", [ct])
let ctBind m f = CTapp (CTid "Bind", [m; f])
let ctpair a b = ctcstr "pair" [a;b]

let ml_type = "ml_type"
let ml_tid = CTid ml_type
let coq_tid = CTid "coq_type"
let mkcoqty ct = ctapp coq_tid [ct]

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
  }

type coq_term_desc =
    { ce_name: string;
      ce_type: type_expr;
      ce_vars: type_expr list;
      ce_rec: rec_flag;
      ce_purary: int; (* pure arity: number of application before monad *)
    }

type coq_env =
    { type_map: coq_type_desc Path.Map.t;
      term_map: coq_term_desc Path.Map.t;
      tvar_map: string TypeMap.t;
      ctvar_map: string TypeMap.t;
      top_exec: string list;
      coq_names: Names.t;
    }

let empty_vars =
  { type_map = Path.Map.empty;
    term_map = Path.Map.empty;
    tvar_map = TypeMap.empty;
    ctvar_map = TypeMap.empty;
    top_exec = [];
    coq_names = Names.empty;
  }

let add_type path td vars =
  { vars with
    type_map = Path.Map.add path td vars.type_map;
    coq_names = Names.add td.ct_name vars.coq_names }

let add_term ?(toplevel = false) path td vars =
  let td, top_exec =
    if toplevel && td.ce_purary = 0 then
      td (*{td with ce_purary = 1}*), td.ce_name :: vars.top_exec
    else td, vars.top_exec
  in
  { vars with
    term_map = Path.Map.add path td vars.term_map;
    top_exec = top_exec;
    coq_names = Names.add td.ce_name vars.coq_names }

let add_tvar tv name vars =
  { vars with
    tvar_map = TypeMap.add tv name vars.tvar_map;
    coq_names = Names.add name vars.coq_names }

let add_ctvar tv name vars =
  { vars with
    ctvar_map = TypeMap.add tv name vars.ctvar_map;
    coq_names = Names.add name vars.coq_names }

let add_reserved name vars =
  { vars with coq_names = Names.add name vars.coq_names }

let refresh tvars =
  TypeMap.fold (fun ty -> TypeMap.add ty) tvars TypeMap.empty

let refresh_tvars vars =
  { vars with
    tvar_map = refresh vars.tvar_map;
    ctvar_map = refresh vars.ctvar_map }

type tvar_map = string TypeMap.t * string TypeMap.t

let names_of_tvars tvars =
  TypeMap.fold (fun _ -> Names.add) tvars Names.empty

let get_tvars vars = (vars.tvar_map, vars.ctvar_map)
let set_tvars vars (tvars, ctvars) =
  let current_names =
    Names.union (names_of_tvars vars.tvar_map) (names_of_tvars vars.ctvar_map)
  and orig_names =
    Names.union (names_of_tvars tvars) (names_of_tvars ctvars) in
  let coq_names =
    Names.union orig_names
      (Names.diff vars.coq_names (Names.diff current_names orig_names)) in
  { vars with tvar_map = tvars; ctvar_map = ctvars; coq_names }

let fresh_name ~vars name =
  if not (Names.mem name vars.coq_names) then name else
  let rec search n =
    let name_n = name ^ "_" ^ string_of_int n in
    if not (Names.mem name_n vars.coq_names) then name_n else search (n+1)
  in search 1

let fresh_opt_name ?(name = "T") vars =
  fresh_name ~vars name

let fresh_var_name ~vars name =
  fresh_opt_name ?name vars

let report_error ppf = function
  | Not_allowed s ->
      Format.fprintf ppf "%s not allowed for Coq translation." s

let () =
  Location.register_error_of_exn
    (function
      | Error (loc, err) ->
        Some (Location.error_of_printer ~loc report_error err)
      | _ ->
        None
    )
