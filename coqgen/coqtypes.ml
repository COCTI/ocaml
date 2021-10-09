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

let make_tuple_type ~def ctl =
  let unit = if def then "unit" else "ml_unit" in
  let pair = if def then "pair" else "ml_pair" in
  List.fold_left
    (fun ct ct' ->
      if ct = CTid unit then ct' else CTapp (CTid pair, [ct; ct']))
    (CTid unit) ctl

let make_subst ~mkcoq ~mkml ctd types =
  let arg_types =
    List.map (fun (n, v) -> (v, mkcoq (List.nth types n)))
      ctd.ct_args @
    List.map (fun (n, v) -> (v, mkml (List.nth types n)))
      ctd.ct_mlargs
  in
  Vars.of_seq (List.to_seq arg_types)

let with_snapshot ~vars f g =
  let snap = Btype.snapshot () in
  let x = f () in
  let vars = refresh_tvars vars in
  let y = g ~vars x in
  Btype.backtrack snap;
  y

let rec transl_type ~loc ~env ~vars ~def visited ty =
  if TypeSet.mem ty visited then not_allowed ~loc "recursive types" else
  let visited = TypeSet.add ty visited in
  let transl_rec = transl_type ~loc ~env ~vars ~def visited in
  match get_desc ty with
  | Tvar _ | Tunivar _ ->
      let tvars = if def then vars.ctvar_map else vars.tvar_map in
      let name =
        try TypeMap.find ty tvars with Not_found -> "Not_found" in
      CTid name
  | Tarrow (Nolabel, t1, t2, _) ->
      let ct1 = transl_rec t1 and ct2 = transl_rec t2 in
      if def then CTprod (None, ct1, ctapp (CTid"M") [ct2])
      else ctapp (CTid "ml_arrow") [ct1; ct2]
  | Tarrow _ ->
      not_allowed ~loc "labels"
  | Ttuple tl ->
      make_tuple_type ~def (List.map transl_rec tl)
  | Tconstr (p, tl, _) ->
      begin match Path.Map.find p vars.type_map with
        desc ->
          if def then
            let mkml = transl_type ~loc ~env ~vars ~def:false visited in
            let subs = make_subst ~mkcoq:transl_rec ~mkml desc tl in
            coq_term_subst subs desc.ct_type
          else
            ctapp (CTid desc.ct_name) (List.map transl_rec tl)
      | exception Not_found ->
          with_snapshot ~vars
            (fun () -> Ctype.expand_head env ty)
            (fun ~vars ty' ->
              if eq_type ty ty' then not_allowed ~loc "This type";
              transl_type ~loc ~env ~vars ~def visited ty')
      end
  | Tnil ->
      CTid (if def then "empty" else "ml_empty")
  | Tobject _ | Tfield _ ->
      not_allowed ~loc "object types"
  | Tvariant _ ->
      not_allowed ~loc "polymorphic variants"
  | Tpoly (t1, vl) ->
      let vars =
        List.fold_left
          begin fun vars tv ->
            match get_desc tv with
            | Tunivar name -> add_tvar tv (fresh_var_name ~vars name) vars
            | _ -> assert false
          end
          vars vl
      in
      let ct1 = transl_type ~loc ~env ~vars ~def visited t1 in
      List.fold_right
        (fun tv ct -> CTprod (Some (TypeMap.find tv vars.tvar_map), ml_tid, ct))
        vl ct1
  | Tpackage _ ->
      not_allowed ~loc "first class modules"
  | Tlink _ | Tsubst _ ->
      assert false

let transl_type ~loc ~env ~vars ?(def=false) =
  transl_type ~loc ~env ~vars ~def TypeSet.empty
let transl_coq_type ~loc ~env ~vars ty =
  mkcoqty (transl_type ~loc ~env ~vars ty)

let find_instantiation ~loc ~env ~vars edesc ty =
  if edesc.ce_vars = [] then [] else
  let open Ctype in
  let ty0, ivars =
    let ty1 = newgenty (Ttuple (edesc.ce_type :: edesc.ce_vars)) in
    match get_desc (generic_instance ty1) with
      Ttuple (ty0 :: vars) -> ty0, vars
    | _ -> assert false
  in
  with_snapshot ~vars
    (fun () ->
      try unify env ty ty0
      with Unify _ -> not_allowed ~loc ("Type for " ^ edesc.ce_name))
    (fun ~vars () -> List.map (transl_type ~loc ~env ~vars) ivars)

let close_type ty =
  let vars = Ctype.free_variables ty in
  List.iter
    (fun ty ->
      let level = get_level ty in
      if level <> Btype.generic_level then
        Types.link_type ty (newty2 ~level Tnil))
    vars

let enter_tvars ~loc ~vars ~def tvl =
  let add_tvar = if def then add_ctvar else add_tvar in
  let names, vars =
    List.fold_left
      (fun (names, vars) tv -> match get_desc tv with
      | Tvar name ->
          let v = fresh_var_name ~vars name in
          v :: names, add_tvar tv v vars
      | _ -> not_allowed ~loc "Non-variable parameter")
      ([],vars) tvl
  in
  (List.mapi (fun n x -> n, x) (List.rev names), vars)

let transl_typedecl ~loc ~env ~vars id td =
  let ml_name = fresh_name ~vars ("ml_" ^ Ident.name id) in
  let name = fresh_name ~vars (Ident.name id) in
  let vars = add_reserved name vars in
  let old_tvars = get_tvars vars in
  let params, vars = enter_tvars ~loc ~vars ~def:true td.type_params in
  let ml_params0, vars = enter_tvars ~loc ~vars ~def:false td.type_params in
  let ret_type params ml_params =
    ctapp (CTid name)
      (List.map (fun (_,v) -> ctid v) params @
       List.map (fun (_,v) -> ctid v) ml_params) in
  let ctd =
    { ct_name = ml_name; ct_arity = td.type_arity;
      ct_args = params; ct_mlargs = ml_params0;
      ct_type = ret_type params ml_params0; ct_def = None;
      ct_compare = None; ct_constrs = [] } in
  let vars = add_type (Path.Pident id) ctd vars in
  if td.type_private <> Public then not_allowed ~loc "Private type";
  begin match td.type_kind with
  | Type_variant (cl, _) ->
      let names_types, vars =
        List.fold_left
          (fun (ntl, vars) (cd : Types.constructor_declaration) ->
            if cd.cd_res <> None then not_allowed ~loc "GADT";
            let cname = fresh_name ~vars (Ident.name cd.cd_id) in
            let vars = add_reserved cname vars in
            let args =
              match cd.cd_args with
              | Cstr_tuple tyl -> tyl
              | Cstr_record _ ->
                  not_allowed ~loc "Inline record"
            in
            ((cname, args) :: ntl, vars))
          ([],vars) cl
      in
      let names_types = List.rev names_types in
      let all_types =
        List.map
          (fun (cname, args) ->
            let ctl_def =
              List.map (transl_type ~loc ~env ~vars ~def:true) args in
            ctapp (CTid cname) ctl_def)
          names_types in
      let all_types = ctapp (CTid "") all_types in
      let used = coq_vars all_types
          ~skip:(function CTapp (CTid x, _) -> x = name | _ -> false) in
      let filter_used = List.filter (fun (_,v) -> Names.mem v used) in
      let params = filter_used params in
      let ml_params = filter_used ml_params0 in
      let ctd = { ctd with ct_args = params; ct_mlargs = ml_params;
                  ct_type = ret_type params ml_params } in
      let vars = add_type (Path.Pident id) ctd vars in
      let cmp_cases =
        List.map snd ml_params0,
        List.map (fun (cname, args) ->
          let ctl_def = List.map (transl_type ~loc ~env ~vars) args in
          (cname, ctl_def))
          names_types
      and ct_constrs =
        List.map2 (fun cd (cname, _) -> (Ident.name cd.cd_id, cname))
          cl names_types
      and cases =
        List.map (fun (cname, args) ->
          let mkarg arg = ("_", transl_type ~loc ~env ~vars ~def:true arg) in
          cname, List.map mkarg args, None)
          names_types
      in
      let ctd = { ctd with ct_constrs; ct_def = Some cmp_cases } in
      let vars = add_type (Path.Pident id) ctd vars in
      let args =
        List.map (fun (_,v) -> v, CTsort Type) params
        @ List.map (fun (_,v) -> v, ml_tid) ml_params in
      CTinductive { name; args; kind = CTsort Type; cases },
      set_tvars vars old_tvars
  | _ -> not_allowed ~loc "Non-inductive type definition"
  end

let enter_free_variables ~loc ~vars ty =
  (*close_type ty;*)
  let fvars = Ctype.free_variables ty in
  let fvars =
    List.filter (fun ty -> not (TypeMap.mem ty vars.tvar_map)) fvars in
  let (fvar_names, vars) =  enter_tvars ~loc ~vars ~def:false fvars in
  (*List.iter (Format.eprintf "fvar=%a@." Printtyp.raw_type_expr) fvars;*)
  fvars, List.map snd fvar_names, vars
