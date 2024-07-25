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

let rec map_snd f = function
    [] -> []
  | (a, b) :: l -> let c = f b in (a, c) :: map_snd f l

let make_tuple_type ~def ctl =
  let unit = if def then "unit" else "ml-unit" in
  let pair = if def then "pair" else "ml-pair" in
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

let str_of_ct ct =
  let rec str_of_ct = function
      CTid x -> "CTid " ^ x
    | CTcstr x -> "CTcstr " ^ x
    | CTapp (ct, l) -> "CTapp (" ^ (str_of_ct ct) ^ " >> [" ^ (String.concat ",\n     " (List.map str_of_ct l)) ^ "])"
    | CTabs (x,_,ct) -> "CTabs (" ^ x ^ ", " ^ (str_of_ct ct) ^ ")"
    | CTsort _ -> "CTsort"
    | CTprod _ -> "CTprod"
    | CTmatch (ct,_,ctcl) -> "CTmatch (" ^ (str_of_ct ct) ^ ") with " ^ (String.concat ",\n     | "
  	                                                                   (List.map (fun (u,v) -> (str_of_ct u) ^ " -> " ^ (str_of_ct v)) ctcl))
    | CTann (ct1, ct2) -> "CTann (" ^ (str_of_ct ct1) ^ ", {ann: " ^ (str_of_ct ct2) ^ "})"
    | CTlet _ -> "CTlet"
    | CTif _ -> "CTif" in
  (str_of_ct ct) ^ "\n"

let () = ignore str_of_ct

let rec transl_type ~loc ~env ~vars ~def visited ty =
  let open Format in
  if TypeSet.mem ty visited then not_allowed ~loc "recursive types" else
    let visited = TypeSet.add ty visited in
    let transl_rec = transl_type ~loc ~env ~vars ~def visited in
    match get_desc ty with
    | Tvar _ | Tunivar _ ->
        let tvars = if def then vars.ctvar_map else vars.tvar_map in
        let name =
          try TypeMap.find ty tvars with Not_found -> "Not-found" in
        CTid name
    | Tarrow (Nolabel, t1, t2, _) -> eprintf "@.translating arrow";
        let ct1 = transl_rec t1 and ct2 = transl_rec t2 in
        if def then CTprod (None, ct1, ctapp (CTid"M") [ct2])
        else ctapp (CTid "ml-arrow") [ct1; ct2] (*CTprod (None, ct1, ctapp (CTid"M") [ct2])*)
    | Tarrow _ ->
        not_allowed ~loc "labels"
    | Ttuple tl ->
        make_tuple_type ~def (List.map transl_rec tl)
    | Tconstr (p, tl, _) ->
        begin match Path.Map.find p vars.type_map with
        | desc ->
            if desc.ct_isgadt then
              ctapp (CTid desc.ct_name) (List.map (transl_type ~loc ~env ~vars ~def:true visited) tl) 
            else begin
              if def then
                let mkml = transl_type ~loc ~env ~vars ~def:false visited in
                let subs = make_subst ~mkcoq:transl_rec ~mkml desc tl in
                coq_term_subst subs desc.ct_type
              else
                ctapp (CTid desc.ct_name) (List.map transl_rec tl) end
        | exception Not_found ->
            with_snapshot ~vars
              (fun () -> Ctype.expand_head env ty)
              (fun ~vars ty' ->
                 if eq_type ty ty' then begin
                   Format.eprintf "type failing: %a@." Printtyp.raw_type_expr ty;
                   (*not_allowed ~loc "This type" end;*)
                   CTid "_"
                 end else
                   transl_type ~loc ~env ~vars ~def visited ty')
        end
    | Tnil ->
        CTid (if def then "empty" else "ml-empty")
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

let is_ty_gadt ~vars ty =
  match get_desc ty with
  | Tconstr(p, _, _) -> begin
      match Path.Map.find p vars.type_map with
      | desc -> desc.ct_isgadt end
  | _ -> false

let transl_coq_type ~loc ~env ~vars ty =
  let gadt = is_ty_gadt ~vars ty in
  let def = if gadt then true else false in
  let ct = transl_type ~loc ~env ~vars ~def:def ty in
  (*let rec apply_ct_deep ct monad =
    match ct with
    | CTapp ((CTid "ml-arrow"), [ct1; ct2]) -> CTprod (None, mkcoqty ct1, apply_ct_deep ct2 true)
    | ct -> if monad then ctapp (CTid"M") [(mkcoqty ct)] else mkcoqty ct in
    apply_ct_deep ct false*)
  if gadt then begin
    match ct with
    | CTapp(t, args) -> CTapp (t, (CTid "M") :: args)
    | _ -> failwith "this should not happen" end
  else
    mkcoqty ct

let transl_coq_type_purary ~loc ~env ~vars ty purary =
  let ct = transl_type ~loc ~env ~vars ty in
  let rec apply_ct_deep ct pary =
    let impure = pary = 0 in
    if impure then ctapp (CTid"M") [(mkcoqty ct)] else
      match ct with
      | CTapp ((CTid "ml-arrow"), [ct1; ct2]) -> let trans_ct2 = apply_ct_deep ct2 (pary-1) in
  	  CTprod (None, mkcoqty ct1, trans_ct2)
      | CTapp(t, args) as ct -> if is_ty_gadt ~vars ty then CTapp (t, (CTid "M") :: args) else mkcoqty ct
      | ct -> (*if is_ty_gadt ~vars ty then ct else*) mkcoqty ct in
  apply_ct_deep ct purary


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

let rec get_st_td td = match td with
    Tvar _ -> "Tvar"
  | Tarrow _ -> "Tarrow"
  | Ttuple _ -> "Ttuple"
  | Tconstr (_, tel, _) -> "Tconstr" ^ (String.concat ", " (List.map (fun x -> get_st_td (Types.get_desc x)) tel)) ^ ")"
  | Tobject _ -> "Tobject"
  | Tfield _ -> "Tfield"
  | Tnil -> "Tnil"
  | Tlink _ -> "Tlink"
  | Tsubst _ -> "Tsubst"
  | Tvariant _ -> "Tvariant"
  | Tunivar _ ->  "Tunivar"
  | Tpoly _ -> "Tpoly"
  | Tpackage _ -> "Tpackage"

let () = ignore get_st_td

let transl_constructor ~vars (cd : Types.constructor_declaration) =
  let loc = cd.cd_loc in
  (match cd.cd_args with
   | Cstr_tuple tel -> Format.eprintf "Args of %s: %a@." (Ident.name cd.cd_id) (Format.pp_print_list Printtyp.raw_type_expr) tel
   | _ -> Format.eprintf "args of %s is not a cstr_tuple)" (Ident.name cd.cd_id));
  (match cd.cd_res with
   | Some td -> Format.eprintf "cd_res: %a@." Printtyp.raw_type_expr td;
   | None -> Format.eprintf "res : none@.");
  let cname = fresh_name ~vars (Ident.name cd.cd_id) in
  let vars = add_reserved cname vars in
  let args =
    match cd.cd_args with
    | Cstr_tuple tyl -> tyl
    | Cstr_record _ ->
        not_allowed ~loc "Inline record"
  in
  (vars, cname, args)

let transl_constructor_gadt ~vars (cd : Types.constructor_declaration) =
  let loc = cd.cd_loc in
  (match cd.cd_args with
   | Cstr_tuple tel -> Format.eprintf "Args of %s: %a@." (Ident.name cd.cd_id) (Format.pp_print_list Printtyp.raw_type_expr) tel
   | _ -> Format.eprintf "args of %s is not a cstr_tuple)" (Ident.name cd.cd_id));
  (match cd.cd_res with
   | Some td -> Format.eprintf "cd_res: %a@." Printtyp.raw_type_expr td;
   | None -> Format.eprintf "res : none@.");
  let cname = fresh_name ~vars (Ident.name cd.cd_id) in
  let vars = add_reserved cname vars in
  let args =
    match cd.cd_args with
    | Cstr_tuple tyl -> tyl
    | Cstr_record _ ->
        not_allowed ~loc "Inline record"
  in
  (vars, cname, args, cd.cd_res)

let print_param p =
  Format.eprintf "%s" (snd p)


let is_gadt td = let open Typedtree in match td.typ_kind with
  | Ttype_variant cases -> List.exists (fun x -> x.cd_res <> None) cases
  | _                       -> false

let transl_typedecl ~env ~vars id td =
  let open Format in
  let loc = td.type_loc in
  let ml_name = fresh_name ~vars ("ml-" ^ Ident.name id) in
  let name = fresh_name ~vars (Ident.name id) in
  eprintf "@.--- Name : %s" name;
  let vars = add_reserved name vars in
  let old_tvars = get_tvars vars in
  let params, vars = enter_tvars ~loc ~vars ~def:true td.type_params in
  let ml_params0, vars = enter_tvars ~loc ~vars ~def:false td.type_params in
  eprintf "@.--- params: "; let _ = List.map print_param params in
  eprintf "@.--- ml-params0: "; let _ = List.map print_param ml_params0 in
  eprintf "@.Constructors:@.";
  let ret_type params ml_params =
    ctapp (CTid name)
      (List.map (fun (_,v) -> ctid v) params @
       List.map (fun (_,v) -> ctid v) ml_params) in
  let ctd =
    { ct_name = ml_name; ct_arity = td.type_arity;
      ct_args = params; ct_mlargs = ml_params0; ct_coqdef = [];
      ct_type = ret_type params ml_params0; ct_def = None;
      ct_compare = None; ct_constrs = []; ct_maps = []; ct_isgadt = false } in
  let vars = add_type (Path.Pident id) ctd vars in
  if td.type_private <> Public then not_allowed ~loc "Private type";
  let new_tvars = get_tvars vars in
  (set_tvars vars old_tvars,
   fun vars ->
     let old_tvars = get_tvars vars in
     let vars = set_tvars vars new_tvars in
     begin match td.type_kind with
     | Type_variant (cl, _) ->
         let names_types, vars =
           List.fold_left
             (fun (ntl, vars) cd ->
                let vars, cname, args = transl_constructor ~vars cd in
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
         let cmp_arg = transl_type ~loc ~env ~vars in
         let coq_def_arg = transl_type ~loc ~env ~vars ~def:true in
         let cmp_cases =
           List.map snd ml_params0, map_snd (List.map cmp_arg) names_types
         and ct_constrs =
           List.map2 (fun cd (cname, _) -> (Ident.name cd.cd_id, cname))
             cl names_types
         and cases =
           List.map (fun (cname, args) ->
               let mkarg arg = ("_", coq_def_arg arg) in
               cname, List.map mkarg args, None)
             names_types
         in
         let ctd = { ctd with ct_constrs; ct_def = Some cmp_cases } in
         let vars = add_type (Path.Pident id) ctd vars in
         let args =
           List.map (fun (_,v) -> v, CTsort Type) params
           @ List.map (fun (_,v) -> v, ml_tid) ml_params in
         { name; args; kind = CTsort Type; cases },
         set_tvars vars old_tvars
     | _ -> not_allowed ~loc "Non-inductive type definition"
     end)


let transl_typedecl_gadt ~env ~vars id td =
  let open Format in
  eprintf "@.@.";
  let loc = td.type_loc in
  let ml_name = fresh_name ~vars ("ml-" ^ Ident.name id) in
  ignore ml_name;
  let name = fresh_name ~vars (Ident.name id) in
  eprintf "@.--- Name : %s" name;
  let vars = add_reserved name vars in
  let old_tvars = get_tvars vars in
  let params, vars = enter_tvars ~loc ~vars ~def:true td.type_params in
  let ml_params = [] in
  eprintf "@.--- params: "; let _ = List.map print_param params in
  eprintf "@.--- ml-params0: "; let _ = List.map print_param ml_params in
  eprintf "@.Constructors:@.";
  let ret_type params ml_params =
    ctapp (CTid name)
      (List.map (fun (_,v) -> ctid v) params @
       List.map (fun (_,v) -> ctid v) ml_params) in
  let ctd =
    { ct_name = name; ct_arity = td.type_arity;
      ct_args = params; ct_mlargs = ml_params; ct_coqdef = [];
      ct_type = ret_type params ml_params; ct_def = None;
      ct_compare = None; ct_constrs = []; ct_maps = []; ct_isgadt = true} in
  let vars = add_type (Path.Pident id) ctd vars in
  if td.type_private <> Public then not_allowed ~loc "Private type";
  let new_tvars = get_tvars vars in
  (set_tvars vars old_tvars,
   fun vars ->
     let old_tvars = get_tvars vars in
     let vars = set_tvars vars new_tvars in
     begin match td.type_kind with
     | Type_variant (cl, _) ->
         let names_types, vars =
           List.fold_left
             (fun (ntl, vars) cd ->
                let vars, cname, args, res = transl_constructor_gadt ~vars cd in
                ((cname, args, res) :: ntl, vars))
             ([],vars) cl
         in
         let names_types = List.rev names_types in
         (*let all_types =
           List.map
             (fun (cname, args, res) ->
               let args_with_res = match res with
               | None -> args
               | Some arg -> arg :: args in
               let ctl_def =
                 List.map (transl_type ~loc ~env ~vars ~def:true) args_with_res in
               ctapp (CTid cname) ctl_def)
             names_types in
           let all_types = ctapp (CTid "") all_types in
           let used = coq_vars all_types
             ~skip:(function CTapp (CTid x, _) -> x = name | _ -> false) in
           let filter_used = List.filter (fun (_,v) -> eprintf "@.test: %s -- is used: %b" v (Names.mem v used); Names.mem v used) in
           let params = filter_used params in
           let ml_params = filter_used ml_params0 in
           let ctd = { ctd with ct_args = params; ct_mlargs = ml_params;
                     ct_type = ret_type params ml_params } in*)
         let vars = add_type (Path.Pident id) ctd vars in
         let cmp_arg = transl_type ~loc ~env ~vars in
         (* let coq_def_arg = transl_type ~loc ~env ~vars ~def:true in *)
         let rec list3_to_list2 l3 = match l3 with       (* converts a list of 3-uples to a list of 2-uples by discarding the last element *)
      	   | [] -> []
      	   | (u, v, _) :: q -> (u, v) :: (list3_to_list2 q) in
         let names_types_no_res = list3_to_list2 names_types in
         let cstr_descs = match Env.find_type_descrs (Path.Pident id) env with
           | Type_variant (cstr_desc_list, _) -> cstr_desc_list
           | _ -> not_allowed ~loc "type_kind that is not a type variant" in
         let cmp_cases =
           List.map snd ml_params, map_snd (List.map cmp_arg) names_types_no_res
         and ct_constrs =
           List.map2 (fun cd (cname, _) -> (Ident.name cd.cd_id, cname))
             cl names_types_no_res
         and cases =
           List.mapi (fun i (cname, args, res) ->
               let gadt_params, cstr_vars = (match res with
                   | None -> params, vars
                   | Some cto ->
                       let gadt_exis = (List.nth cstr_descs i).cstr_existentials in
                       let gadt_univ = Ctype.free_variables cto in
                       enter_tvars ~loc ~vars ~def:true (gadt_exis @ gadt_univ)) in
               eprintf "@.parameters : ";
               let _ = List.map (fun (_, v) -> eprintf "%s, " v) gadt_params in
               let coq_def_arg = transl_type ~loc ~env ~vars:cstr_vars ~def:true in
               let oret_type = match res with
                 | Some arg -> coq_def_arg arg
                 | None -> eprintf "@.Bad return type";  ret_type params ml_params in
               let ctd = { ctd with ct_args = params; ct_mlargs = ml_params;
                                    ct_type = oret_type } in
               let cstr_vars = add_type (Path.Pident id) ctd cstr_vars in
               let coq_def_arg = transl_type ~loc ~env ~vars:cstr_vars ~def:true in
               (*let mkarg arg = ("_", List.fold_left (fun ct (_, param) -> CTabs(param, None, ct)) (coq_def_arg arg) gadt_params) in*)
               let mkarg arg = ("_", coq_def_arg arg) in
               cname,
               ((List.map (fun (_, v) -> v, ctid "Set") gadt_params) @ (List.map mkarg args)),
               (match res with
                | None -> Some oret_type
                | Some arg -> let c = coq_def_arg arg in Some c))
             names_types
         in
         let ctd = { ctd with ct_constrs; ct_def = Some cmp_cases } in
         let vars = add_type (Path.Pident id) ctd vars in
         eprintf "@.- params: "; let _ = List.map print_param params in
         eprintf "@.- ml-params: "; let _ = List.map print_param ml_params in
         let args = []
         (*List.map (fun (_,v) -> v, CTsort Type) params
           @ List.map (fun (_,v) -> v, ml_tid) ml_params*) in
         { name; args; kind = CTsort Type; cases },
         set_tvars vars old_tvars
     | _ -> not_allowed ~loc "Non-inductive type definition"
     end)




let transl_typedecls ~env ~vars (td_list: Typedtree.type_declaration list) =
  let open Typedtree in
  let (vars, clos) =
    List.fold_left
      (fun (vars, clos) td ->
         let (vars, clo) = if is_gadt td
           then transl_typedecl_gadt ~env ~vars td.typ_id td.typ_type
           else transl_typedecl ~env ~vars td.typ_id td.typ_type in
         (vars, clo :: clos))
      (vars, []) td_list
  in
  let (inds, vars) =
    List.fold_left
      (fun (inds, vars) clo ->
         let (ind, vars) = clo vars in (ind::inds, vars))
      ([], vars) clos
  in
  (CTinductive inds, vars)

(*
let rec make_exn_name = function
    Pident id -> Ident.name id
  | Pdot(p, s) -> make_exn_name p ^ "__" ^ s
  | Papply(p1,p2) -> make_exn_name p1 ^ "__'" ^ make_exn_name p2 ^ "'"
*)

let constructor_of_extension excon =
  let exty = excon.Typedtree.ext_type in
  { cd_id = excon.Typedtree.ext_id;
    cd_args = exty.ext_args;
    cd_res = exty.ext_ret_type;
    cd_loc = exty.ext_loc;
    cd_attributes = exty.ext_attributes;
    cd_uid = exty.ext_uid }

let transl_exception ~loc ~env ~vars excon =
  let cd = constructor_of_extension excon in
  let (vars, cname, args) = transl_constructor ~vars cd in
  let cmp_arg = transl_type ~loc ~env ~vars in
  let coq_def_arg = transl_type ~loc ~env ~vars ~def:true in
  let cmp_args = List.map cmp_arg args in
  let coq_def_args = List.map coq_def_arg args in
  add_exception (Path.Pident cd.cd_id) cname cmp_args coq_def_args vars

let enter_free_variables ~loc ~vars ty =
  (*close_type ty;*)
  let fvars = Ctype.free_variables ty in
  let fvars =
    List.filter (fun ty -> not (TypeMap.mem ty vars.tvar_map)) fvars in
  let (fvar_names, vars) =  enter_tvars ~loc ~vars ~def:false fvars in
  (*List.iter (Format.eprintf "fvar=%a@." Printtyp.raw_type_expr) fvars;*)
  fvars, List.map snd fvar_names, vars
