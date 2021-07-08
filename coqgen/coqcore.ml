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
open Typedtree
open Coqdef
open Coqinit
open Coqtypes

type term_props =
    { pterm: coq_term; prec: rec_flag; pary: int }

let make_tuple ctl =
  List.fold_left
    (fun ct ct' ->
      if ct = CTid "tt" then ct' else CTapp (CTid"pair", [ct; ct']))
    (CTid "tt") ctl

let name_tuple names =
  let ctl = List.map ctid names in
  make_tuple ctl

let rec shrink_purary_val ~vars ~args p1 p2 ct =
  if p1 <= 1 then ctapp ct (List.rev args) else
  let x = fresh_name ~vars "x" in
  let ct1 =
    CTabs (x, None,
           shrink_purary_val ~vars:(add_reserved x vars) ~args:(CTid x :: args)
             (p1-1) (p2-1) ct)
  in
  if p2 <= 0 then ctRet ct1 else ct1

let rec shrink_purary_rec ~vars p1 p2 ct =
  assert (p2 <= p1);
  if p1 <= 0 || p1 = p2 then ct else
  let ct2 =
    match ct with
    | CTabs (x, t, ct1) ->
        let vars = add_reserved x vars in
        CTabs (x, t, shrink_purary_rec ~vars (p1-1) (p2-1) ct1)
    | _ ->
        shrink_purary_val ~vars ~args:[] p1 p2 ct
  in
  if p2 <= 0 then ctRet ct2 else ct2

let shrink_purary ~vars pt p2 =
  if pt.pary = p2 then pt else
  {pterm = shrink_purary_rec ~vars pt.pary p2 pt.pterm;
   prec = pt.prec; pary = p2}

let nullary ~vars pt =
  shrink_purary ~vars pt 0

let rec cut n l =
  if n <= 0 then ([], l) else
  match l with
  | [] -> invalid_arg "cut"
  | a :: l -> let (l1, l2) = cut (n-1) l in (a::l1, l2)

let or_rec r1 r2 =
  match r1, r2 with
  | Nonrecursive, Nonrecursive -> Nonrecursive
  | _ -> Recursive

let rec insert_guard ct =
  match ct with
    CTabs (v, Some cty, body) when not (Names.mem "h" (coq_vars cty)) ->
      CTabs (v, Some cty, insert_guard body)
  | CTabs (v, None, body) ->
      CTabs (v, None, insert_guard body)
  | CTann (ct, cty) when not (Names.mem "h" (coq_vars cty)) ->
      CTann (insert_guard ct, cty)
  | _ ->
      CTmatch (CTid "h", None,
               [(CTapp(CTid"S",[CTid"h"]),ct); (CTid"_", CTid"Fail")])

let string_of_constant ~loc = function
  | Const_int x ->
      let s = string_of_int x ^ "%int63" in
      if x < 0 then "("^s^")" else s
  | Const_char c ->
      let s = Char.escaped c in
      let s =
        if String.length s = 1 then s else
        Printf.sprintf "%03d" (Char.code c) in
      Printf.sprintf "\"%s\"%%char" s
  | Const_string (s, _, _) ->
      Printf.sprintf "\"%s\"%%string" s
  | _ ->
      not_allowed ~loc "This constant"

let find_constructor ~loc ~vars cd =
  let path, tl =
    match get_desc cd.cstr_res with
    | Tconstr (path, tl, _) -> path, tl
    | _ -> assert false
  in
  try
    let ct = Path.Map.find path vars.type_map in
    List.assoc cd.cstr_name ct.ct_constrs, tl
  with Not_found ->
    not_allowed ~loc
      ("The constructor " ^ cd.cstr_name ^ " of type " ^ Path.name path)

let rec transl_pat : type k. vars:_ -> k general_pattern -> _ =
  fun ~vars pat ->
  let loc = pat.pat_loc in
  match pat.pat_desc with
  | Tpat_any -> (CTid "_", vars)
  | Tpat_var (id, _) ->
      let name = fresh_name ~vars (Ident.name id) in
      let desc =
        { ce_name = name; ce_type = pat.pat_type;
          ce_vars = []; ce_rec = Nonrecursive; ce_purary = 1 } in
      let vars = add_term (Path.Pident id) desc vars in
      (CTid name, vars)
  | Tpat_constant cst ->
      (CTcstr (string_of_constant ~loc cst), vars)
  | Tpat_tuple [] ->
      (CTcstr "()", vars)
  | Tpat_tuple (pat1 :: patl) ->
      List.fold_left
        (fun (ctt, vars) pat ->
          let (ct, vars) = transl_pat ~vars pat in (ctpair ctt ct, vars))
        (transl_pat ~vars pat1) patl
  | Tpat_construct (_, cd, patl, _) ->
      let (ctl, vars) =
        List.fold_left
          (fun (ctl, vars) pat ->
            let (ct, vars) = transl_pat ~vars pat in
            (ct :: ctl, vars))
          ([],vars) patl
      in
      let name, tl = find_constructor ~loc ~vars cd in
      let args = List.map (fun _ -> CTid "_") tl @ List.rev ctl in
      (ctapp (CTcstr name) args, vars)
  | Tpat_value pat ->
      transl_pat ~vars (pat :> value general_pattern)
  | _ ->
      not_allowed ~loc "transl_pat : This pattern"

let is_primitive s =
  String.length s >= 2 && (s.[0] >= '@' && s.[0] <= 'Z')

let transl_ident ~loc ~vars env desc ty =
  let f = CTid desc.ce_name in
  if desc.ce_purary = 0 then
    {pterm = f; prec = Nonrecursive; pary = 1}
  else
    let args = find_instantiation ~loc ~env ~vars desc ty in
    let args =
      if is_primitive desc.ce_name then List.map mkcoqty args else args in
    let args =
      if desc.ce_rec = Recursive then CTid"h" :: args else args in
    {pterm = ctapp f args; prec = desc.ce_rec; pary = desc.ce_purary}

let rec fun_arity e =
  match e.exp_desc with
  | Texp_function
    {cases=[{c_lhs={pat_desc=(Tpat_var _|Tpat_any)};c_guard=None;c_rhs}]} ->
      1 + fun_arity c_rhs
  | Texp_function _ -> 1
  | _ -> 0

let abstract_recursive ct =
  CTabs ("h", Some (CTid"nat"), ct)

let rec transl_exp ~vars e =
  let loc = e.exp_loc in
  close_type e.exp_type;
  match e.exp_desc with
  | Texp_ident (path, _, _) ->
      let desc =
        try Path.Map.find path vars.term_map
        with Not_found ->
          not_allowed ~loc ("Identifier " ^ Path.name path)
      in
      transl_ident ~loc ~vars e.exp_env desc e.exp_type
  | Texp_constant cst ->
      {pterm = CTcstr (string_of_constant ~loc cst); prec = Nonrecursive;
       pary = 1 }
  | Texp_let (Nonrecursive, vbl, body) ->
      let ctl =
        List.map (transl_binding ~vars ~rec_flag:Nonrecursive) vbl in
      let (id_descs, ctl) = List.split ctl in
      let names = List.map (fun (_,desc) -> desc.ce_name) id_descs in
      let vars =
        List.fold_right
          (fun (id, desc) vars ->
            match id with
            | Some id ->
                let desc =
                  if desc.ce_purary = 0 then {desc with ce_purary = 1}
                  else desc in
                add_term (Path.Pident id) desc vars
            | None -> vars)
          id_descs
          vars
      in
      let pbody = transl_exp ~vars body in
      let prec = List.fold_right (fun ct -> or_rec ct.prec) ctl pbody.prec in
      let pbody = {pbody with prec} in
      let pat = name_tuple names in
      let ct = make_tuple (List.map (fun ct -> ct.pterm) ctl) in
      begin match pat, id_descs with
      | CTid v, [(_, desc)] ->
          if desc.ce_purary = 0 then
            let pbody = nullary ~vars pbody in
            {pbody with pterm = ctBind ct (CTabs (v, None, pbody.pterm))}
          else
            {pbody with pterm = CTlet (v, None, ct, pbody.pterm)}
      | _ ->
          if List.exists (fun (_,desc) -> desc.ce_purary = 0) id_descs then
            let pbody = nullary ~vars pbody in
            let pbody =
              List.fold_right
                (fun (_,{ce_name; ce_purary}) pbody ->
                  if ce_purary <> 0 then pbody else
                  {pbody with pterm =
                   ctBind (CTid ce_name) (CTabs (ce_name, None, pbody.pterm))})
                id_descs pbody in
            let v = fresh_name ~vars "v" in
            {pbody with pterm =
             ctBind ct (CTabs (v, None,
                               CTmatch (CTid v, None, [pat, pbody.pterm])))}
          else
            {pbody with pterm = CTmatch (ct, None, [pat, pbody.pterm])}
      end
  | Texp_sequence (e1, e2) ->
      let ct1 = nullary ~vars (transl_exp ~vars e1) in
      let ct2 = nullary ~vars (transl_exp ~vars e2) in
      {pterm = ctBind ct1.pterm (CTabs ("_", None, ct2.pterm));
       prec = or_rec ct1.prec ct2.prec; pary = 0}
  | Texp_function
      {arg_label = Nolabel; param = _;
       cases = [{c_lhs = {pat_type; pat_loc} as pat;
                 c_rhs; c_guard = None}]} ->
      let (arg, vars) = transl_pat ~vars pat in
      let cty = transl_coq_type ~loc:pat_loc ~env:pat.pat_env ~vars pat_type in
      let ct = transl_exp ~vars c_rhs in
      let ct =
        match ct.pterm with
          CTabs _ | CTann _ -> ct
        | pt ->
            if ct.pary >= 2 then ct else
            let cty =
              transl_coq_type ~loc:c_rhs.exp_loc ~env:c_rhs.exp_env
                ~vars c_rhs.exp_type in
            let cty = if ct.pary = 0 then CTapp (CTid"M", [cty]) else cty in
            {ct with pterm = CTann (pt, cty)}
      in
      let pterm =
        match arg with
          CTid v -> CTabs (v, Some cty, ct.pterm)
        | pat ->
            let v = fresh_name ~vars "v" in
            CTabs (v, Some cty, CTmatch (CTid v, None, [pat, ct.pterm]))
      in
      {pterm; prec  = ct.prec; pary  = ct.pary + 1}
  | Texp_apply (f, args)
    when List.for_all (function (Nolabel,Some _) -> true | _ -> false) args ->
      let args =
        List.map (function (_,Some arg) -> arg | _ -> assert false) args in
      let ct = transl_exp ~vars f in
      let ctl = List.map (transl_exp ~vars) args in
      let prec =
        if List.exists (fun ct -> ct.prec = Recursive) (ct :: ctl)
        then Recursive else Nonrecursive
      in
      let args, binds, vars =
        List.fold_right
          (fun ct (args, binds, vars) ->
            if ct.pary >= 1 then
              ((shrink_purary ~vars ct 1).pterm :: args, binds, vars)
            else
              let v = fresh_name ~vars "v" in
              (CTid v :: args, (v, ct.pterm) :: binds, add_reserved v vars))
          ctl ([],[],vars)
      in
      let ct =
        if ct.pary >= List.length args then
          {pterm = ctapp ct.pterm args; prec; pary = ct.pary - List.length args}
        else let args1, args2 = cut ct.pary args in
        let ct1 = ctapp ct.pterm args1 in
        {pterm =
         List.fold_left (fun ct1 arg -> CTapp (CTid"AppM", [ct1; arg]))
           ct1 args2;
         prec; pary = 0}
      in
      if binds = [] then ct else
      List.fold_left
        (fun ct (v,arg) ->
          {ct with pterm = ctBind arg (CTabs (v,None,ct.pterm))})
        (nullary ~vars ct) binds
  | Texp_construct (_, cd, []) ->
      let name, tl = find_constructor ~loc ~vars cd in
      let ce =
        {ce_name = name;
         ce_type = List.fold_right newgenarrow cd.cstr_args cd.cstr_res;
         ce_vars = tl;
         ce_rec = Nonrecursive;
         ce_purary = cd.cstr_arity + 1}
      in
      transl_ident ~loc ~vars e.exp_env ce e.exp_type
  | Texp_construct (lid, cd, args) ->
      let ty =
        List.fold_right (fun arg -> newgenarrow arg.exp_type) args e.exp_type
      in
      let constr =
        {e with exp_desc = Texp_construct (lid, cd, []); exp_type = ty} in
      let args = List.map (fun e -> (Nolabel, Some e)) args in
      let app = {e with exp_desc = Texp_apply (constr, args)} in
      begin match transl_exp ~vars app with
      | {pterm = CTapp (CTapp (f, args1), args2)} as ct ->
          {ct with pterm = CTapp (f, args1 @ args2)}
      | ct -> ct
      end
  | Texp_ifthenelse (be, e1, e2) ->
      let ct = transl_exp ~vars be
      and ct1 = transl_exp ~vars e1
      and ct2 =
        match e2 with
        | None    -> {pterm = CTid "tt"; prec = Nonrecursive; pary = 1}
        | Some e2 -> transl_exp ~vars e2
      in
      let prec = or_rec ct.prec (or_rec ct1.prec ct2.prec) in
      if ct.pary = 0 then
        let v = fresh_name ~vars "v" in
        let vars = add_reserved v vars in
        let ct1 = nullary ~vars ct1
        and ct2 = nullary ~vars ct2 in
        {pterm =
         ctBind ct.pterm (CTabs (v, None, CTif (CTid v, ct1.pterm, ct2.pterm)));
         pary = 0; prec}
      else
        let pary = min ct1.pary ct2.pary in
        let ct1 = shrink_purary ~vars ct1 pary
        and ct2 = shrink_purary ~vars ct2 pary in
        {pterm = CTif (ct.pterm, ct1.pterm, ct2.pterm); prec; pary}
  | Texp_match (e, cases, partial) ->
      let ct = transl_exp ~vars e in
      let ccases = List.map (transl_cases ~vars) cases in
      let lhs, ctl = List.split ccases in
      let prec =
        if List.exists (fun ct -> ct.prec = Recursive) (ct :: ctl)
        then Recursive else Nonrecursive
      in
      let pary =
        if partial = Partial then 0 else
        List.fold_left (fun pary ct -> min pary ct.pary) ct.pary ctl in
      let ctl =
        List.map2 (fun (_, vars) ct -> (shrink_purary ~vars ct pary).pterm)
          lhs ctl
      in
      let ccases = List.combine (List.map fst lhs) ctl in
      let ccases =
        if partial = Partial then ccases @ [CTid"_", CTid"Fail"] else ccases in
      let pterm =
        if ct.pary = 0 then
          let v = fresh_name ~vars "v" in
          ctBind ct.pterm (CTabs (v, None, CTmatch (CTid v, None, ccases)))
        else CTmatch (ct.pterm, None, ccases)
      in
      {pterm; prec; pary}
  | _ ->
      not_allowed ~loc "This kind of term"

and transl_cases ~vars case =
  Option.iter (fun e -> not_allowed ~loc:e.exp_loc "This guard") case.c_guard;
  let ct_lhs, vars = transl_pat ~vars case.c_lhs in
  let ct_rhs = transl_exp ~vars case.c_rhs in
  ((ct_lhs, vars), ct_rhs)

and transl_binding ~vars ~rec_flag vb =
  let name, id =
    match vb.vb_pat.pat_desc with
      Tpat_any -> "_", None
    | Tpat_var (id, _) -> fresh_name ~vars (Ident.name id), Some id
    | Tpat_construct (_, {cstr_name="()"}, [], _) -> "_", None
    | _ -> not_allowed ~loc:vb.vb_pat.pat_loc "This pattern"
  in
  let ty = vb.vb_expr.exp_type in
  (*Format.eprintf "exp_type=%a@." Printtyp.raw_type_expr ty;*)
  let fvars, fvar_names, vars =
    enter_free_variables ~loc:vb.vb_loc ~vars ty in
  let desc =
    {ce_name = name; ce_type = ty; ce_vars = fvars;
     ce_rec = rec_flag; ce_purary = fun_arity vb.vb_expr}
  in
  let vars =
    match rec_flag, id with
    | Recursive, Some id -> add_term (Path.Pident id) desc vars
    | _ -> vars
  in
  let ct = transl_exp ~vars vb.vb_expr in
  let ct, desc, prec =
    match rec_flag with
    | Recursive ->
        let ct = shrink_purary ~vars ct desc.ce_purary in
        insert_guard ct.pterm, desc, Nonrecursive
    | Nonrecursive ->
        ct.pterm, {desc with ce_purary = ct.pary}, ct.prec
  in
  let ct =
     List.fold_right (fun tv ct -> CTabs (tv, Some ml_tid, ct))
       fvar_names ct in
  let ct =
    if rec_flag = Recursive then abstract_recursive ct else ct in
  ((id, desc), {pterm = ct; prec; pary = desc.ce_purary})

let apply_recursive rec_flag ct =
  if rec_flag = Nonrecursive then ct else
  coq_term_subst (Vars.add "h" (CTid"100000") Vars.empty) ct
  (* CTlet ("h", None, CTid"1000", ct) *)

let close_top ~vars ct =
  let fvars = coq_vars ct.pterm in
  let is_pure =
    ct.pary > 0 && Names.disjoint fvars (Names.of_list vars.top_exec) in
  if is_pure then ct.pterm else
  let ct = (nullary ~vars ct).pterm in
  let fvars =
    match vars.top_exec with [] -> fvars | v :: _ -> Names.add v fvars in
  let ct =
    List.fold_left
      (fun ct v ->
        if not (Names.mem v fvars) then ct else
        ctBind (CTapp (CTid"K",[CTid v])) (CTabs (v, None, ct)))
      ct vars.top_exec in
  ctapp ct [CTid "empty_env"]

let rec transl_structure ~vars = function
    [] -> ([], vars)
  | it :: rem -> match it.str_desc with
    | Tstr_eval (e, _) ->
        Ctype.unify_var e.exp_env (Ctype.newvar ()) e.exp_type;
        close_type e.exp_type;
        let pt = transl_exp ~vars e in
        let ct = close_top ~vars pt in
        let ct = apply_recursive pt.prec ct in
        if pt.pary > 0 then
          let cmds, vars = transl_structure ~vars rem in
          (CTeval ct :: cmds, vars)
        else
          let name = fresh_name ~vars "it" in
          let id = Ident.create_local name in
          (* dummy descriptor *)
          let desc =
            {ce_name = name; ce_rec = Nonrecursive; ce_purary = 0;
             ce_type = e.exp_type; ce_vars = []} in
          let vars = add_term ~toplevel:true (Path.Pident id) desc vars in
          let cmds, vars = transl_structure ~vars rem in
          (CTdefinition (name, ct) :: CTeval (CTid name) :: cmds, vars)
    | Tstr_value (rec_flag, [vb]) ->
        let ((id, desc), pt) = transl_binding ~vars ~rec_flag vb in
        let name, vars' =
          match id with
          | Some id ->
              let prec = if pt.pary > 0 then pt.prec else Nonrecursive in
              let desc = {desc with ce_rec = or_rec desc.ce_rec prec} in
              desc.ce_name, add_term ~toplevel:true (Path.Pident id) desc vars
          | None -> assert false
        in
        let cmds, vars' = transl_structure ~vars:vars' rem in
        if desc.ce_rec = Recursive then
          if pt.pary = 0 then
            not_allowed ~loc:it.str_loc "This recursive definition"
          else
            CTfixpoint (name, pt.pterm) :: cmds, vars'
        else
          let ct = close_top ~vars pt in
          let ct =
            if ct = pt.pterm && pt.prec = Recursive
            then abstract_recursive ct
            else apply_recursive pt.prec ct in
          CTdefinition (name, ct) :: cmds, vars'
    | Tstr_type (Recursive, [td]) ->
        let def, vars =
          transl_typedecl ~loc:td.typ_loc ~env:it.str_env ~vars
            td.typ_id td.typ_type in
        let cmds, vars = transl_structure ~vars rem in
        (def :: cmds, vars)
    | _ ->
        not_allowed ~loc:it.str_loc "This structure item"
