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

open Typedtree
open Agdadef
open Agdainit
open Agdacore
open Proof_eq

let rec iota m n = if n <= 0 then [] else m :: iota (m+1) (n-1)
let iota_names m n t =
  List.map (fun i -> t ^ string_of_int i) (iota m n)

let make_ml_type vars =
  let cases =
    List.map
      (fun (_, ctd) ->
        ctd.ct_name,
        List.map (fun _ -> "_", ml_tid) (iota 0 ctd.ct_arity),
        None)
      (Path.Map.bindings vars.type_map)
  in
  CTinductive [{ name = ml_type; args = []; kind = CTsort Set; cases }]

let make_subst = Agdatypes.make_subst ~mkcoq:mkcoqty ~mkml:(fun x -> x)

let make_coq_type vars =
  let make_case (_, ctd) =
    let constr = CTid ctd.ct_name in
    let names = iota_names 1 ctd.ct_arity "T" in
    let types = List.map ctid names in
    let lhs = ctapp constr types
    and rhs =
      let subs = make_subst ctd types in
      coq_term_subst subs ctd.ct_type
    in lhs, rhs
  in
  let cases = List.map make_case (Path.Map.bindings vars.type_map) in
  CTfixpoint ("  coq-type",
              CTabs ("T", Some ml_tid,
                     CTann (CTmatch (CTid "T", None, cases), CTsort Type)))

let retEq = ctRet (CTid "Eq")

let make_compare_rec vars =
  let make_case (_, ctd) =
    let constr = CTid ctd.ct_name in
    let names = iota_names 1 ctd.ct_arity "T" in
    let types = List.map ctid names in
    let lhs = ctapp constr types
    and rhs =
      let ret =
        match ctd.ct_compare, ctd.ct_def with
        | Some ct, _ -> ct
        | None, Some (_, [_,[]]) -> retEq
        | None, Some (ml_params, cases) ->
            let subs =
              Types.Vars.of_seq (List.to_seq (List.combine ml_params types)) in
            let const_cases, nconst_cases =
              List.partition (fun (_,args) -> args = []) cases in
            let cases = const_cases @ nconst_cases in
            let eq_cases =
              List.map (fun (cname, ctl) ->
                let len = List.length ctl in
                let xs = List.map ctid (iota_names 1 len "x")
                and ys = List.map ctid (iota_names 1 len "y") in
                (ctpair (ctcstr cname xs) (ctcstr cname ys),
                 List.fold_right2
                   (fun cty (x,y) ct ->
                     let xy =
                       ctapp (CTid"compare-rec")
                         [coq_term_subst subs cty; x; y] in
                     if ct = retEq then xy else
                     ctapp (CTid"lexi-compare")
                       [xy; ctapp (CTid"Delay") [ct]])
                   ctl (List.combine xs ys) (ctRet (CTid "Eq"))))
                cases in
            let rec mk_neq_cases = function
                [] | [_] -> [] (* last constructor already covered *)
              | (cname, ctl) :: cases ->
                  let cstr =
                    ctcstr cname (List.map (fun _ -> CTid "_") ctl) in
                  [ctpair cstr (CTid "_"), ctRet (CTid "Lt");
                   ctpair (CTid "_") cstr, ctRet (CTid "Gt")]
                  @ mk_neq_cases cases
            in
            let neq_cases = mk_neq_cases cases in
            CTmatch (ctpair (CTid"x") (CTid"y"), None, eq_cases @ neq_cases)
        | None, _ -> ctapp (CTid "Raise")
              [ctapp (CTid "Catchable")
                 [ctapp (CTid"Invalid-argument")
                    [CTcstr"\"compare\""]]]
      in
      CTabs ("x", None, CTabs ("y", None, ret))
    in
    (lhs, rhs)
  in
  CTfixpoint ("compare-rec", CTabs (
              "h", Some (CTid "ℕ"), CTabs (
              "T", Some ml_tid,
              CTann (CTmatch (
              CTid "h", None,
              [CTapp (CTid "S", [CTid "h"]), CTlet (
               "compare-rec", None, ctapp (CTid"compare-rec") [CTid"h"],
               CTmatch (
               CTid "T", Some ("T", CTprod (
                               None, mkcoqty (CTid "T"), CTprod (
                               None, mkcoqty (CTid "T"),
                               CTapp (CTid"M", [CTid "comparator"])))),
               List.map make_case (Path.Map.bindings vars.type_map)));
               CTid "_", CTabs ("_", None, CTabs ("_", None, CTid "FailGas"))]
             ), CTprod (
                     None, mkcoqty (CTid "T"), CTprod (
                     None, mkcoqty (CTid "T"),
                     CTapp (CTid"M", [CTid "comparator"]))))
             )))

let topo_sort (type def) (deps : def -> string * Names.t) (defs : def list) =
  let edges = List.map deps defs in
  let edge id1 id2 =
    try Names.mem id2 (List.assoc id1 edges) with Not_found -> false in
  let rec add (id : string) (dep : Names.t) (groups : string list list) =
    match groups with
      [] -> [[id]]
    | gr :: rem ->
        if List.exists (fun x -> Names.mem x dep) gr then
          let cycle, groups' = get_cycle id groups in
          (id :: cycle) :: groups'
        else
          gr :: add id dep rem
  and get_cycle id = function
      [] -> [], []
    | gr :: rem as groups ->
        let cycle, rem' = get_cycle id rem in
        if cycle <> [] then gr @ cycle, rem' else
        if List.exists (fun x -> edge x id) gr then gr, rem'
        else [], groups
  in
  let groups =
    List.fold_left (fun groups (id,dep) -> add id dep groups) [] edges in
  let id_defs = List.combine (List.map fst edges) defs in
  List.map (List.map (fun id -> List.assoc id id_defs)) groups

let inductive_of_exn vars =
  let constrs =
    match Path.Map.find_opt Predef.path_exn vars.type_map with
      Some {ct_coqdef = constrs} -> constrs
    | _ -> assert false
  in
  let cases =
    List.map
      (fun (cstr, args) -> cstr, List.map (fun ct -> "_", ct) args, None)
      constrs
  in
  CTinductive [{ name = "ml-exns"; args = []; kind = CTsort Type; cases }]

let deps_inductive ind =
  let types =
    List.map snd ind.args @
    List.flatten (List.map (fun (_, args, _) -> List.map snd args) ind.cases)
  in
  let vars = List.map coq_vars types in
  (ind.name, List.fold_left Names.union Names.empty vars)



(*let proof vars =
	let diff_arity_0 ctd1 ctd2 = 
		CTverbatim ("\n" ^ ctd1.ct_name ^ "≢" ^ ctd2.ct_name ^ " : " ^  (* \nequiv *)
		ctd1.ct_name ^ " ≢ " ^ ctd2.ct_name)  ::
		CTverbatim (ctd1.ct_name ^ "≢" ^ ctd2.ct_name ^ " ()") :: [] in

  let ctds = Path.Map.bindings vars.type_map in let res = ref [] in
  for i = 0 to List.length ctds - 1 do
  		for j = i to List.length ctds - 1 do
  			let ctd1 = snd(List.nth ctds i) and ctd2 = snd (List.nth ctds j) in
  			if ctd1.ct_name <> ctd2.ct_name && ctd1.ct_arity = 0 && ctd2.ct_arity = 0 
  			then (res := (diff_arity_0 ctd1 ctd2) @ !res) done; done; 
  	!res*)
let make_proof vars = 
	let rec get_names_and_arities ctds = match ctds with
		| [] -> []
		| ( _, x ) :: q -> (x.ct_name, x.ct_arity) :: (get_names_and_arities q) in
	let ctds = Path.Map.bindings vars.type_map in
	let ctdN_ctdA_list = get_names_and_arities ctds in
	gen_proof ctdN_ctdA_list


let indent_induct n induct = let space = repro n " " in 
	{name = space ^ (induct.name); args = induct.args; kind = induct.kind;
      cases = List.map (fun (s, l1, cto) -> (space ^ s), l1, cto) (induct.cases)}

let indent_ctind n vernac = match vernac with
	| CTinductive ind_list -> CTinductive(List.map (indent_induct n) ind_list)
	| x -> x

let transl_implementation _modname st =
  let cmds, vars = transl_structure ~vars:init_vars st.str_items in
  let typedefs, cmds =
    List.partition (function CTinductive _ -> true | _ -> false) cmds
  in
  let typedefs = typedefs @ [inductive_of_exn vars] in 
  let inductives =
    List.flatten
      (List.map (function CTinductive ind -> ind | _ -> assert false) typedefs)
  in
  let inductives = topo_sort deps_inductive inductives in
  let typedefs = List.map (fun gr -> indent_ctind 2 (CTinductive gr)) inductives in


let _ = make_compare_rec in

  CTverbatim "open import agdagen_defs\
\nopen import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)\
\nopen import Data.Sum using (_⊎_; inj₁; inj₂)\
\nopen import Relation.Binary.Definitions using (DecidableEquality)\
\nopen import Data.Bool using (true; false; Bool; if_then_else_)\
\nopen import Relation.Nullary.Decidable.Core using (_because_; isYes; Dec; yes)\
\nopen import Relation.Nullary.Reflects using (ofʸ; ofⁿ)\
\nopen import Data.String hiding (length; _<?_)\
\nopen import Data.Float using (Float)\
\nopen import Data.Char using (Char)\
\nopen import Data.Nat using (ℕ; suc) renaming (_<?_ to _ℕ<?_)\
\nopen import Data.Unit\
\nopen import Data.List using (List; []; length; _∷_)\
\nopen import Data.Product using (_×_ ; _,_; proj₁ ; proj₂; _,′_)\
\nopen import Data.Empty\
\nopen import Data.Maybe\
\nopen import Relation.Nullary\
\nopen import Relation.Nullary.Decidable\
\nopen import Relation.Binary.PropositionalEquality\
\nopen import Data.Integer\
\nopen import Data.Integer.DivMod using (_%_ ; _/_)\
\nopen import Function.Base using (case_of_)\
\n\n-- Generated representation of all ML types" :: 
  make_ml_type vars ::
  CTverbatim "variable\
\n u1 u2 u3 u4 u5 u6 v1 v2 v3 v4 v5 v6 : ml-type" ::
  CTverbatim (make_proof vars) ::
  CTverbatim "\
\nml-type-eq-dec : DecidableEquality ml-type\
\nml-type-eq-dec = eq-decc\
\n\
\ninstance\
\n    ml-type-is-eq-dec : eqType ml-type\
\n    ml-type-is-eq-dec = record {eq-dec = ml-type-eq-dec}\
\n\
\ndata array-t (T : Set) : Set where\
\n  ArrayVal : List T → array-t T\
\n\
\nmodule MLtypes-aux (M : Set → Set) where\
\n\
\n  -- Generated type definitions\n" :: 
  typedefs @ (* Indentation to handle *)
  CTverbatim "\
\n  data lazy-val (a : Set) : Set where\
\n    LzVal : a → lazy-val a\
\n    LzThunk : (M a) → lazy-val a\
\n    LzExn : ml-exns → lazy-val a\
\n\
\n  loc = loc-b ml-type\
\n\
\n  data lazy-t (a : Set) (a1 : ml-type) : Set where\
\n    Lval : a → lazy-t a a1\
\n    Lref : (loc (ml-lazy-val a1)) → lazy-t a a1\
\n\
\n-- Generated type translation function\n" ::
  make_coq_type vars :: (* needs to be indented *)
  CTverbatim "\
\nopen MLtypes-aux hiding (loc; coq-type)\
\nMLtypes : MLTY\
\nMLtypes = record {\
\n  ml-type = ml-type ;\
\n  coq-type-b = MLtypes-aux.coq-type;\
\n  ml-exn = ml-exn ;\
\n  ml-type-is-eq-dec = ml-type-is-eq-dec\
\n  }\
\n\
\nopen MLTY MLtypes hiding (ml-type)\
\n\
\nREFmonadML : REFmonad MLtypes\
\nREFmonadML = record {}\
\n\
\nopen REFmonad REFmonadML\
\n\
\nempty-env : Env2\
\nempty-env = mkEnv []\
\n\
\nit : W ⊤\
\nit = inj₂ (inj₂ tt , empty-env)\
\n\
\n\n-- Generated comparison function\ "
(*\npostulate compare-rec : (h : ℕ) (T : ml-type)\
  → coq-type T -> coq-type T -> M comparator*) ::
  make_compare_rec vars ::
  CTverbatim "\
\nml-compare = compare-rec\
\n\
\nwrap-compare : (comparator → Bool) → (h : ℕ) → (T : ml-type) → coq-type T → coq-type T → M Bool\
\nwrap-compare wrap h T x y = Do c ← compare-rec h T x y // Ret (wrap c)\
\n\
\nml-eq = wrap-compare (λ {Eq → true ; _ → false })\
\nml-lt = wrap-compare (λ {Lt → true ; _ → false })\
\nml-gt = wrap-compare (λ {Gt → true ; _ → false })\
\nml-ne = wrap-compare (λ {Eq → false ; _ → true })\
\nml-ge = wrap-compare (λ {Lt → false ; _ → true })\
\nml-le = wrap-compare (λ {Gt → false ; _ → true })\
\n" ::
  CTverbatim "-- Array operations\
\nnewarray : (T : ml-type) → ℕ → (x : coq-type T) → M (loc (ml-array-t T))\
\nnewarray T len x = cnew (ml-array-t T) (ArrayVal (ncons len x))\
\n\
\nbounded : ℕ → ℕ → M ℕ\
\nbounded m n = case (n ℕ<? m) of λ {\
                   (yes _) → Ret n ;\
                   _ → Raise BoundedNat }\
\n\
\ngetarray : (T : ml-type) → (a : coq-type (ml-array T)) → (n : ℕ) → M (coq-type T)\
\ngetarray T a n = Do s ← cget (ml-array-t T) a // case s of λ {\
\n                      (ArrayVal u) → Do n ← bounded (length u) n //\
\n                        case u of λ {\
\n                          [] → raise T (Invalid-argument \"getarray\") ;\
\n                          (x ∷ q) → Ret (nth x u n) } }\
\n\
\nsetarray : (T : ml-type) → (a : coq-type (ml-array T)) → (n : ℕ) → (coq-type T) → M ⊤\
\nsetarray T a n x = Do s ← cget (ml-array-t T) a //\
\n                      case s of λ {\
\n                        (ArrayVal u) → Do n ← bounded (length u) n //\
\n                          cput (ml-array-t T) a (ArrayVal (set-nth x u n x)) }\
\n\
\n-- Lazy values\
\nforce : (a : ml-type) → (lz : coq-type (ml-lazy a)) → M (coq-type a)\
\nforce a (Lval x) = Ret x\
\nforce a (Lref r) = Do r' ← cget (ml-lazy-val a) r //\
\n                           (case r' of λ {\
\n                               (LzVal x) → Ret x ;\
\n                               (LzExn e) → raise _ e ;\
\n                               (LzThunk f) → let ff : M (coq-type a)\
\n                                                 ff = f in\
\n                                                    handle _ (Do x ← ff //\
\n                                                       Do _ ← cput (ml-lazy-val a) r (LzVal x) //\
\n                                                       Ret x)\
\n                                                       (λ e → Do _ ← cput _ r (LzExn e) //\
\n                                                              raise _ e) })\
\n\
\nmake-lazy : (a : ml-type) (b : M (coq-type a)) → M (coq-type (ml-lazy a))\
\nmake-lazy a b = Do x ← cnew (ml-lazy-val a) (LzThunk b) // Ret (Lref x)\
\n\
\nmake-lazy-val : (a : ml-type) (b : coq-type a) → coq-type (ml-lazy a)\
\nmake-lazy-val a b = Lval b\
\n\
\n-- Default amount of gas\n\
\nh = 100000\
\n\
\n-- Translated code\n" :: cmds;;

(* \ndata ml-exns : Set where\
\n  Invalid-argument : String → ml-exns\
\n  Failure : String → ml-exns\
\n  Not-found : ml-exns\
*)



