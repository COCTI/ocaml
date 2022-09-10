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
open Coqdef
open Coqinit
open Coqcore

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

let make_subst = Coqtypes.make_subst ~mkcoq:mkcoqty ~mkml:(fun x -> x)

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
  CTfixpoint ("coq_type",
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
                       ctapp (CTid"compare_rec")
                         [coq_term_subst subs cty; x; y] in
                     if ct = retEq then xy else
                     ctapp (CTid"lexi_compare")
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
        | None, _ -> ctapp (CTid "Fail")
              [ctapp (CTid "Catchable")
                 [ctapp (CTid"Invalid_argument")
                    [CTcstr"\"compare\"%string"]]]
      in
      CTabs ("x", None, CTabs ("y", None, ret))
    in
    (lhs, rhs)
  in
  CTfixpoint ("compare_rec", CTabs (
              "h", Some (CTid "nat"), CTabs (
              "T", Some ml_tid,
              CTann (CTmatch (
              CTid "h", None,
              [CTapp (CTid "S", [CTid "h"]), CTlet (
               "compare_rec", None, ctapp (CTid"compare_rec") [CTid"h"],
               CTmatch (
               CTid "T", Some ("T", CTprod (
                               None, mkcoqty (CTid "T"), CTprod (
                               None, mkcoqty (CTid "T"),
                               CTapp (CTid"M", [CTid "comparison"])))),
               List.map make_case (Path.Map.bindings vars.type_map)));
               CTid "_", CTabs ("_", None, CTabs ("_", None, CTid "FailGas"))]
             ), CTprod (
                     None, mkcoqty (CTid "T"), CTprod (
                     None, mkcoqty (CTid "T"),
                     CTapp (CTid"M", [CTid "comparison"]))))
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
  CTinductive [{ name = "ml_exns"; args = []; kind = CTsort Type; cases }]

let deps_inductive ind =
  let types =
    List.map snd ind.args @
    List.flatten (List.map (fun (_, args, _) -> List.map snd args) ind.cases)
  in
  let vars = List.map coq_vars types in
  (ind.name, List.fold_left Names.union Names.empty vars)

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
  let typedefs = List.map (fun gr -> CTinductive gr) inductives in

  CTverbatim "From mathcomp Require Import ssreflect ssrnat seq.\
\nRequire Import PrimInt63 Ascii String Floats cocti_defs.\
\n\n(* Generated representation of all ML types *)" ::
  make_ml_type vars ::
  CTverbatim "(* Module argument for monadic functor *)\
\nModule MLtypes.\
\nDefinition ml_type_eq_dec (T1 T2 : ml_type) : {T1=T2}+{T1<>T2}.\
\nrevert T2; induction T1; destruct T2;\
\n  try (right; intro; discriminate); try (now left);\
\n  try (case (IHT1_5 T2_5); [|right; injection; intros; contradiction]);\
\n  try (case (IHT1_4 T2_4); [|right; injection; intros; contradiction]);\
\n  try (case (IHT1_3 T2_3); [|right; injection; intros; contradiction]);\
\n  try (case (IHT1_2 T2_2); [|right; injection; intros; contradiction]);\
\n  (case (IHT1 T2) || case (IHT1_1 T2_1)); try (left; now subst);\
\n    right; injection; intros; contradiction.\
\nDefined.\n\
\nLocal Definition ml_type := ml_type.\
\nRecord key := mkkey {key_id : int; key_type : ml_type}.\
\nVariant loc : ml_type -> Type := mkloc : forall k : key, loc (key_type k).\
\n\
\nSection with_monad.\
\nContext [M : Type -> Type].\
\n\n(* Generated type definitions *)" ::
  typedefs @
  CTverbatim "\
\nInductive lazy_val (a : Type) :=\
\n  LzVal of a | LzThunk of M a | LzExn of ml_exns.\
\nInductive lazy_t a a1 := Lval of a | Lref of (loc (ml_lazy_val a1)).\
\n\
\nLocal (* Generated type translation function *)" ::
  make_coq_type vars ::
  CTverbatim "End with_monad.\
\nLocal Definition ml_exn := ml_exn.\
\nEnd MLtypes.\
\nExport MLtypes.\
\n\
\nModule REFmonadML := REFmonad (MLtypes).\
\nExport REFmonadML.\
\n\
\nDefinition coq_type := @MLtypes.coq_type M.\
\nDefinition empty_env := mkEnv 0%int63 nil.\
\nDefinition it : W unit := (empty_env, inl tt).\
\n\n(* Generated comparison function *)" ::
  make_compare_rec vars ::
  CTverbatim "Definition ml_compare := compare_rec.\
\n\
\nDefinition wrap_compare wrap T h x y : M bool :=\
\n  do c <- compare_rec T h x y; Ret (wrap c).\
\n\
\nDefinition ml_eq := wrap_compare (fun c => if c is Eq then true else false).\
\nDefinition ml_lt := wrap_compare (fun c => if c is Lt then true else false).\
\nDefinition ml_gt := wrap_compare (fun c => if c is Gt then true else false).\
\nDefinition ml_ne := wrap_compare (fun c => if c is Eq then false else true).\
\nDefinition ml_ge := wrap_compare (fun c => if c is Lt then false else true).\
\nDefinition ml_le := wrap_compare (fun c => if c is Gt then false else true).\
\n" ::
  CTverbatim "(* Array operations *)\
\nDefinition newarray T len (x : coq_type T) :=\
\n  do len <- nat_of_int len; newref (ml_array_t T) (ArrayVal _ (nseq len x)).\
\nDefinition getarray T (a : coq_type (ml_array T)) n : M (coq_type T) :=\
\n  do s <- getref (ml_array_t T) a;\
\n  let: ArrayVal s := s in\
\n  do n <- bounded_nat_of_int (seq.size s) n;\
\n  if s is x :: _ then Ret (nth x s n) else\
\n  raise _ (Invalid_argument \"getarray\").\
\nDefinition setarray T (a : coq_type (ml_array T)) n (x : coq_type T) :=\
\n  do s <- getref (ml_array_t T) a;\
\n  let: ArrayVal s := s in\
\n  do n <- bounded_nat_of_int (seq.size s) n;\
\n  setref (ml_array_t T) a (ArrayVal _ (set_nth x s n x)).\
\n\n(* Lazy values *)\
\nDefinition force a (lz : coq_type (ml_lazy a)) :=\
\n  match lz with\
\n  | Lval x => Ret x\
\n  | Lref r =>\
\n    do r' <- getref (ml_lazy_val a) r;\
\n    match r' with\
\n    | LzVal x => Ret x\
\n    | LzExn e => raise _ e\
\n    | LzThunk f => handle _\
\n        (do x <- f; do _ <- setref (ml_lazy_val a) r (LzVal _ x); Ret x)\
\n        (fun e => do _ <- setref _ r (LzExn _ e); raise _ e)\
\n    end\
\n  end.\
\nDefinition make_lazy a (b : M (coq_type a)) : M (coq_type (ml_lazy a)) :=\
\n  do x <- newref (ml_lazy_val a) (LzThunk _ b); Ret (Lref _ _ x).\
\nDefinition make_lazy_val a (b : coq_type a) : coq_type (ml_lazy a) :=\
\n  Lval _ _ b.\
\n\n(* Default amount of gas *)\
\nDefinition h := 100000.\
\n\n(* Translated code *)\n"
  :: cmds
