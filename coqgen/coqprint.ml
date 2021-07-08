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

open Coqdef
open Format

let priority_level = function
  | CTid _ -> 10
  | CTcstr _ -> 10
  | CTprod (None, _, _) -> 2
  | CTapp (CTid "*", [_;_]) -> 3
  | CTapp (CTid "Bind", [_;CTabs _]) -> 0
  | CTapp (CTid "@cons", [_;_;_]) -> 0
  | CTapp (CTcstr "@cons", [_;_;_]) -> 0
  | CTapp (CTcstr "|", [_;_]) -> 0
  | CTapp (CTcstr "pair", [_;_]) -> -1
  | CTapp _ -> 8
  | CTabs _ -> 0
  | CTsort _ -> 10
  | CTprod _ -> 0
  | CTmatch _ -> 10
  | CTann _ -> 10
  | CTlet _ -> 0
  | CTif _ -> 0

let string_of_sort = function
  | Type -> "Type"
  | Set -> "Set"
  | Prop -> "Prop"

let rec extract_args = function
  | CTabs (x, cto, ct) ->
      let (args, ct, ann) = extract_args ct in
      begin match args with
      | (argl, cto') :: args when cto = cto' ->
          (x :: argl, cto) :: args, ct, ann
      | _ -> ([x], cto) :: args, ct, ann
      end
  | CTann (ct, ann) -> ([], ct, Some ann)
  | ct -> ([], ct, None)

let rec print_term_rec lv ppf ty =
  if lv > priority_level ty then fprintf ppf "(%a)" (print_term_rec (-1)) ty
  else match ty with
  | CTid s | CTcstr s -> pp_print_string ppf s
  | CTprod (None, t1, t2) ->
      fprintf ppf "@[%a ->@ %a@]" (print_term_rec 3) t1 (print_term_rec 2) t2
  | CTapp (CTid "*", [t1; t2]) ->
      fprintf ppf "@[%a ->@ %a@]" (print_term_rec 3) t1 (print_term_rec 8) t2
  | CTapp (CTid "Bind", [ct1; CTabs (x, cto, ct2)]) ->
      fprintf ppf "@[do %s%a <-@ %a;@ %a@]"
        x print_type_ann cto
        (print_term_rec 1) ct1
        print_term ct2
  | CTapp (CTid "S", [t1]) ->
      fprintf ppf "@[%a.+1@]" (print_term_rec 10) t1
  | CTapp (CTid "@cons", [_;t1;t2])
  | CTapp (CTcstr "@cons", [_;t1;t2]) ->
      fprintf ppf "@[%a ::@ %a@]" (print_term_rec 8) t1 (print_term_rec 0) t2
  | CTapp (CTcstr "|", [t1;t2]) ->
      fprintf ppf "@[%a |@ %a@]" (print_term_rec lv) t1 (print_term_rec lv) t2
  | CTapp (CTcstr "pair", [t1;t2]) ->
      fprintf ppf "@[%a,@ %a@]" (print_term_rec (-1)) t1 (print_term_rec 0) t2
  | CTapp (f, args) ->
      fprintf ppf "@[<2>%a@ %a@]" (print_term_rec 8) f
        (pp_print_list ~pp_sep:pp_print_space (print_term_rec 9)) args
  | CTabs _ ->
      fprintf ppf "@[<hov2>@[<hov2>fun";
      let t1 = print_args false ppf ty in
      fprintf ppf "@ =>@]@ %a@]" print_term t1
  | CTsort k -> pp_print_string ppf (string_of_sort k)
(*  | CTtuple tl ->
      fprintf ppf "(@[%a)@]"
        (pp_print_list (print_term_rec 1)
           ~pp_sep:(fun ppf () -> fprintf ppf ",@ "))
        tl *)
  | CTprod (Some x, t, t1) ->
      fprintf ppf "@[<hov2>@[<hov2>forall@ %s@ :@ %a@]@ %a@]"
        x print_term t print_term t1
  | CTmatch (ct, None, [(p1,ct1); (CTid"_",ct2)]) ->
      fprintf ppf
        "@[<hv>@[<2>@[<2>if@ %a@ is@ %a@]@;<1 -2>then@ %a@]@ @[<2>else@ %a@]@]"
        print_term ct
        print_term p1
        print_term ct1
        print_term ct2
  | CTmatch (ct, oret, cases) ->
      fprintf ppf "@[<hv>@[<2>match@ %a" (print_term_rec (-1)) ct;
      Option.iter
        (fun (v, ct) ->
          fprintf ppf "@ as@ %s@ return@ %a" v print_term ct)
        oret;
      fprintf ppf "@ with@]";
      List.iter
        (fun (pat, ct) ->
          fprintf ppf "@ @[@[| %a =>@]@;<1 2>%a@]"
            (print_term_rec (-1)) pat
            print_term ct)
        cases;
      fprintf ppf "@ end@]"
  | CTann (ct, cty) ->
      fprintf ppf "@[<1>(%a :@ %a)@]"
        print_term ct
        print_term cty
  | CTlet (x, None, ct1, ct2) ->
      fprintf ppf "@[<2>@[let %s" x;
      let ct1 = print_args true ppf ct1 in
      fprintf ppf "@ :=@]@ %a@ in@;<1 -2>%a@]"
        print_term ct1
        print_term ct2
  | CTlet (x, cto, ct1, ct2) ->
      fprintf ppf "@[<2>@[let %s%a :=@]@ %a@;<1 -2>in@ %a@]"
        x print_type_ann cto
        print_term ct1
        print_term ct2
  | CTif (ct1, ct2, ct3) ->
      fprintf ppf "@[if@;<1 2>%a@ then@;<1 2>%a@ else@;<1 2>%a@]"
        print_term ct1
        print_term ct2
        print_term ct3

and print_type_ann ppf = function
  | None -> ()
  | Some t -> fprintf ppf "@ : %a" (print_term_rec 0) t

and print_term ppf = print_term_rec 0 ppf

and print_args is_def ppf ct =
  let (args, ct, ann) = extract_args ct in
  let one_group = not is_def && List.length args = 1 in
  List.iter
    (fun (argl,cto) ->
      match cto with
      | None -> List.iter (fprintf ppf "@ %s") argl
      | _ when not is_def && List.for_all ((=) "_") argl ->
          List.iter (fprintf ppf "@ %s") argl
      | Some ct ->
          let po, pc = if one_group then "", "" else "(", ")" in
          fprintf ppf "@ @[<1>%s" po;
          List.iter (fprintf ppf "%s@ ") argl;
          fprintf ppf ":@ %a%s@]" print_term ct pc)
    args;
  (*if List.exists (fun (l,_) -> List.mem "h" l) args then
    fprintf ppf "@ {struct h}";*)
  if is_def then print_type_ann ppf ann;
  ct
  (* else may_app (fun cty ct -> CTann (ct, cty)) ann ct *)

let emit_def ppf def s ct =
  fprintf ppf "@[<2>@[<2>%s %s" def s;
  let ct = print_args true ppf ct in
  fprintf ppf " :=@]@ %a.@]" print_term ct;
  let is_it = s = "it" || String.length s >= 3 && String.sub s 0 3 = "it_" in
  if not is_it then pp_print_newline ppf ()

let print_arg_typed ppf (s, ct) =
  fprintf ppf "@ @[<1>(%s :@ %a)@]" s print_term ct

let emit_vernacular ppf = function
  | CTverbatim s            -> fprintf ppf "%s" s
  | CTdefinition (s, ct) -> emit_def ppf "Definition" s ct
  | CTfixpoint (s, ct)   -> emit_def ppf "Fixpoint" s ct
  | CTeval ct ->
      fprintf ppf "@[<2>Eval vm_compute in@ %a.@]@ " print_term ct
  | CTinductive td ->
      fprintf ppf "@[<hv2>@[<2>Inductive %s" td.name;
      List.iter (print_arg_typed ppf) td.args;
      fprintf ppf "@ :=@]";
      let bar = if List.length td.cases = 1 then "" else "| " in
      List.iter
        (fun (s, args, ret) ->
          fprintf ppf "@ @[<2>%s%s" bar s;
          List.iter (print_arg_typed ppf) args;
          match ret with
          | None -> fprintf ppf "@]"
          | Some ret -> fprintf ppf "@ : %a@]" print_term ret)
        td.cases;
      fprintf ppf ".@]@ "

let emit_gallina _modname ppf cmds =
  pp_print_list ~pp_sep:pp_print_newline emit_vernacular ppf cmds
