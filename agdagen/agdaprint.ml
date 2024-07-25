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

open Agdadef
open Format

let priority_level = function
  | CTid _ -> 10
  | CTcstr _ -> 10
  | CTprod (None, _, _) -> 2
  | CTapp (CTid "*", [_;_]) -> 3
  | CTapp (CTid "Bind", [_; CTabs _]) -> 0
  | CTapp (CTid "@cons", [_;_;_]) -> 0
  | CTapp (CTcstr "@cons", [_;_;_]) -> 0
  | CTapp (CTcstr "|", [_;_]) -> 0
  | CTapp (CTcstr "pair", [_;_]) -> -1
  | CTapp _ -> 8
  | CTabs _ -> 0
  | CTsort _ -> 10
  | CTprod _ -> 0
  | CTmatch _ -> 8
  | CTann _ -> 10
  | CTlet _ -> 0
  | CTif _ -> 0

let string_of_sort = function
  | Type -> "Set"
  | Set -> "Set"	(* to do ?*)
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

(* for DEBUG only *)
let rec str_of_ct = (function
      CTid x -> "(CTid " ^ x ^ ")"
    | CTcstr x -> "(CTcstr " ^ x ^ ")"
    | CTapp (ct, l) -> "CTapp (" ^ (str_of_ct ct) ^ (String.concat "\n     " (List.map str_of_ct l))
    | CTabs (x,_,ct) -> "CTabs (" ^ x ^ ", " ^ (str_of_ct ct) ^ ")"
    | CTsort _ -> "CTsort"
    | CTprod _ -> "CTprod"
    | CTmatch (ct,_,ctcl) -> "CTmatch " ^ (str_of_ct ct) ^ " with " ^
  			     (String.concat "@.\n     "
  			        (List.map (fun (u,v) -> (str_of_ct u) ^ " -> " ^ (str_of_ct v)) ctcl))
    | CTann (ct1, ct2) -> "CTann (" ^ (str_of_ct ct1) ^ "," ^ (str_of_ct ct2) ^ ")"
    | CTlet _ -> "CTlet"
    | CTif _ -> "CTif")

let () = ignore str_of_ct

(* for printing unicode characters with module Format*)
let uc ppf = pp_print_as ppf 1

let rec print_term_rec lv ppf ty =
  if lv > priority_level ty then fprintf ppf "(%a)" (print_term_rec (-1)) ty
  else match ty with
    | CTid s | CTcstr s -> pp_print_string ppf s
    | CTprod (None, t1, t2) ->
        fprintf ppf "@[%a %a@ %a@]" (print_term_rec 3) t1 uc "→" (print_term_rec 2) t2
    | CTapp (CTid "*", [t1; t2]) ->
        fprintf ppf "@[%a %a@ %a@]" (print_term_rec 3) t1 uc "→" (print_term_rec 8) t2
    | CTapp (CTid "Bind", [ct1; CTabs (x, _, ct2)]) ->
        fprintf ppf "@[<v3>do @[<hov1>%s %a@ %a@]@,%a@]"
          x
          uc "←"
          (print_term_rec 0) ct1
          print_term ct2
    | CTapp (CTid "S", [t1]) ->
        fprintf ppf "@[suc %a@]" (print_term_rec 10) t1
    | CTapp (CTid "@cons", [_;t1;t2])
    | CTapp (CTcstr "@cons", [_;t1;t2])
    | CTapp (CTid "@cons", [t1;t2])
    | CTapp (CTcstr "@cons", [t1;t2])->
        fprintf ppf "@[%a %a@ %a@]" (print_term_rec 8) t1 uc "∷" (print_term_rec 0) t2 (* constructor for lists *)
    | CTapp (CTcstr "|", [t1;t2]) ->
        fprintf ppf "@[%a |@ %a@]" (print_term_rec lv) t1 (print_term_rec lv) t2
    | CTapp (CTcstr "pair", [t1;t2]) ->
        fprintf ppf "@[%a ,@ %a@]" (print_term_rec (-1)) t1 (print_term_rec 0) t2
    | CTapp (f, args) ->
        fprintf ppf "@[<2>%a@ %a@]" (print_term_rec 8) f (* traductions of constructors and functions *)
          (pp_print_list ~pp_sep:pp_print_space (print_term_rec 9)) args
    | CTabs _ ->
        fprintf ppf "@[<hov2>@[<hov2>%a" uc "λ";
        let t1 = print_args ~no_types:true false ppf ty in
        fprintf ppf "@ %a@]@ %a@]" uc "→" print_term t1
    | CTsort k -> pp_print_string ppf (string_of_sort k)
    (*  | CTtuple tl ->
          fprintf ppf "(@[%a)@]"
            (pp_print_list (print_term_rec 1)
               ~pp_sep:(fun ppf () -> fprintf ppf ",@ "))
            tl *)
    | CTprod (Some x, t, t1) ->
        fprintf ppf "@[<hov2>@[<hov2>forall@ %s@ :@ %a@]@ %a@]"
          x print_term t print_term t1
    (* | CTmatch (ct, None, [(p1,ct1); (CTid"_",ct2)]) ->
        fprintf ppf
          "@[<hv>@[<2>@[<2>if@ %a@ is@ %a@]@;<1 -2>then@ %a@]@ @[<2>else@ %a@]@]"
          print_term ct
          print_term p1
          print_term ct1
          print_term ct2 *)
    | CTmatch (ct, oret, cases) ->
        ignore oret;
        fprintf ppf "@[<v 2>case %a" (print_term_rec (-1)) ct;
        fprintf ppf " of %a {" uc "λ";
        let first = ref true in
        List.iter
          (fun (pat, ct) -> (* pat: pattern *)
             if not !first then fprintf ppf "@ ; " else (fprintf ppf "@,"; first := false);
             fprintf ppf "@[@[(%a) %a@]@;<1 2>%a@]"
               (print_term_rec (-1)) pat
               uc "→"
               print_term ct)
          cases;
        fprintf ppf "@ }@]";
    | CTann (ct, _) ->
        fprintf ppf "@[<1>(%a)@]" print_term ct
    | CTlet (x, None, ct1, ct2) ->
        fprintf ppf "let @[<2>@[<v>%s" x;
        let args, _, _ = extract_args ct1 in
        let is_a_function_def = args <> [] in
        if is_a_function_def
        then (fprintf ppf " :@[";);
        let ct1a = print_args is_a_function_def ~print_arrow:is_a_function_def ppf ct1 in 
        (* if not a function defintion, i don't need not to print anything *)
        if is_a_function_def
        then (fprintf ppf "@]@,%s@[" x;
      	      let _ = print_args ~no_types:true false ppf ct1 in ();
      	      fprintf ppf " @]")
        else (fprintf ppf " ");
        fprintf ppf "=@]@ %a@ in@;<1 2>%a@]"
          print_term ct1a
          print_term ct2
    | CTlet (x, cto, ct1, ct2) ->
        fprintf ppf "@[<2>@[let %s%a =@]@ %a@;<1 -2>in@ %a@]"
          x print_type_ann cto
          print_term ct1
          print_term ct2
    | CTif (ct1, ct2, ct3) ->
        fprintf ppf "@[<hov1>if@;<1 2>%a@ then@;<1 2>%a@ else@;<1 2>%a@]"
          (print_term_rec 1) ct1
          (print_term_rec 1) ct2
          (print_term_rec 1) ct3

and print_type_ann ppf = function
  | None -> ()
  | Some t -> fprintf ppf " %a" (print_term_rec 0) t

and print_term ppf = print_term_rec 0 ppf

and print_args ?(s="") ?(no_types=false) ?(print_arrow=false) is_def ppf ct =
  let (args, ct, ann) = extract_args ct in
  ignore s;
  let one_group = not is_def && List.length args = 1 in
  let n = List.length args in
  List.iteri
    (fun j (argl,cto) ->
       let r =
         match cto with
         | None -> List.iter (fprintf ppf "@ %s") argl
         | _ when (not is_def && List.for_all ((=) "_") argl) || no_types ->
             List.iter (fprintf ppf "@ %s") argl
         | Some ct ->
             let po, pc = if one_group then "", "" else "(", ")" in
             fprintf ppf "@ @[<1>%s" po;
             List.iter (fprintf ppf "%s@ ") argl;
             fprintf ppf ":@ %a%s@]" print_term ct pc in
       if j = n-1 && print_arrow then fprintf ppf "@ →";
       r)
    args;
  if is_def then print_type_ann ppf ann;
  ct


let emit_def ppf def s ~eval ct =
  ignore eval;
  let add_new_line = ref true in
  (match ct with
   | CTapp (CTid "Restart" , [_ ; _]) -> add_new_line := false; fprintf ppf "@["
   | _ -> fprintf ppf "@[<2>%s%s :" def s);
  let ct2 = print_args ~s:s ~print_arrow:true true ppf ct in
  fprintf ppf "@]";
  if !add_new_line then fprintf ppf "@,";
  fprintf ppf "@[<2>%s" s;
  let _ = print_args ~no_types:true false ppf ct in
  fprintf ppf " =@;<1 2>";
  fprintf ppf "%a@]" print_term ct2



let print_arg_typed ?(brackets=false) ppf (s, ct) = (* used to print the arguments of a constructor *)
  if s = "" || s = "_"
  then fprintf ppf "@ @[<1>(%a)@ %a@]" print_term ct uc "→"
  else
    begin
      if brackets then     (* polymorphic parameters of gadts constructors are optional *)
        fprintf ppf "@ @[<1>{%s : %a}@ %a@]" s print_term ct uc "→"
      else
        fprintf ppf "@ @[<1>(%s : %a)@ %a@]" s print_term ct uc "→" 
    end

let print_arg_typed_data_def ppf (s, ct) = (* used to print the parameters in a datatype declaration *)
  fprintf ppf "@ @[<1>(%s :@ %a)@]" s print_term ct

let print_arg_untyped_data ppf (s, _) = (* used to print the parameters in a datatype declaration *)
  fprintf ppf "@ @[<1>%s@]" s

let newlines = ref 1

let vv = ref 0
let fresh_v () =
  incr vv; string_of_int !vv

let rec repro s n = match n with
  | 0 -> ""
  | n -> s ^ (repro s (n-1))

let print_set ppf res = match res with
  | None -> fprintf ppf " :@ Set"
  | Some CTapp (_, l) ->     (* gadt *)
      begin
        let n = List.length l in
        fprintf ppf " :%s" (repro " Set →" n);
        fprintf ppf "@ Set₁"     (* all gadts are Set₁ *)
      end
  | _ -> fprintf ppf " :@ Set"

let emit_vernacular ppf = function
  | CTverbatim s  -> fprintf ppf  (CamlinternalFormat.format_of_string_format s "")
  | CTdefinition (s, ct, eval) ->
      emit_def ppf "" s ~eval ct
  | CTfixpoint (s, ct) -> emit_def ppf "" s ~eval:false ct
  | CTeval ct ->
      emit_def ppf "" ("-Eval" ^ fresh_v ()) ~eval:true ct
  | CTinductive tds ->
      let n = List.length tds in
      let mutual = n > 1 in
      if mutual     (* mutually recursive datatype declaration  *)
      then (List.iter     (* generates all the signatures of the mutual types  *)
      	      (fun td ->
      	  	 fprintf ppf "@[<hv2>data %s" td.name;
      	  	 List.iter (print_arg_typed_data_def ppf) td.args;
      	  	 fprintf ppf " :@ Set@]@,@,")
      	      tds);
      List.iteri
        (fun i td ->
           fprintf ppf "@[<v2>@[<hv2>data";
           fprintf ppf " %s" td.name;
           (if not mutual then     (* signature for non-mutual datatype declaration *)
              begin
                List.iter (print_arg_typed_data_def ppf) td.args;
                let (_,_,res) = List.nth td.cases 0 in print_set ppf res
              end
            else
              List.iter (print_arg_untyped_data ppf) td.args);
           fprintf ppf " where@]";
           List.iter
             (fun (s, args, oret) ->     (* for each constructor... *)
                fprintf ppf "@ @[<2>%s :" s;     (* ...we print its name... *)
                (* polymorphic parameters of gadts constructors are optional thus printed between "{}" *)
                List.iter     (* ... its arguments...*)
                  (print_arg_typed ~brackets: (oret <> None) ppf)
                  args;
                (match oret with     (* ...and the return type it instantiates *)
                 | None -> fprintf ppf "@ %s" (td.name);     (* non-gadt  *)
                     List.iter (print_arg_untyped_data ppf) td.args
                 | Some cto -> fprintf ppf "@ %a" print_term cto);     (* gadt  *)
                fprintf ppf "@]")
             td.cases;
           fprintf ppf "@]";
           if mutual && (i <> n-1) then fprintf ppf "@,@,")
        tds;
      newlines := 1


let print_newlines ppf () =
  for _ = 1 to !newlines do fprintf ppf "@,@," done; newlines := 1


let emit_gallina _modname ppf cmds =
  pp_print_list ~pp_sep:print_newlines emit_vernacular ppf cmds



