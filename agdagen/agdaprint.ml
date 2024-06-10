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
  | CTapp (CTid "Bind", [_;CTabs _]) -> -1
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

let ignore _ = ()

(*let is_constructor_name s =
	let is_uppercase c = 
		Char.equal c (Char.uppercase_ascii c) in
	is_uppercase (s.[0]) && not (String.equal s "List") && not (String.equal s "M")*)


let rec print_term_rec lv ppf ty =
  if lv > priority_level ty then fprintf ppf "(%a)" (print_term_rec (-1)) ty
  else match ty with
  | CTid s | CTcstr s -> pp_print_string ppf s
  | CTprod (None, t1, t2) ->
      fprintf ppf "@[%a →@ %a@]" (print_term_rec 3) t1 (print_term_rec 2) t2
  | CTapp (CTid "*", [t1; t2]) ->
      fprintf ppf "@[%a →@ %a@]" (print_term_rec 3) t1 (print_term_rec 8) t2
  | CTapp (CTid "Bind", [ct1; CTabs (x, cto, ct2)]) ->
      fprintf ppf "@[Do %s%a ←@ %a //@ %a@]"
        x print_type_ann cto
        (print_term_rec 1) ct1
        print_term ct2
  | CTapp (CTid "S", [t1]) ->
      fprintf ppf "@[suc %a@]" (print_term_rec 10) t1
  | CTapp (CTid "@cons", [_;t1;t2])
  | CTapp (CTcstr "@cons", [_;t1;t2]) ->
      fprintf ppf "@[%a ∷@ %a@]" (print_term_rec 8) t1 (print_term_rec 0) t2 (* constructor for lists *)
  | CTapp (CTcstr "|", [t1;t2]) ->
      fprintf ppf "@[%a |@ %a@]" (print_term_rec lv) t1 (print_term_rec lv) t2
  | CTapp (CTcstr "pair", [t1;t2]) ->
      fprintf ppf "@[%a ,@ %a@]" (print_term_rec (-1)) t1 (print_term_rec 0) t2
  (*| CTapp (CTid s, _) when is_constructor_name s -> fprintf ppf "@[<2>%a@]" pp_print_string s*)
  | CTapp (f, args) ->
      fprintf ppf "@[<2>%a@ %a@]" (print_term_rec 8) f (* traductions of constructors and functions *)
        (pp_print_list ~pp_sep:pp_print_space (print_term_rec 9)) args
  | CTabs _ ->
      fprintf ppf "@[<hov2>@[<hov2>λ";
      let t1 = print_args ~no_types:true false ppf ty in
      fprintf ppf "@ →@]@ %a@]" print_term t1
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
      fprintf ppf "@[<v 2>case %a" (print_term_rec (-1)) ct; (* called when there is a match in a function *)
      (* Option.iter
        (fun (v, ct) ->
          fprintf ppf "@ as@ %s@ return@ %a" v print_term ct) (* Don't know what this does yet *)
        oret; *)
      fprintf ppf " of λ {";
      let first = ref true in
      List.iter
        (fun (pat, ct) -> (* pat: pattern *)
        	 if not !first then fprintf ppf "@ ; " else (fprintf ppf "@,"; first := false); 
          fprintf ppf "@[@[(%a) →@]@;<1 2>%a@]"
            (print_term_rec (-1)) pat
            print_term ct)
        cases;
      fprintf ppf "@ }@]";

  | CTann (ct, cty) ->
      (*fprintf ppf "@[<1>(%a :@ %a)@]"
        print_term ct
        print_term cty*)
      ignore cty;
      fprintf ppf "@[<1>(%a)@]" print_term ct
  | CTlet (x, None, ct1, ct2) ->
      fprintf ppf "let @[<2>@[<v>%s" x;
      let args, _, _ = extract_args ct1 in
      let is_a_function_def = args <> [] in
      if is_a_function_def
      then (fprintf ppf " :@[";);
      let ct1a = print_args is_a_function_def ~print_arrow:is_a_function_def ppf ct1 in (* if not a function defintion, i don't need not to print anything *)
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
      fprintf ppf "@[if@;<1 2>%a@ then@;<1 2>%a@ else@;<1 2>%a@]"
        print_term ct1
        print_term ct2
        print_term ct3

and print_type_ann ppf = function
  | None -> ()
  | Some t -> fprintf ppf " %a" (print_term_rec 0) t

and print_term ppf = print_term_rec 0 ppf

and print_args ?(s="") ?(no_types=false) ?(print_arrow=false) is_def ppf ct =
  let (args, ct, ann) = extract_args ct in
  if is_def then (
  Format.eprintf "name: %s@.args: " s;
  List.iter (fun x -> let argh = fst x in List.iter (Format.eprintf "%s ")  argh) args;
  Format.eprintf "@.returns: ";
  if is_def then print_type_ann Format.err_formatter ann;
    Format.eprintf "@.@.");
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
  (*if List.exists (fun (l,_) -> List.mem "h" l) args then
    fprintf ppf "@ {struct h}";*)
  if is_def then print_type_ann ppf ann;
  ct
  (* else may_app (fun cty ct -> CTann (ct, cty)) ann ct *)

let emit_def ?(ann=None) ppf def s ~eval ct =
  ignore eval;
  (match ct with
  		| CTapp (CTid "Restart" , _) -> fprintf ppf "@["
  		| _ -> fprintf ppf "@[<2>%s%s :" def s);
  let ct2 = print_args ~s:s ~print_arrow:true true ppf ct in
  (if ann <> None then print_type_ann ppf ann);
  fprintf ppf "@]@,@[<2>%s" s;
  let _ = print_args ~no_types:true false ppf ct in
  fprintf ppf " =@;<1 2>";
  fprintf ppf "%a@]" print_term ct2
  (*let is_it = s = "it" || String.length s >= 3 && String.sub s 0 3 = "it_" in
  if not is_it then pp_print_newline ppf ()*)


let print_arg_typed ppf (_, ct) = (* used to print the arguments of a constructor *)
  fprintf ppf "@ @[<1>%a@]" print_term ct;
  fprintf ppf "@ →"
  (* fprintf ppf "@ @[<1>(%s :@ %a)@]" s print_term ct;*)
  (* first_arrow := true *)

let print_arg_typed_data_def ppf (s, ct) = (* used to print the parameters in a dataype declaration *)
	fprintf ppf "@ @[<1>(%s :@ %a)@]" s print_term ct

let print_arg_untyped_data ppf fs (s, _) = (* used to print the parameters in a dataype declaration *)
	if !fs 
	then fprintf ppf "@ @[<1>%s@]" s
	else (fprintf ppf "@ @[<1> %s@]" s; fs := false)


let newlines = ref 1

let rec repro n s = match n with
	| 0 -> ""
	| n -> s ^ (repro (n-1) s)

let get_begin_spaces name = 
	let indentation_opt = String.rindex_opt name ' ' in
      let nb_spaces = match indentation_opt with
      	| None -> 0
      	| Some x -> x + 1 in repro nb_spaces " "

let vv = ref 0
let fresh_v () = 
	incr vv; string_of_int !vv

let emit_vernacular ppf = function
  | CTverbatim s  -> fprintf ppf  (CamlinternalFormat.format_of_string_format s "")
  (*| CTdefinition (s, CTann(ct, cty), eval) -> emit_def ~ann:(Some cty) ppf "" s ~eval ct*)
  | CTdefinition (s, ct, eval) ->
      emit_def ppf "" s ~eval ct
  | CTfixpoint (s, ct) -> emit_def ppf "" s ~eval:false ct
  | CTeval ct ->
      emit_def ppf "" ("-Eval" ^ fresh_v ()) ~eval:true ct
      (*fprintf ppf "@[<2>let -A = %a@]" print_term ct;
      newlines := 2*)
  | CTinductive tds ->
      let first = ref true in
      List.iter (fun td ->
        let begin_spaces = get_begin_spaces td.name in
        fprintf ppf "@[<v2>@[<hv2>%sdata" begin_spaces;
        if !first then first := false
        else fprintf ppf "@]@ @[<hv2>@[<2>with"; 
        (* I dont know what the line above does yet 
			  Probably useful for mutually recursive inductive types 
			  See https://coq.inria.fr/doc/V8.18.0/refman/language/core/inductive.html#simple-inductive-types 
			  Section Mutually recursive inductive types *)
        fprintf ppf " %s" (String.trim td.name);
        List.iter (print_arg_typed_data_def ppf) td.args;
        fprintf ppf "@ : Set where@]";
        (* let bar = if List.length td.cases = 1 then "" else "| " in *) (* There is no "|" at the beginning of a line in Agda *) 
        List.iter
          (fun (s, args, ret) ->
            fprintf ppf "@ @[<2>%s :" s;
            (* let first_arrow = ref false in *)
            List.iter (print_arg_typed ppf) args;
            fprintf ppf "@ %s" (String.trim td.name);
            let fs = ref true in 
            List.iter (print_arg_untyped_data ppf fs) td.args;
            match ret with
            | None -> fprintf ppf "@]"
            | Some ret -> fprintf ppf "@ : %a@]" print_term ret)
          td.cases;
          fprintf ppf "@]")
        tds;
      newlines := 1


(*let print_newlines ppf () =
  for _ = 1 to !newlines do pp_print_newline ppf () done; newlines := 1*)

let print_newlines ppf () =
  for _ = 1 to !newlines do fprintf ppf "@,@," done; newlines := 1


let emit_gallina _modname ppf cmds =
  pp_print_list ~pp_sep:print_newlines emit_vernacular ppf cmds



