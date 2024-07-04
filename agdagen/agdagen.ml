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
  CTfixpoint ("coq-type",
              CTabs ("T", Some ml_tid,
                     CTann (CTmatch (CTid "T", None, cases), CTsort Type)))


(* ++++++++++++++++++++++++++++++++++++ *)
(* Functions for generating compare-rec *)
(* ++++++++++++++++++++++++++++++++++++ *)

let cis c i = if i <= 0 then "" else " " ^ String.concat " " (iota_names 1 i c)

let rec repro n s = match n with
	| 0 -> ""
	| n -> s ^ repro (n-1) s

let xyi i = let i_str = string_of_int i in Format.sprintf "x%s y%s" i_str i_str

let xis = cis "x"
let yis = cis "y"
let ais = cis "a"

let cons_eq ppf arity = 
	let rec cons_eq_aux arity ppf i = match arity with
		| 0 -> Format.fprintf ppf "Ret Eq"
		| 1 -> Format.fprintf ppf "@[compare-rec h %s@]" (xyi i)
		| n -> Format.fprintf ppf "@,@[<v1>lexi-compare (compare-rec h %s)@,@[<v2>(Delay (%a))@]@]" 
				 (xyi i) (cons_eq_aux (n-1)) (i+1) in
	Format.fprintf ppf "%a" (cons_eq_aux arity) 1

let make_one_line arity ppf name = 
	let xs = xis arity in
	let ys = yis arity in
	Format.fprintf ppf "@[<v2>(%s%s , %s%s) → %a@]" name xs name ys cons_eq arity

let cons_not_eq arity ppf name = 
	Format.fprintf ppf "@[<v>; (%s%s , _) → Ret Lt@,; (_ , %s%s) → Ret Gt@]" name (repro arity " _") name (repro arity " _")

let cr_left typ_arity ppf typ_name =
	Format.fprintf ppf "compare-rec (suc h) {%s%s} =@,@[<v2>λ x y → case x , y of λ {@," typ_name (ais typ_arity)

let cr_one_type typ_name typ_arity ppf cases = 
	Format.fprintf ppf "@[<v2>%a@[<v>" (cr_left typ_arity) typ_name;
	let sep = ref "" in
	let size = List.length cases in
	let _ = List.mapi
	(fun i (name, args) ->
		let arity = List.length args in
			Format.fprintf ppf "%s%a@," !sep (make_one_line arity) name;
			if i <> (size - 1) then (* for the last constructor these lines would result in unreachable clauses *)
				(sep := "; ";
				Format.fprintf ppf "%a@," (cons_not_eq arity) name))
	cases in
	Format.fprintf ppf "}@]@]@]"

let make_case_ag z = 
	let (_, ctd) = z in
	match ctd, ctd.ct_def with
		| _, None -> ""
		| _, Some(_, []) -> ""
		| ctd, Some (_, cases) ->
			match ctd.ct_name with
				| "ml-int" | "ml-char" | "ml-float" |
"ml-bool" | "ml-unit" | "ml-array" |
"ml-list" | "ml-lazy" | "ml-string" | "ml-array-t" | 
"ml-lazy-val" | "ml-ref" | "ml-arrow" -> ""
				| _ -> Format.asprintf "%a@," (cr_one_type ctd.ct_name ctd.ct_arity) cases

let make_compare_rec_ag vars = 
	String.concat "" (List.map make_case_ag (Path.Map.bindings vars.type_map))

let comprec_const =  
	CTverbatim ("compare-rec : (h : ℕ) {T : ml-type}\
@,  → coq-type T -> coq-type T -> M comparator\
@,compare-rec ℕ.zero {T} x y = FailGas\
@,compare-rec (suc h) {ml-int} = λ x y →  Ret (compare-integer x y)\
@,compare-rec (suc h) {ml-char} = λ x y → Ret (compare-ascii x y)\
@,compare-rec (suc h) {ml-float} = λ x y → Ret (compare-float x y)\
@,compare-rec (suc h) {ml-bool} = λ x y → Ret (compare-bool x y)\
@,compare-rec (suc h) {ml-unit} = λ x y → Ret Eq" ^ 
(*@,compare-rec (suc h) {ml-array T} =\
@,  λ x y → compare-ref {ml-array-t T} {compare-rec h} x y\*)
"@,compare-rec (suc h) {ml-list T} =\
@,  λ x y → compare-list {T} {compare-rec h} x y\
@,compare-rec (suc h) {ml-lazy T} =\
@,  λ x y → Raise (Catchable (Invalid-argument \"compare\"))\
@,compare-rec (suc h) {ml-string} = λ x y → Ret (compare-string x y)\
@,compare-rec (suc h) {ml-array-t T} (ArrayVal x) (ArrayVal y) =\
@,  compare-rec h x y\
@,compare-rec (suc h) {ml-lazy-val T} =\
@,  λ x y → Raise (Catchable (Invalid-argument \"compare\"))\
@,compare-rec (suc h) {ml-ref T} =\
@,  λ x y → compare-ref {T} {compare-rec h} x y\
@,compare-rec (suc h) {ml-arrow T T1} =\
@,  λ x y → Raise (Catchable (Invalid-argument \"compare\"))")


(* ++++++++++++++++++++++++++ *)
(* End of compare-rec section *)
(* ++++++++++++++++++++++++++ *)


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
  List.rev_map (List.map (fun id -> List.assoc id id_defs)) groups

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

let make_proof vars = 
	let rec get_names_and_arities ctds = match ctds with
		| [] -> []
		| ( _, x ) :: q -> (x.ct_name, x.ct_arity) :: (get_names_and_arities q) in
	let ctds = Path.Map.bindings vars.type_map in
	let ctdN_ctdA_list = get_names_and_arities ctds in
	gen_proof ctdN_ctdA_list

(*let indent_induct n induct = let space = repro n " " in 
	{name = space ^ (induct.name); args = induct.args; kind = induct.kind;
      cases = List.map (fun (s, l1, cto) -> (space ^ s), l1, cto) (induct.cases)}

let indent_ctind n vernac = match vernac with
	| CTinductive ind_list -> CTinductive(List.map (indent_induct n) ind_list)
	| x -> x*)

let remove_type path vars =
  { vars with
    type_map = Path.Map.remove path vars.type_map}

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
  let typedefs = List.map (fun gr -> (*indent_ctind 2*) (CTinductive gr)) inductives in
  let vars_no_mlarray = remove_type Predef.path_array vars in



  CTverbatim "@[<v>open import agdagen_defs\
@,open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)\
@,open import Data.Sum using (_⊎_; inj₁; inj₂)\
@,open import Relation.Binary.Definitions using (DecidableEquality)\
@,open import Data.Bool using (true; false; Bool; if_then_else_)\
@,open import Relation.Nullary.Decidable.Core using (_because_; isYes; Dec; yes)\
@,open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)\
@,open import Data.String using (String)\
@,@[<v2>open import Data.Float using (Float)\
@,renaming (_+_ to _ℝ+_; _*_ to _ℝ*_; _-_ to _ℝ-_; _÷_ to _ℝ÷_; -_ to ℝ-_)@]\
@,open import Data.Char using (Char)\
@,open import Data.Nat using (ℕ; suc) renaming (_<?_ to _ℕ<?_)\
@,open import Data.Unit using (⊤; tt)\
@,open import Data.List using (List; []; length; _∷_)\
@,open import Data.Product using (_×_ ; _,_; proj₁ ; proj₂; _,′_)\
@,open import Data.Empty using (⊥)\
@,open import Data.Maybe using (Maybe; just; nothing)\
@,open import Relation.Nullary using (¬_)\
@,open import Relation.Nullary.Decidable using (map′; _×-dec_; no)\
@,open import Relation.Binary.PropositionalEquality using (inspect; [_])\
@,open import Data.Integer using (ℤ; _+_; _-_; _*_; +_; -_)\
@,open import Data.Integer.DivMod using (_/_)\
@,open import Function.Base using (case_of_)\
@,@,-- Generated representation of all ML types" :: 
  make_ml_type vars_no_mlarray ::
  CTverbatim "\
@[<v2>variable\
@,u1 u2 u3 u4 u5 u6 v1 v2 v3 v4 v5 v6 : ml-type@]@]@." :: (* no more boxes open so far *)
  CTverbatim (make_proof vars_no_mlarray) ::
  CTverbatim "\
@[<v>ml-type-eq-dec : DecidableEquality ml-type\
@,ml-type-eq-dec = eq-decc\
@,@,\
@[<v2>instance\
@,ml-type-is-eq-dec : eqType ml-type\
@,ml-type-is-eq-dec = record {eq-dec = ml-type-eq-dec}@]\
@,@,\
@[<v2>data array-t (T : Set) : Set where\
@,ArrayVal : List T → array-t T@]\
@,\
@,ml-array : ml-type → ml-type\
@,ml-array T = ml-ref (ml-array-t T)\
@,@[<v2>module MLtypes-aux (M : Set → Set) where\
@,-- Generated type definitions\
@,\
loc = loc-b ml-type" :: 
  typedefs @ (* Indentation to handle *)
  CTverbatim "\
@[<v 2>data lazy-val (a : Set) : Set where\
@,LzVal : a → lazy-val a\
@,LzThunk : (M a) → lazy-val a\
@,LzExn : ml-exns → lazy-val a@]\
@,@,\
@[<v 2>data lazy-t (a : Set) (a1 : ml-type) : Set where\
@,Lval : a → lazy-t a a1\
@,Lref : (loc (ml-lazy-val a1)) → lazy-t a a1@]\
@,\
-- Generated type translation function" ::
  make_coq_type vars_no_mlarray :: (* box [<v2>modules MLtypes-aux (...) closed *)
CTverbatim "@]\
@,open MLtypes-aux hiding (loc; coq-type)\
@,@,\
MLtypes : MLTY\
@,@[<v2>MLtypes = record {\
@,ml-type = ml-type ;\
@,coq-type-b = MLtypes-aux.coq-type ;\
@,ml-exn = ml-exn ;\
@,ml-type-is-eq-dec = ml-type-is-eq-dec\
@,}@]\
@,\
@,open MLTY MLtypes hiding (ml-type; ml-exn)\
@,\
@,REFmonadML : REFmonad MLtypes\
@,REFmonadML = record {}\
@,\
@,open REFmonad REFmonadML\
@,\
@,empty-env : Env2\
@,empty-env = mkEnv []\
@,\
@,it : W ⊤\
@,it = inj₂ (inj₂ tt , empty-env)\
@,@,\
-- Generated comparison function\
@,@[<v>"
  (*@,postulate compare-rec : (h : ℕ) (T : ml-type)\
  → coq-type T -> coq-type T -> M comparator*) ::
  comprec_const :: 
  CTverbatim (make_compare_rec_ag vars_no_mlarray) ::
  CTverbatim "@]\
ml-compare = compare-rec\
@,\
@,wrap-compare : (comparator → Bool) → (h : ℕ) → (T : ml-type) → coq-type T → coq-type T → M Bool\
@,wrap-compare wrap h T x y = Do c ← compare-rec h {T} x y // Ret (wrap c)\
@,\
@,ml-eq = wrap-compare (λ {Eq → true ; _ → false })\
@,ml-lt = wrap-compare (λ {Lt → true ; _ → false })\
@,ml-gt = wrap-compare (λ {Gt → true ; _ → false })\
@,ml-ne = wrap-compare (λ {Eq → false ; _ → true })\
@,ml-ge = wrap-compare (λ {Lt → false ; _ → true })\
@,ml-le = wrap-compare (λ {Gt → false ; _ → true })" ::
  CTverbatim "-- Array operations\
@,nat-of-int : ℤ → M ℕ\
@,nat-of-int (+_ n) = Ret n\
@,nat-of-int (ℤ.negsuc n) = Raise BoundedNat\
@,\
@,newarray : (T : ml-type) → ℤ → (x : coq-type T) → M (loc (ml-array-t T))\
@,newarray T len x = Do len ← nat-of-int len // cnew (ml-array-t T) (ArrayVal (ncons len x))\
@,\
@,bounded-nat-of-int : ℕ → ℤ → M ℕ\
@,bounded-nat-of-int m n = Do n ← nat-of-int n // case (n ℕ<? m) of λ {\
@,                (yes _) → Ret n ;\
@,                _ → Raise BoundedNat }\
@,\
@,getarray : (T : ml-type) → (a : coq-type (ml-array T)) → (n : ℤ) → M (coq-type T)\
@,getarray T a n = Do s ← cget (ml-array-t T) a // case s of λ {\
@,                      (ArrayVal u) → Do n ← bounded-nat-of-int (length u) n //\
@,                        case u of λ {\
@,                          [] → raise T (Invalid-argument \"getarray\") ;\
@,                          (x ∷ q) → Ret (nth x u n) } }\
@,\
@,setarray : (T : ml-type) → (a : coq-type (ml-array T)) → (n : ℤ) → (coq-type T) → M ⊤\
@,setarray T a n x = Do s ← cget (ml-array-t T) a //\
@,                      case s of λ {\
@,                        (ArrayVal u) → Do n ← bounded-nat-of-int (length u) n //\
@,                          cput (ml-array-t T) a (ArrayVal (set-nth x u n x)) }\
@,\
@,-- Lazy values\
@,force : (a : ml-type) → (lz : coq-type (ml-lazy a)) → M (coq-type a)\
@,force a (Lval x) = Ret x\
@,force a (Lref r) = Do r' ← cget (ml-lazy-val a) r //\
@,                           (case r' of λ {\
@,                               (LzVal x) → Ret x ;\
@,                               (LzExn e) → raise _ e ;\
@,                               (LzThunk f) → let ff : M (coq-type a)\
@,                                                 ff = f in\
@,                                                    handle _ (Do x ← ff //\
@,                                                       Do _ ← cput (ml-lazy-val a) r (LzVal x) //\
@,                                                       Ret x)\
@,                                                       (λ e → Do _ ← cput _ r (LzExn e) //\
@,                                                              raise _ e) })\
@,\
@,make-lazy : (a : ml-type) (b : M (coq-type a)) → M (coq-type (ml-lazy a))\
@,make-lazy a b = Do x ← cnew (ml-lazy-val a) (LzThunk b) // Ret (Lref x)\
@,\
@,make-lazy-val : (a : ml-type) (b : coq-type a) → coq-type (ml-lazy a)\
@,make-lazy-val a b = Lval b\
@,\
@,-- Default amount of gas@,\
@,h = 100000\
@,\
@,-- Translated code" :: cmds @ [CTverbatim "@]"];;

(* @,data ml-exns : Set where\
@,  Invalid-argument : String → ml-exns\
@,  Failure : String → ml-exns\
@,@,  Not-found : ml-exns\
*)



