(*let ml_type_list = ["ml-int", 0; "ml-char", 0; "ml-list", 1; "ml-arrow", 2]*)


(** [rm_last s] returns the string [s] without its last character

    If [s = ""], returns [""]. *)
let rm_last s = 
	String.sub s 0 (max 0 (String.length s - 1))


(** [repro n s] returns a concatenation of [n] times the string [s]

    If [n = 0], returns the empty string *)
let rec repro n s = match n with
	| 0 -> ""
	| n -> s ^ (repro (n-1) s)


(** [uks n] returns the string ["u1 u2 ... uk"]

    If [n = 0], returns the empty string *)
let uks n = let rec aux n = 
	match n with
	| 0 -> ""
	| n -> aux (n-1) ^ "u" ^ (string_of_int n) ^ " " in rm_last (aux n)


(** [vks n] returns the string ["v1 v2 ... vk"]

    If [n = 0], returns the empty string *)
let vks n = let rec aux n = 
	match n with
	| 0 -> ""
	| n -> aux (n-1) ^ "v" ^ (string_of_int n) ^ " " in rm_last (aux n)


(** [uks_e_vks] n returns the string ["(u1 ≡ v1) (u2 ≡ v2) ... (uk ≡ vk)"]

    If [n = 0], returns the empty string *)
let uks_e_vks n = let rec aux n = 
	match n with
	| 0 -> ""
	| n -> aux (n-1) ^ "(u" ^ (string_of_int n) ^ 
			 " ≡ " ^ "v" ^ (string_of_int n) ^ ") " 
	in rm_last (aux n)


(** [eq_deccs n] returns the string ["(eq_decc u1 v1) (eq_decc u2 v2) ... (eq_decc uk vk)"]

    If [n = 0], returns the empty string *)
let eq_deccs n = let rec aux n = 
	match n with
	| 0 -> ""
	| n -> aux (n-1) ^ "(eq-decc u" ^ (string_of_int n) ^ 
			 " v" ^ (string_of_int n) ^ ") " 
	in rm_last (aux n)


(** [nz n s] returns the string [s] if [n <> 0] and the empty string otherwise *)
let nz n s = match n with
	| 0 -> ""
	| _ -> s


(*(** [p] is a shortcut for [print_endline] *)
let p s = print_endline s*)


(** [body_Fl f_line ctds] applies the function [f_line], generating one line of a function,
to the elements of [ctds], which is a [list] of couples [(name, arity)] *)
let rec body_FL f_line ctds = 
	match ctds with
		| [] -> ""
		| (name, arity) :: q -> let line = (f_line name arity) in 
											if line = "" 
											then ("" ^ (body_FL f_line q))
											else (line ^ "\n" ^ (body_FL f_line q))


(** [gen_data_rel_line n a] returns a [string] corresponding to the line of 
[data _~_ = Set where ...] for the ml-type of name [m] and arity [a] *)
let gen_data_rel_line name arity = match arity with
	| 0 -> "  ~" ^ name ^ " : " ^ name ^ " ~ " ^ name 
	| n -> "  ~" ^ name ^ " : (" ^ (uks n) ^ " " ^ (vks n) ^ " : ml-type) → " 
			 ^ name ^ " " ^ (uks n) ^ " ~ " ^ name ^ " " ^ (vks n)


(** [gen_data ctds] returns a [string] corresponding to the definition of [data _~_ = Set where ...]
for the types in [ctds], which is a [(string * int) list] of couples [(name, arity)] *)
let gen_data_rel ctds = 
	let sign = "data _~_ : (T1 T2 : ml-type) → Set where\n" in   
	let body = body_FL gen_data_rel_line ctds in
	sign ^ body 


(** [gen_view_line n a] returns a [string] corresponding to the line of 
[view] for the ml-type of name [m] and arity [a] *)
let gen_view_line name arity = match arity with
	| 0 -> "view " ^ name ^ " " ^ name ^ " = just ~" ^ name
	| n -> "view (" ^ name ^ " " ^ (uks n) ^ ") (" ^ name ^ " " ^ (vks n) ^
	       ") = just (~" ^ name ^ " " ^ (uks n) ^ " " ^ (vks n) ^ ")"


(** [gen_view ctds] returns a [string] corresponding to the definition of [view]
for the types in [ctds], which is a [(string * int) list] of couples [(name, arity)] *)
let gen_view ctds = 
	let sign = "view : (T1 T2 : ml-type) →  Maybe (T1 ~ T2)\n" in
	let body = body_FL gen_view_line ctds in
	let end_fun = "view _ _ = nothing\n" in
	sign ^ body ^ end_fun


(** [gen_view_diag_line n a] returns a [string] corresponding to the line of 
[view_diag_line] for the ml-type of name [m] and arity [a] *)
let gen_view_diag_line name arity = match arity with
	| 0 -> "view-diag " ^ name ^ "()"
	| n -> "view-diag (" ^ name ^ (repro n " _") ^ ") ()"


(** [gen_view_diag ctds] returns a [string] corresponding to the definition of [view_diag]
for the types in [ctds], which is a [(string * int) list] of couples [(name, arity)] *)
let gen_view_diag ctds =
	let sign = "view-diag : (T : ml-type) → ¬ (view T T ≡ nothing)\n" in
	let body = body_FL gen_view_diag_line ctds in
	sign ^ body 


(** [arity_type n] returns the name of the type of [n]-uples*)
let arity_type n = match n with
	| 0 | 1 -> ""
	| 2 -> "_×_ "
	| n -> "up" ^ (string_of_int n) ^ " "


(** [arity_cons n] returns the contructor of [n]-uples*)
let arity_cons n = if n < 2 then "" else repro (n-1) ","


(** [gen_inj_one n a] returns the proof of injectivity for the constructor of the ml-type [m] *)
let gen_inj_one name arity = 
	if arity = 0 
	then "" 
	else (
	let sign = name ^ "-inj : " ^ name ^ " " ^ 
				  (uks arity) ^ " ≡ " ^ name ^ " " ^ (vks arity) ^
				  " → " ^ (arity_type arity) ^ (uks_e_vks arity) ^ "\n"
	in let body = name ^ "-inj refl = refl" ^ 
					  repro (arity-1) ((" " ^ arity_cons arity) ^ " refl") ^ "\n" in
	sign ^ body
	)


(** [gen_inj ctds] returns the proof of injectivity for all the ml-types in [ctds], 
which is a [(string * int) list] of couples [(name, arity)] *)
let gen_inj ctds = rm_last (body_FL gen_inj_one ctds)


(** [gen_cong_one n a] returns the proof of congruence for the constructor of the ml-type [m] *)
let gen_cong_one name arity = 
	if arity = 0 
	then "" 
	else (
	let sign = name ^ "-cong : " ^ (arity_type arity) ^ (uks_e_vks arity) ^ 
				  " → " ^ name ^ " " ^ (uks arity) ^ " ≡ " ^ 
				  name ^ " " ^ (vks arity) ^ "\n"
	in let body = name ^ "-cong (refl" ^ 
					  repro (arity-1) (" " ^ (arity_cons arity) ^ " refl") 
					  ^ ")" ^ " = refl" ^ "\n" in
	sign ^ body
	)


(** [gen_cong ctds] returns the proof of congruence for all the ml-types in [ctds], 
which is a [(string * int) list] of couples [(name, arity)] *)
let gen_cong ctds = rm_last (body_FL gen_cong_one ctds)


(** [decideur a] returns the name of the term proving the decidabilityof [a]-uples *)
let decideur arity = match arity with
	| 0 | 1 -> ""
	| 2 -> "_×-dec_ "
	| n -> (rm_last (arity_type n)) ^ "-dec "


(** [gen_eq_decc_line n a] returns a [string] corresponding to the line of 
[eq_decc] for the ml-type of name [m] and arity [a] *)
let gen_eq_decc_line name arity = 
	let beninging = "eq-decc _ _ | just " ^ (nz arity "(") 
						 ^ "~" ^ name ^ (nz arity " ") ^ 
						 (uks arity) ^ (nz arity " ") ^ 
	                (vks arity) ^ (nz arity ")") ^ " | _ = " in
	let r_handside = match arity with
		| 0 -> "yes refl"
		| n -> "map′ " ^ name ^ "-cong " ^ name ^ "-inj (" ^ 
		       (decideur n) ^ (eq_deccs n) ^ ")" in
	beninging ^ r_handside


(** [gen_eq_decc ctds] returns a [string] corresponding to the definition of [eq_decc]
for the types in [ctds], which is a [(string * int) list] of couples [(name, arity)] *)
let gen_eq_decc ctds = 
	let sign = "eq-decc : (T1 T2 : ml-type) → Dec (T1 ≡ T2)\
\neq-decc T1 T2 with view T1 T2 | inspect (view T1) T2\n" in 
	let end_fun = "eq-decc m n | nothing | [ eq ] = no λ where refl → view-diag _ eq\n" in
	let body = body_FL gen_eq_decc_line ctds in
	sign ^ body ^ end_fun


(** [gen_proof ctds] returns the whole proof for the types in [ctds], 
which is a [(string * int) list] of couples [(name, arity)] *)
let gen_proof ctdN_ctdA_list = 
	"-- Proof of DecidableEquality on ml-type\n\n" ^
	(gen_data_rel ctdN_ctdA_list) ^ "\n" ^
	(gen_view ctdN_ctdA_list) ^ "\n" ^
	(gen_view_diag ctdN_ctdA_list) ^ "\n" ^
	(gen_inj ctdN_ctdA_list) ^ "\n" ^
	(gen_cong ctdN_ctdA_list) ^ "\n" ^
	(gen_eq_decc ctdN_ctdA_list) ^ "\n" ^
	"-- End of the proof of DecidableEquality on ml-type"
	
(*let () = p (gen_proof ml_type_list)*);;


















