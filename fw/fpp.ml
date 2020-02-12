(** Pretty printing for terms and formulas*)
open Ftm_rep
open Fprop_rep
open Format

let verbose  = ref false
let showhash = ref false

(* Auxilliary printing functions*)

let rec pp_list_aux fmt sep fn = function
  | [] -> ()
  | [x] -> fn x
  | x :: tl -> (
    pp_open_hovbox fmt 0;
    fn x;
    pp_print_string fmt sep;
    pp_close_box fmt ();
    pp_print_space fmt ();
    pp_list_aux fmt sep fn tl
  ) 


let rec pp_hash_consed_aux fmt lvl fn h =
	let pps = pp_print_string fmt in
	if !showhash then
		(pp_open_hovbox fmt 0;
		pps "{hkey = "; pps (string_of_int h.Hashcons.hkey); pps ";"; pp_print_break fmt 1 1;
		pps "Ftop.tag = "; pps (string_of_int h.Hashcons.tag); pps ";"; pp_print_break fmt 1 1;
		pps "node = "; fn fmt lvl (h.Hashcons.node); pps "}";
		pp_close_box fmt ())
	else fn fmt lvl (h.Hashcons.node)

let rec pp_tm_aux st fmt lvl =
	pp_hash_consed_aux fmt lvl (pp_tm_t_aux st) 
and pp_tm_t_aux (st : int -> string) fmt lvl t =
	let pps = pp_print_string fmt in 
	match t with
		| Tm_uvar i ->  pps ("u_" ^ (string_of_int i))
		| Tm_param x -> pps ("x_" ^ (string_of_int x))
		| Tm_fun (f, l) -> 
				pps (st f);
				if l = [] then () else begin
					pps "(";
					(pp_list_aux fmt "," (pp_tm_aux st fmt 0) l);
					pps ")"
				end

let prec_of_sprop sp = 
	match sp with
	| SProp_pred _ -> 1000
	| SProp_and _ -> 30
	| SProp_imp _ -> 10 
	| SProp_or  _ -> 30
	| SProp_not _ -> 30
	| SProp_top _ -> 1000
	| SProp_bot _ -> 1000
	| SProp_Emp _ -> 1000

let rec pp_sprop_aux st fmt lvl p =
	let this_level = prec_of_sprop p in
	let pps = pp_print_string fmt in
	let pph lvl = pp_hash_consed_aux fmt lvl (pp_sprop_aux st) in
	let pp_bin_sprop p1 p2 s l1 l2 = 
		pp_open_box fmt 0;
		pph l1 p1;
		pps s;
		pph l2 p2;
	  pp_close_box fmt ()
	in
	let pp_imp p1 n2 l1 l2 = 
		pp_open_box fmt 0;
		pp_hash_consed_aux fmt l1 (pp_sprop_aux st) p1;
		pps " -> ";
		pph l2 n2;
	  pp_close_box fmt ()
	in

  (if this_level < lvl then fprintf fmt "(" else ());	
 	begin
	match p with
	| SProp_pred ((f, ts), sn) -> begin
	                  pps "(";
			  pps (st f);
				if List.length ts = 0 then () else (
					pps "(";
					(pp_list_aux fmt "," (pp_tm_aux st fmt 0) ts);
					pps ")");
			   pps ")" ; (match sn with |Pos -> pps "+" |Neg -> pps "-") 
			  end
	| SProp_and ((sp1,sp2),sn) -> pps "(" ;pp_bin_sprop sp1 sp2 " & " this_level this_level; pps ")"; (match sn with |Pos -> pps "+" |Neg -> pps "-")  
	| SProp_imp ((sp1,sp2),sn) -> pps "("; pp_imp sp1 sp2 1000 this_level; pps ")"; (match sn with |Pos -> pps "+" |Neg -> pps "-") 
	| SProp_or  ((sp1,sp2),sn) -> pps "("; pp_bin_sprop sp1 sp2 " * " this_level this_level; pps ")"; (match sn with |Pos -> pps "+" |Neg -> pps "-") 
	| SProp_not (sp,sn) -> pps "(" ; pps "$"; pp_hash_consed_aux fmt lvl (pp_sprop_aux st) sp; pps ")"; (match sn with |Pos -> pps "+" |Neg -> pps "-") 
	| SProp_top sn -> pps "(TOP)"; (match sn with |Pos -> pps "+" |Neg -> pps "-") 
	| SProp_bot sn -> pps "(BOT)"; (match sn with |Pos -> pps "+" |Neg -> pps "-") 
	| SProp_Emp sn -> pps "."; (match sn with |Pos -> pps "+" |Neg -> pps "-") 
  end;
	(if (this_level < lvl) then fprintf fmt ")" else ())									

let string_of_x f x =
	pp_open_hvbox str_formatter 0;
	f str_formatter x;
	pp_close_box str_formatter ();
	flush_str_formatter ()																																			
let string_of_tm st = string_of_x (fun fmt -> pp_tm_aux st fmt 0)																									
let string_of_sprop st sp = if !verbose then string_of_x (fun fmt -> pp_hash_consed_aux fmt 0 (pp_sprop_aux st)) sp else "[SPROP]"

let pp_input i =
	match i with
		| Ast.Include (s, _) -> (
			  print_string "input: ";
				print_string s;
				print_newline ()
			)
		| Ast.Fof (s, _, _) -> (
			  print_string "fof: ";
				print_string s;
				print_newline ()
			)

let pp_file = List.iter pp_input

