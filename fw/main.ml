(* open Arg *)
open List
open Range


module G : Fglobals.T = struct
  type tm_t = Fglobals.HTm.t
  let tm_table = Fglobals.HTm.create 251    (* or, load from a file based on flags *)

  type fprop_t = Fglobals.FProp.t
  let fprop_table = Fglobals.FProp.create 251
	
  type sym_t = (int,string * int) Hashtbl.t
  let sym_table = (Hashtbl.create 251 : sym_t)
	
  let rev_table : (int, string) Hashtbl.t = Hashtbl.create 251
			
  let gen_sym s = 
		let h = Hashtbl.hash s in
		try let _,t = Hashtbl.find sym_table h in t 
		with Not_found -> let t = Hashcons.gentag () in Hashtbl.add sym_table h (s, t); Hashtbl.add rev_table t s; t

  let lookup_sym t =
		try Hashtbl.find rev_table t with Not_found -> ("S" ^ string_of_int t) 
		
  let gen_tag = Hashcons.gentag   (* ensures that proposition symbols and term Top.tags can be used together in unification *)
end 
 
module TMS = Ftm.Make(G);;
module PROPS = Fprop.Make(G)(TMS);;
module TRANS = Ftranslate.Make(G)(TMS)(PROPS);;
module RULES = Frule.Make(G)(TMS);;
(* module RULE_SET = Frule_set.Make (RULES);;
module PROVER = Fprover.Make(G)(TMS)(PROPS)(RULES)(RULE_SET);; *)
module PROVER = Fprover.Make (G)(TMS)(PROPS)(RULES);;


let ast_from_lexbuf filename buf =
  try
    Lexer.reset_lexbuf filename buf;
    Parser.file Lexer.token buf
  with Parsing.Parse_error ->
    failwith (Printf.sprintf "Parse error at %s." 
        (string_of_range (Lexer.lex_range buf)))

let ctxt = ref (Frule.AssumpSet.empty)

let process_input i =
  let _ = Format.print_flush () in
  match i with 
  | Ast.Include _ -> Fpp.pp_input i
  | Ast.Fof(s, r, p) -> begin
      match r with 
      | Ast.Conjecture -> (
	  let q = TRANS.prop_to_prop [] p (Fprop_rep.Pos)in 
	  let _ = Printf.printf " Proving %s" s in
	  let _ = if !Fpp.verbose then Printf.printf ": %s\n" (Fpp.string_of_sprop G.lookup_sym q) else 
	      Printf.printf "\n" in

	  let _ = Printf.printf "Symbols:\n" in
	  let _ = Hashtbl.iter (fun h -> fun (s,t) -> Printf.printf " S:%d = %s[%d]\n" h s t) G.sym_table in										
	  let _ = Printf.printf"FProp Table:\n" in
	  let _ = Fglobals.FProp.iter (fun x -> Printf.printf " S:%d = %s\n" x.Hashcons.tag (Fpp.string_of_sprop G.lookup_sym x)) G.fprop_table in				                                
	  let _ = PROVER.fw_search (!ctxt) q in
	  (*let (params, goals) = PROVER.make_synthetics (!ctxt) q in*)		

	  (* let _ = RULE_SET.iter (fun (i, r) -> Printf.printf "RULE(S:%d)\n%s\n" i (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r)) rule_val in*)
	  (*let _ = Hashtbl.iter (fun i r -> Printf.printf "RULE(S:%d)\n%s\n" i (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r)) PROVER.rules in*)
	  (*let _ = Printf.printf "Goals:\n" in
	    let _ = Printf.printf "%s\n" (Fpp.string_of_x (fun fmt -> Fpp.pp_list_aux fmt "\n" (RULES.pp_sequent G.lookup_sym fmt)) goals) in *)							
	  ()

	)
      | Ast.Axiom -> (
	  let _ = if !Fpp.verbose then Printf.printf "adding axiom: " in
	  let q = TRANS.prop_to_prop [] p (Fprop_rep.Neg) in  (* negative proposition *)
	  let _ = if !Fpp.verbose then Printf.printf "%s\n" (Fpp.string_of_sprop G.lookup_sym q) else () in 
	  let _ = G.gen_tag () in
	  let g = !ctxt in
	  ctxt := Frule.AssumpSet.add q g

	)
      | _ ->  Printf.printf "Role not supported\n";
	Printf.printf "Proposition %s : %s\n" s (Fpp.string_of_sprop G.lookup_sym (TRANS.prop_to_prop [] p (Fprop_rep.Pos)))
    end

let process_file = 
	(* let _ = ctxt := [] in *)
	List.iter process_input


let do_file fn =
	let _ = Printf.printf "Processing: %s\n" fn in
  let buffer = open_in fn in
  let ast = ast_from_lexbuf fn (Lexing.from_channel buffer) in
	process_file ast;
  close_in buffer
  
(*
let ast_from_string str = ast_from_lexbuf "string" (Lexing.from_string str)
*)

let argspec = [
  ("-debug", Arg.Set (PROVER.debug_flag), "turn on debugging"); 
(* 	("-backtrack", Arg.Set (Prover.backtrack_flag), "show backtracking"); *)
	("-print_depth", Arg.Int Format.set_max_boxes, "set print depth, default 10");
	("-verbose", Arg.Set Fpp.verbose, "turn on more output");
	("-showhash", Arg.Set Fpp.showhash, "display hash cons tags")
]

let _ =
	let _ = Format.set_max_boxes 10 in
  Printf.printf("Running TP\n");
	try 
    Arg.parse argspec do_file "Default command-line parser"
	with
		| Failure s -> print_string s
