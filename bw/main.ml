open Debug
open Core
open Util
open Common
open Range

module G : Globals.T = struct
  type tm_t = Globals.HTm.t
  let tm_table = Globals.HTm.create 251    (* or, load from a file based on flags *)

  type ppat_t = Globals.PPat.t
  let ppat_table = Globals.PPat.create 251

  type npat_t = Globals.NPat.t
  let npat_table = Globals.NPat.create 251

  type pprop_t = Globals.PProp.t
  let pprop_table = Globals.PProp.create 251

  type nprop_t = Globals.NProp.t
  let nprop_table = Globals.NProp.create 251

  type proof_t = Globals.HProof.t
  let proof_table = Globals.HProof.create 251

  type value_t = Globals.PValue.t
  let value_table = Globals.PValue.create 251

  type stack_t = Globals.NStack.t
  let stack_table = Globals.NStack.create 251

  type sym_t = (int,string * int) Hashtbl.t
  let sym_table = (Hashtbl.create ~size:251 (module Int) : sym_t)

  let rev_table : (int, string) Hashtbl.t = Hashtbl.create ~size:251 (module Int)

  let gen_sym s =
    let h = Hashtbl.hash s in
    begin match Hashtbl.find sym_table h with
    | Some (_, t) -> t
    | None -> let t = Hashcons.gentag () in
      ignore (Hashtbl.add sym_table ~key:h ~data:(s, t));
      ignore (Hashtbl.add rev_table ~key:t ~data:s);
      t
    end

  let lookup_sym t =
    match Hashtbl.find rev_table t with
    | Some x -> x
    | None -> "S" ^ string_of_int t

  let gen_tag = Hashcons.gentag   (* ensures that proposition symbols and term Top.tags can be used together in unification *)
end

module TMS = Tm.Make(G);;
module PROPS = Prop.Make(G)(TMS);;
module PROOFS = Proof.Make(G)(TMS)(PROPS);;
module TRANS = Translate.Make(G)(TMS)(PROPS);;
module RULES = Rule.Make(G)(TMS);;
module SYNTH = Synthetics.Make(G)(TMS)(PROPS)(RULES)(PROOFS);;
module SEARCH = Search.Make(RULES)
module PROVER = Prover.Make(G)(TMS)(PROPS)(RULES)(SYNTH)(SEARCH);;
module STRATEGY = Mcts.RuleStrategy(RULES)(SYNTH)(PROVER);;
module MCTS = Mcts.Make(STRATEGY);;

let ast_from_lexbuf filename buf =
  try
    Lexer.reset_lexbuf filename buf;
    Parser.file Lexer.token buf
  with Parsing.Parse_error ->
    failwith (Printf.sprintf "Parse error at %s."
                (string_of_range (Lexer.lex_range buf)))

let ctxt = ref []

let process_input i =
  let _ = Format.print_flush () in
  match i with
  | Ast.Include _ -> Pp.pp_input i
  | Ast.Fof(s, r, p) -> begin
      match r with
      | Ast.Conjecture -> (
	        let q = TRANS.prop_to_nprop [] p in
	        let _ = Printf.printf " Proving %s" s in
	        let _ = if !Pp.verbose then Printf.printf ": %s\n" (Pp.string_of_nprop G.lookup_sym q) else
	            Printf.printf "\n" in

	        let _ = Printf.printf "Symbols:\n" in
	        let _ = Hashtbl.iteri ~f:(fun ~key -> fun ~data:(s,t) -> Printf.printf " S:%d = %s[%d]\n" key s t) G.sym_table in
	        let _ = Printf.printf"NProp Table:\n" in
	        let _ = Globals.NProp.iter (fun x -> Printf.printf " S:%d = %s\n" x.Hashcons.tag (Pp.string_of_nprop G.lookup_sym x)) G.nprop_table in
	        let _ = Printf.printf"PProp Table:\n" in
	        Globals.PProp.iter (fun x -> Printf.printf " S:%d = %s\n" x.Hashcons.tag (Pp.string_of_pprop G.lookup_sym x)) G.pprop_table;

	        let (params, goals) = SYNTH.make_synthetics (!ctxt) q in
	        Int.Table.iteri ~f:(fun ~key:i ~data:rules ->
            List.iter ~f:(fun r ->
              Printf.printf "LEFT RULE(S:%d)\n%s\n" i (Pp.string_of_x (RULES.pp_rule G.lookup_sym) r))
            rules) SYNTH.lfoc_rules;
	        Int.Table.iteri ~f:(fun ~key:i ~data:rules ->
            List.iter ~f:(fun r ->
              Printf.printf "RIGHT RULE(S:%d)\n%s\n" i (Pp.string_of_x (RULES.pp_rule G.lookup_sym) r))
            rules) SYNTH.rfoc_rules;
	        Printf.printf "Goals:\n";
	        Printf.printf "%s\n" (Pp.string_of_x (fun fmt -> Pp.pp_list_aux fmt "\n" (RULES.pp_sequent G.lookup_sym fmt)) goals);
          let heuristic state =
            debug "heuristic called";
            let result = (MCTS.search_rounds 1 state) in
            -result.wins
          in
          let success = PROVER.search_goals heuristic params goals in
          if success then
            debug "PROOF SEARCH SUCCEEDED\n"
          else
            debug "PROOF SEARCH FAILED\n")
      | Ast.Axiom -> (
         let _ = if !Pp.verbose then Printf.printf "adding axiom: " in
	       let q = TRANS.prop_to_pprop [] p in  (* positive proposition *)
	       let _ = if !Pp.verbose then Printf.printf "%s\n" (Pp.string_of_pprop G.lookup_sym q) else () in
         (*	  let l = G.gen_tag () in *)
	       let g = !ctxt in
	       ctxt := q::g
	     )
      | _ ->  Printf.printf "Role not supported\n";
        Printf.printf "Proposition %s : %s\n" s (Pp.string_of_nprop G.lookup_sym (TRANS.prop_to_nprop [] p))
    end

let process_file =
  ctxt := [];
  List.iter ~f:process_input


let do_file fn =
  let _ = Printf.printf "Processing: %s\n" fn in
  let buffer = In_channel.create fn in
  let ast = ast_from_lexbuf fn (Lexing.from_channel buffer) in
  process_file ast;
  In_channel.close buffer

let argspec = [
  ("-debug", Arg.Set (enabled), "turn on debugging");
  (* 	("-backtrack", Arg.Set (Prover.backtrack_flag), "show backtracking"); *)
  ("-print_depth", Arg.Int Format.set_max_boxes, "set print depth, default 10");
  ("-verbose", Arg.Set Pp.verbose, "turn on more output");
  ("-showhash", Arg.Set Pp.showhash, "display hash cons tags")
]

let _ =
  Format.set_max_boxes 10;
  Printf.printf("Running TP\n");
  try
    Arg.parse argspec do_file "Default command-line parser"
  with
  | Failure s -> print_string s
