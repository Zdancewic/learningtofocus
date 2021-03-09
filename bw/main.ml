open Debug
open Core
open Util
open Common
open Range
open Globals
module G = Globals.G

let ctxt = ref []

let process_input i =
  Format.print_flush ();
  match i with
  | Ast.Include _ -> Pp.pp_input i
  | Ast.Fof(s, r, p) -> begin
      match r with
      | Ast.Conjecture -> (
	        let q = Translate.prop_to_nprop [] p in
	        Printf.printf " Proving %s" s;
	        if !Pp.verbose then Printf.printf ": %s\n" (Pp.string_of_nprop G.lookup_sym q) else
	            Printf.printf "\n";
	        Printf.printf "Symbols:\n";
	        Hashtbl.iteri ~f:(fun ~key -> fun ~data:(s,t) -> Printf.printf " S:%d = %s[%d]\n" key s t) G.sym_table;
	        Printf.printf"NProp Table:\n";
	        Globals.NProp.iter (fun x -> Printf.printf " S:%d = %s\n" x.Hashcons.tag (Pp.string_of_nprop G.lookup_sym x)) G.nprop_table;
	        Printf.printf"PProp Table:\n";
	        Globals.PProp.iter (fun x -> Printf.printf " S:%d = %s\n" x.Hashcons.tag (Pp.string_of_pprop G.lookup_sym x)) G.pprop_table;

	        let (params, goals) = Synthetics.make_synthetics (!ctxt) q in
	        Int.Table.iteri ~f:(fun ~key:i ~data:rules ->
            List.iter ~f:(fun r ->
              Printf.printf "LEFT RULE(S:%d)\n%s\n" i (Pp.string_of_x (Rule.pp_rule G.lookup_sym) r))
            rules) Synthetics.lfoc_rules;
	        Int.Table.iteri ~f:(fun ~key:i ~data:rules ->
            List.iter ~f:(fun r ->
              Printf.printf "RIGHT RULE(S:%d)\n%s\n" i (Pp.string_of_x (Rule.pp_rule G.lookup_sym) r))
            rules) Synthetics.rfoc_rules;
	        Printf.printf "Goals:\n";
	        Printf.printf "%s\n" (Pp.string_of_x (fun fmt -> Pp.pp_list_aux fmt "\n" (Rule.pp_sequent G.lookup_sym fmt)) goals);
          let heuristic state = 0
            (* debug "heuristic called";
             * let result = (MCTS.search_rounds 1 state) in
             * -result.wins *)
          in
          let success = Prover.search_goals heuristic params (fun _ _ _ -> ()) goals in
          if Option.is_some success then
            debug "PROOF SEARCH SUCCEEDED\n"
          else
            debug "PROOF SEARCH FAILED\n")
      | Ast.Axiom ->
        begin
          begin if !Pp.verbose then Printf.printf "adding axiom: " end;
	        let q = Translate.prop_to_pprop [] p in  (* positive proposition *)
	        begin if !Pp.verbose then Printf.printf "%s\n" (Pp.string_of_pprop G.lookup_sym q) else () end;
          (*	  let l = G.gen_tag () in *)
	        let g = !ctxt in
	        ctxt := q::g
	      end
      | _ ->  Printf.printf "Role not supported\n";
        Printf.printf "Proposition %s : %s\n" s (Pp.string_of_nprop G.lookup_sym (Translate.prop_to_nprop [] p))
    end

let process_file =
  ctxt := [];
  List.iter ~f:process_input


let do_file fn =
  let _ = Printf.printf "Processing: %s\n" fn in
  let buffer = In_channel.create fn in
  let ast = Processor.ast_from_lexbuf fn (Lexing.from_channel buffer) in
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
