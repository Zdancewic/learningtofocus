open Debug
open Core
open Util
open State

let print_processing_info axioms goals goal_names includes =
  let _ = Format.print_flush () in
  List.iter includes ~f:(Pp.pp_input);
  List.iter axioms ~f:(fun axiom ->
    if !Pp.verbose then Printf.printf "adding axiom: ";
    if !Pp.verbose then Printf.printf "%s\n" (Pp.string_of_pprop G.lookup_sym axiom)
  );
  List.iter2_exn goals goal_names ~f:(fun goal name ->
    let _ = Printf.printf " Proving %s" name in
    let _ = if !Pp.verbose then Printf.printf ": %s\n" (Pp.string_of_nprop G.lookup_sym goal) else
        Printf.printf "\n" in

    let _ = Printf.printf "Symbols:\n" in
    let _ = Hashtbl.iteri ~f:(fun ~key -> fun ~data:(s,t) -> Printf.printf " S:%d = %s[%d]\n" key s t) G.sym_table in
    let _ = Printf.printf"NProp Table:\n" in
    let _ = Globals.NProp.iter (fun x -> Printf.printf " S:%d = %s\n" x.Hashcons.tag (Pp.string_of_nprop G.lookup_sym x)) G.nprop_table in
    let _ = Printf.printf"PProp Table:\n" in
    Globals.PProp.iter (fun x -> Printf.printf " S:%d = %s\n" x.Hashcons.tag (Pp.string_of_pprop G.lookup_sym x)) G.pprop_table;
  );
  ()

let print_synthetics _synth_params synth_goals () = 
  Int.Table.iteri ~f:(fun ~key:i ~data:rules ->
    List.iter ~f:(fun r ->
      Printf.printf "LEFT RULE(S:%d)\n%s\n" i (Pp.string_of_x (RULES.pp_rule G.lookup_sym) r))
    rules) SYNTH.lfoc_rules;
  Int.Table.iteri ~f:(fun ~key:i ~data:rules ->
    List.iter ~f:(fun r ->
      Printf.printf "RIGHT RULE(S:%d)\n%s\n" i (Pp.string_of_x (RULES.pp_rule G.lookup_sym) r))
    rules) SYNTH.rfoc_rules;
  Printf.printf "Goals:\n";
  Printf.printf "%s\n" (Pp.string_of_x (fun fmt -> Pp.pp_list_aux fmt "\n" (RULES.pp_sequent G.lookup_sym fmt)) synth_goals)

let do_search params goals =
    let heuristic state =
    debug "heuristic called";
    let result = (MCTS.search_rounds 1 state) in
    -result.wins
  in
  let success = PROVER.search_goals heuristic params goals in
  if success then
    debug "PROOF SEARCH SUCCEEDED\n"
  else
    debug "PROOF SEARCH FAILED\n"


let do_file fn =
  let _ = Printf.printf "Processing: %s\n" fn in
  let ast = Parser_aux.parse_file fn in
  (* process_file ast; *)
  let axioms, goals, goal_names, includes = Parser_aux.process_parsed_file (module G) (module TRANS) ast in
  print_processing_info axioms goals goal_names includes;
  
  List.iter goals ~f:(fun goal ->
    let synth_params, synth_goals = SYNTH.make_synthetics axioms goal in
    print_synthetics synth_params synth_goals ();
    do_search synth_params synth_goals
    )

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
