open Util
open Common
open Range

let ast_from_lexbuf filename buf =
    try
      Lexer.reset_lexbuf filename buf;
      Parser.file Lexer.token buf
    with Parsing.Parse_error ->
      failwith (Printf.sprintf "Parse error at %s."
                  (string_of_range (Lexer.lex_range buf)))

let heuristic state = 0
      (* let result = (MCTS.search_rounds 10 state) in
       * -result.wins *)

let prove axioms goal =
	    let (params, goals) = Synthetics.make_synthetics axioms goal in
      Prover.search_goals heuristic params (fun _ _ _ -> ()) goals

let process_input axioms i =
    begin match i with
    | Ast.Fof(_, role, p) ->
      begin match role with
        | Ast.Conjecture ->
          let q = Translate.prop_to_nprop [] p in
          prove (!axioms) q
        | Ast.Axiom ->
	        let q = Translate.prop_to_pprop [] p in
	        let g = !axioms in
	        axioms := q::g;
         Some []
        | _ ->
          failwith "Role not supported"
      end
    | _ -> failwith "Ast not supported"
    end


let process_file ast =
    let axioms = ref [] in
    List.for_all (fun i -> Option.is_some (process_input axioms i)) ast

let do_file fn =
    let buffer = open_in fn in
    let ast = ast_from_lexbuf fn (Lexing.from_channel buffer) in
    let result = process_file ast in
    close_in buffer;
    result





