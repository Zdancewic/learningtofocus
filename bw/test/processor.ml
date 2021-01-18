open Util
open Common
open Range


module Make(G : Globals.T) = struct
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


  let heuristic state =
      let result = (MCTS.search_rounds 10 state) in
      -result.wins

  let prove axioms goal =
	    let (params, goals) = SYNTH.make_synthetics axioms goal in
      PROVER.search_goals heuristic params goals


  let process_input axioms i =
    begin match i with
    | Ast.Fof(_, role, p) ->
      begin match role with
        | Ast.Conjecture ->
          let q = TRANS.prop_to_nprop [] p in
          prove (!axioms) q
        | Ast.Axiom ->
	        let q = TRANS.prop_to_pprop [] p in
	        let g = !axioms in
	        axioms := q::g;
         true
        | _ ->
          failwith "Role not supported"
      end
    | _ -> failwith "Ast not supported"
    end

  let process_file ast =
    let axioms = ref [] in
    List.for_all (process_input axioms) ast

  let do_file fn =
    let buffer = open_in fn in
    let ast = ast_from_lexbuf fn (Lexing.from_channel buffer) in
    let result = process_file ast in
    close_in buffer;
    result

end
