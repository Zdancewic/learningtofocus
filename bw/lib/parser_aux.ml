open Core
open Common
open Util
open Range

let ast_from_lexbuf filename buf =
  try
    Lexer.reset_lexbuf filename buf;
    Parser.file Lexer.token buf
  with Parsing.Parse_error ->
    failwith (Printf.sprintf "Parse error at %s."
                (string_of_range (Lexer.lex_range buf)))
let parse_file fn =
  let buffer = In_channel.create fn in
  let ast = ast_from_lexbuf fn (Lexing.from_channel buffer) in
  In_channel.close buffer;
  ast

let parse_string str =
  ast_from_lexbuf "<string>" (Lexing.from_string str)

let process_parsed_file (module G : Globals.T) (module TRANS : Translate.S) ast = 
  let axioms = ref [] in
  let goals = ref [] in
  let goal_names = ref [] in
  let includes = ref [] in
  let do_input i =
    match i with
    | Ast.Include _ -> includes := i :: !includes
    | Ast.Fof(s, r, p) -> begin
        match r with
        | Ast.Conjecture -> (
            let q = TRANS.prop_to_nprop [] p in
            goals := q :: (!goals);
            goal_names := s :: !goal_names
        )
        | Ast.Axiom -> axioms := (TRANS.prop_to_pprop [] p) :: !axioms
        | _ ->  Printf.printf "Role not supported\n";
          Printf.printf "Proposition %s : %s\n" s (Pp.string_of_nprop G.lookup_sym (TRANS.prop_to_nprop [] p));
          failwith ""
      end
  in
  List.iter ~f:do_input ast;
  (!axioms, !goals, !goal_names, !includes)

let parsed_to_synths ast =
  let open State in
  let axioms, goals, _goal_names, _includes = process_parsed_file (module G) (module TRANS) ast in
  let l = List.map goals ~f:(fun goal ->
    SYNTH.make_synthetics axioms goal
  ) in
  assert (List.length l = 1);
  (* FIXME: this is massively stateful, as lfoc_rules and rfoc_rules won't be cleared between runs *)
  let synth_params, synth_goals = List.nth_exn l 0 in
  synth_params, synth_goals, SYNTH.lfoc_rules, SYNTH.rfoc_rules