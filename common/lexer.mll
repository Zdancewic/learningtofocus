{
  open Lexing
  open Parser
  open Range
  
  exception Lexer_error of Range.t * string
  
  (* Boilerplate to get ranges out of the lexer. *)
  
  let pos_of_lexpos p = mk_pos (p.pos_lnum) (p.pos_cnum - p.pos_bol)
  let mk_lex_range p1 p2 = mk_range (file_index_of_file p1.pos_fname)
      (pos_of_lexpos p1) (pos_of_lexpos p2)
  let lex_range lexbuf = mk_lex_range (lexeme_start_p lexbuf)
      (lexeme_end_p lexbuf)
  
  let newline lexbuf =
    lexbuf.lex_curr_p <- { (lexeme_end_p lexbuf) with
      pos_lnum = (lexeme_end_p lexbuf).pos_lnum + 1;
      pos_bol = (lexeme_end lexbuf) }

  let reset_lexbuf filename lexbuf =
    lexbuf.lex_curr_p <- {
      pos_fname = filename;
      pos_cnum = 0;
      pos_bol = 0;
      pos_lnum = 1;
    }
    
  (* Boilerplate to define exceptional cases in the lexer. *)
  let unexpected_char lexbuf c =
    raise (Lexer_error (lex_range lexbuf,
        Printf.sprintf "Unexpected character: '%c'" c))

  let unexpected_eof lexbuf =
    raise (Lexer_error (lex_range lexbuf, "Unexpected end of file"))

  (* It's convenient to handle escape codes in string literals directly inside
     the lexer. For this, we'll need a buffer to hold the translated part of
     the string. *)
  let begin_string lexbuf = ((lex_range lexbuf), Buffer.create 8)
  let finish_string info buf lexbuf =
    LITERAL ((lex_range lexbuf), Buffer.contents buf)
  let add_byte buf cha = Buffer.add_char buf cha
  let get_escaped cha =
    match cha with
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'r' -> '\r'
    | _ -> cha
  let add_escaped buf cha =
    let toadd = get_escaped cha
    in add_byte buf toadd
  
  (* To keep the size of the generated automaton small, we'll cheat and
     use tables for keywords. *)
  
  let kwdtab = [
		"include", (fun i -> KW_INCLUDE i);
    "fof", (fun i -> KW_FOF i);
		"axiom", (fun i -> KW_AXIOM i);
		"hypothesis", (fun i -> KW_HYPOTHESIS i);
		"definition", (fun i -> KW_DEFINITION i);
		"assumption", (fun i -> KW_ASSUMPTION i);
		"lemma", (fun i -> KW_LEMMA i);
		"theorem", (fun i -> KW_THEOREM i);
		"conjecture", (fun i -> KW_CONJECTURE i);
		"negated_conjecture", (fun i -> KW_NEG_CONJECTURE i);
		"plain", (fun i -> KW_PLAIN i);
		"fi_domain", (fun i -> KW_FI_DOMAIN i);
		"fi_functor", (fun i -> KW_FI_FUNCTORS i);
		"fi_predicates", (fun i -> KW_FI_PREDICATES i);
		"type", (fun i -> KW_TYPE i);
		"unknown", (fun i -> KW_UNKNOWN i); 
  ]

  let kwd_table =
		let tab = Hashtbl.create 128 in
		List.iter (fun (k,t) -> Hashtbl.add tab k t) kwdtab;
		tab
  
  let kwd_or_id lexbuf s =
    let r = lex_range lexbuf in
    if Hashtbl.mem kwd_table s then Hashtbl.find kwd_table s r
        else IDENT (r, s)
}

let newline = '\n' | ('\r' '\n')
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let character = uppercase | lowercase
let whitespace = ['\t' ' ']
let digit = ['0'-'9']

rule token = parse
  | lowercase (digit | character | '_')* { kwd_or_id lexbuf (lexeme lexbuf) }
	| uppercase (digit | character | '_')* { UIDENT (lex_range lexbuf, lexeme lexbuf) }
  | digit+ { INT (lex_range lexbuf, (Int32.of_string (lexeme lexbuf))) }
  | whitespace+ { token lexbuf }
  | newline { newline lexbuf; token lexbuf }
  | eof { EOF }
  | '\'' { let (info, buf) = begin_string lexbuf in string info buf lexbuf }
  | '(' { TOK_LPAREN (lex_range lexbuf) }
  | ')' { TOK_RPAREN (lex_range lexbuf) }
  | ',' { TOK_COMMA (lex_range lexbuf) }
  | '?' { TOK_QUESTION (lex_range lexbuf) }
  | '.' { TOK_DOT (lex_range lexbuf) }
  | ':' { TOK_COLON (lex_range lexbuf) }
  | '%' { comment_line lexbuf }
  | '[' { TOK_LBRACKET (lex_range lexbuf) }
  | ']' { TOK_RBRACKET (lex_range lexbuf) }
	| '!' { TOK_BANG (lex_range lexbuf) }
	| '&' { TOK_AMPERSAND (lex_range lexbuf) }
	| '|' { TOK_BAR (lex_range lexbuf) }
	| '~' { TOK_TILDE (lex_range lexbuf) }
	| "!=" { TOK_BANGEQ (lex_range lexbuf) }
	| "<=" { TOK_LTEQ (lex_range lexbuf) }
	| "=>" { TOK_EQGT (lex_range lexbuf) }
	| "<=>" { TOK_LTEQGT (lex_range lexbuf) }
	| "<~>" { TOK_LTTILDEGT (lex_range lexbuf) }
	| "~|" { TOK_TILDEBAR (lex_range lexbuf) }
	| "~&" { TOK_TILDEAMPERSAND (lex_range lexbuf) }
	| "*" { TOK_STAR (lex_range lexbuf) }
	| "+" { TOK_PLUS (lex_range lexbuf) }
	| "$true"  {TOK_TRUE (lex_range lexbuf) }
	| "$false" {TOK_FALSE (lex_range lexbuf) }
	| "/*" {comment 1 lexbuf }
  | _ as c { unexpected_char lexbuf c }
and comment_line = parse
  | whitespace+ "Status (intuit.) : " (whitespace | character | '-')* { print_endline (lexeme lexbuf); comment_line lexbuf }   
  | newline { newline lexbuf; token lexbuf }
	| eof { unexpected_eof lexbuf }
	| _ { comment_line lexbuf }
and comment nest = parse
  | "/*" { comment (nest + 1) lexbuf }
  | "*/" { if nest = 1 then token lexbuf else comment (nest - 1) lexbuf }
  | newline { newline lexbuf; comment nest lexbuf }
  | eof { unexpected_eof lexbuf }
  | _ { comment nest lexbuf }
and string info buf = parse
  | '\\' ("\"" | '\\' | 'n' | 't' | 'b' | 'r') {
      add_escaped buf (lexeme_char lexbuf 1);
      string info buf lexbuf }
  | '\'' { finish_string info buf lexbuf }
  | _ { add_byte buf (lexeme_char lexbuf 0); string info buf lexbuf }
  | eof { unexpected_eof lexbuf }
