/*
 * Steve Zdancewic
 * 
 * Parser for the FOF fragment of the TPTP standardized theorem prover syntax.
 * See the definition at this web page:
 *    http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html
 *
*/


%{
open Ast
%}

%token <Util.Range.t * string> IDENT
%token <Util.Range.t * string> UIDENT
%token <Util.Range.t * string> LITERAL
%token <Util.Range.t * int32> INT

%token <Util.Range.t> KW_INCLUDE
%token <Util.Range.t> KW_FOF
%token <Util.Range.t> KW_AXIOM 
%token <Util.Range.t> KW_HYPOTHESIS
%token <Util.Range.t> KW_DEFINITION
%token <Util.Range.t> KW_ASSUMPTION
%token <Util.Range.t> KW_LEMMA
%token <Util.Range.t> KW_THEOREM
%token <Util.Range.t> KW_CONJECTURE
%token <Util.Range.t> KW_NEG_CONJECTURE
%token <Util.Range.t> KW_PLAIN
%token <Util.Range.t> KW_FI_DOMAIN
%token <Util.Range.t> KW_FI_FUNCTORS
%token <Util.Range.t> KW_FI_PREDICATES
%token <Util.Range.t> KW_TYPE
%token <Util.Range.t> KW_UNKNOWN

%token <Util.Range.t> TOK_LPAREN
%token <Util.Range.t> TOK_RPAREN 
%token <Util.Range.t> TOK_COMMA 
%token <Util.Range.t> TOK_QUESTION 
%token <Util.Range.t> TOK_DOT 
%token <Util.Range.t> TOK_COLON 
/* %token <Util.Range.t> TOK_PERCENT  */
%token <Util.Range.t> TOK_LBRACKET 
%token <Util.Range.t> TOK_RBRACKET 
%token <Util.Range.t> TOK_BANG 
%token <Util.Range.t> TOK_BANGEQ
%token <Util.Range.t> TOK_AMPERSAND 
%token <Util.Range.t> TOK_BAR 
%token <Util.Range.t> TOK_TILDE 
%token <Util.Range.t> TOK_LTEQ 
%token <Util.Range.t> TOK_EQGT 
%token <Util.Range.t> TOK_LTEQGT 
%token <Util.Range.t> TOK_LTTILDEGT 
%token <Util.Range.t> TOK_TILDEBAR 
%token <Util.Range.t> TOK_TILDEAMPERSAND 
/* %token <Util.Range.t> TOK_STAR  */
/* %token <Util.Range.t> TOK_PLUS  */
%token <Util.Range.t> TOK_TRUE
%token <Util.Range.t> TOK_FALSE

%token EOF

%type <Ast.file> file
%type <Ast.file> tptp_input_list
%type <Ast.input> tptp_input
%type <Ast.input> include_input
%type <string list> formula_selection



%start file

%%

file:
  tptp_input_list EOF { $1 }
	
tptp_input_list:
  | /* empty */      { [] }
  | tptp_input tptp_input_list   { $1 :: $2 }

tptp_input:
  | annotated_formula     { $1 }
  | include_input         { $1 }

include_input:
  KW_INCLUDE TOK_LPAREN atomic_word formula_selection TOK_RPAREN TOK_DOT
	    { Include($3, $4) }
			
formula_selection:
  |  /* empty */      { [] }
  | TOK_COMMA name_list { $2 }

name_list:
  | name    { [$1] }
  | name TOK_COMMA name_list { $1 :: $3 }

name:
  | atomic_word  { $1 }
  | INT          { Int32.to_string (snd $1) }

atomic_word:
  | IDENT        { (snd $1) }
  | LITERAL      { (snd $1) }

/* The full TPTP spec includes other kinds of formulas here */
annotated_formula: 
  | fof_annotated   { $1 }

/* Note: the TPTP spec allows 'annotations', but we don't parse them currently */
fof_annotated:
  KW_FOF TOK_LPAREN name TOK_COMMA formula_role TOK_COMMA fof_formula TOK_RPAREN TOK_DOT
	  { Fof($3, $5, $7) }
		
formula_role:
  | KW_AXIOM { Axiom }
  | KW_HYPOTHESIS {Hypothesis}
  | KW_DEFINITION {Definition}
  | KW_ASSUMPTION {Assumption}
  | KW_LEMMA      {Lemma}
  | KW_THEOREM    {Theorem}
  | KW_CONJECTURE {Conjecture}
  | KW_NEG_CONJECTURE  {Neg_conjecture}
  | KW_PLAIN           {Plain}
  | KW_FI_DOMAIN       {Fi_domain}
  | KW_FI_FUNCTORS     {Fi_functors}
  | KW_FI_PREDICATES   {Fi_predicates}
  | KW_TYPE            {Type}
  | KW_UNKNOWN         {Unknown}

fof_formula:
  | fof_logic_formula  { $1 }
	
fof_logic_formula:
  | fof_binary_formula  { $1 }
  | fof_unitary_formula { $1 }

fof_binary_formula:
  | fof_binary_nonassoc { $1 }
  | fof_binary_assoc    { $1 }

fof_binary_nonassoc:
  | fof_unitary_formula binary_connective fof_unitary_formula { BinOp($1, $2, $3) }

fof_binary_assoc:
  | fof_or_formula  { $1 }
  | fof_and_formula { $1 }

fof_or_formula:
  | fof_unitary_formula TOK_BAR fof_unitary_formula { BinOp($1, Or, $3) }
  | fof_or_formula TOK_BAR fof_unitary_formula      { BinOp($1, Or, $3) }

fof_and_formula:
  | fof_unitary_formula TOK_AMPERSAND fof_unitary_formula { BinOp($1, And, $3) }
  | fof_and_formula TOK_AMPERSAND fof_unitary_formula      { BinOp($1, And, $3) }

fof_unitary_formula:
  | fof_quantified_formula  { $1 }
  | fof_unary_formula       { $1 }
  | atomic_formula          { $1 }
/*	| fof_conditional         { $1 }  */   /* part of extended syntax */
  | TOK_LPAREN fof_logic_formula TOK_RPAREN  { $2 }

fof_quantified_formula:
  | TOK_BANG TOK_LBRACKET fof_variable_list TOK_RBRACKET TOK_COLON fof_unitary_formula
    { All ($3, $6) }
  | TOK_QUESTION TOK_LBRACKET fof_variable_list TOK_RBRACKET TOK_COLON fof_unitary_formula
    { Exists ($3, $6) }

fof_variable_list:
  | UIDENT  { [ (snd $1) ] }
  | UIDENT TOK_COMMA fof_variable_list { (snd $1) :: $3 }

fof_unary_formula:
  | TOK_TILDE fof_unitary_formula    { Not $2 }
  | fol_infix_unary                  { $1 }

fol_infix_unary:
  | term TOK_BANGEQ term             { Not (Eq($1, $3)) }
	
atomic_formula:
  | plain_atomic_formula  { $1 }
  | defined_atomic_formula { $1 }  
/*	| system_atomic_formula  { $1 }  */

plain_atomic_formula:
  | IDENT       { Prop(snd $1, [] ) }
  | IDENT TOK_LPAREN arguments TOK_RPAREN  { Prop(snd $1, $3) }

arguments:
  | term   { [ $1 ] }
  | term TOK_COMMA arguments { $1 :: $3 }

term:
  | function_term  { $1 }
  | UIDENT   { Var(snd $1) }

function_term: 
  | IDENT     { Fun (snd $1, [] ) }
  | IDENT TOK_LPAREN arguments TOK_RPAREN { Fun(snd $1, $3) }

binary_connective:
  | TOK_LTEQGT { Iff }
  | TOK_EQGT   { Imp }
  | TOK_LTEQ   { RevImp }
  | TOK_LTTILDEGT { NotIff }
  | TOK_TILDEBAR { NotOr }
  | TOK_TILDEAMPERSAND { NotAnd }

defined_atomic_formula:
  | defined_plain_formula { $1 }
/* | defined_infix_formula */   /* We don't handle equality yet */

defined_plain_formula:   /* This rule short-circuits a bunch of the standard */
  | TOK_TRUE    { True }
  | TOK_FALSE   { False }
