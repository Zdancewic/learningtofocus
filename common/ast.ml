(* Abstract syntax for source input files *)
type var = string (* uppercase *)

type binop =
	| Iff
	| Imp
	| RevImp
	| NotIff
	| NotOr
	| NotAnd
	| And
	| Or

type tm =
	| Var of var
	| Fun of string * tm list

type prop =
	| Prop of string * tm list
	| BinOp of prop * binop * prop
	| All of var list * prop
	| Exists of var list * prop
  | Not of prop
	| Eq of tm * tm
	| True 
	| False

type role =
  | Axiom 
	| Hypothesis 
	| Definition 
	| Assumption 
	| Lemma 
	| Theorem 
	| Conjecture 
	| Neg_conjecture 
	| Plain 
	| Fi_domain 
	| Fi_functors 
	| Fi_predicates 
	| Type
  | Unknown

type input =
	| Include of string * string list
	| Fof of string * role * prop 

type file = input list





		


