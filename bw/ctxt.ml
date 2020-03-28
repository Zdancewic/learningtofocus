open Fol

type ctxt =
  {
    preds : (lab * id * tm) list;
    imps: (lab * prop * prop) list;
    alls: (lab * string * prop) list;  (* note, only one binder *)
  }

type goal =
  | Gpred of id * tm
  | Gex   of string * prop
  | Gor   of prop * prop
  | Gbot	

type judgment = ctxt * goal

type subst = (uvar * tm) list

let empty_subst = []

(*
type ctxt =
  | All of judgment list
  | One of subst * focus_options * judgment 


let rec prover u s =
  match x with
  | [] -> empty_subst
  | (All [])::r -> prover u r    (* Success! *)  
  | (All js)::r -> 	List.fold_left prover u js   (* This is wrong! *)
  | (One opts j)::r ->
    let (focus, rest) = choose opts in  (* fails if there are no options *)
    let (new_top, u') = normalize j focus u' in
    try
      prover u' (new_top::r)
    with
    | Backtrack -> prover u (One rest j)::r  

*)
