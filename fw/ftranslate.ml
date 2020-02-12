
module Make(G : Fglobals.T)(TMS:Ftm.S)(PROPS:Fprop.S) = struct
  open TMS
  open PROPS
  open Ast

  type lab = int  (* move to Pf_rep *)

  type translation =
    | Binding of lab * prop
	  | Goal of prop

  let rec tm_to_tm m t =
	  match t with
		 | Var x -> tm_param (List.assoc x m)   
		 | Fun (s, tms) -> tm_fun (G.gen_sym s) (List.map (tm_to_tm m) tms)


  let rec prop_to_prop m p sn =
    let prop_not m p = sp_imp (prop_to_prop m p sn) (sp_emp sn) sn in
		match p with
			| BinOp (p1, bop, p2) ->
				(match bop with
					| Or -> sp_or (prop_to_prop m p1 sn) (prop_to_prop m p2 sn) sn
					| Iff -> prop_to_prop m (BinOp (BinOp (p1, Imp, p2), And, BinOp (p2, Imp, p1))) sn
					| Imp -> sp_imp (prop_to_prop m p1 (Fprop_rep.flip sn)) (prop_to_prop m p2 sn) sn
					| RevImp -> sp_imp (prop_to_prop m p2 (Fprop_rep.flip sn)) (prop_to_prop m p1 sn) sn 
					| NotIff -> prop_not m (BinOp (p1, Iff, p2))
					| NotOr  -> prop_not m (BinOp (p1, Or, p2))
					| NotAnd -> prop_not m (BinOp (p1, And, p2))
					| And    -> sp_and (prop_to_prop m p1 sn) (prop_to_prop m p2 sn) sn)
			| Prop (s, tms) -> sp_pred (G.gen_sym s) (List.map (tm_to_tm m) tms) sn
			| All  _ -> failwith "ALL not supported"
			| Exists _ -> failwith "EX not supported"
			| Not p' -> sp_imp (prop_to_prop m p' (Fprop_rep.flip sn)) (sp_emp sn) sn (*sp_not (prop_to_prop m p sn) sn*) 
			| Eq _  -> failwith "Term EQ primitive '=' not supported"
			| True  -> sp_top sn
			| False -> sp_bot sn

end
