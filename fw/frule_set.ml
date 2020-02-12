
module type Rule_type = 
  sig 
    type t
    val compare : t -> t -> int
  end

module Make_Rule_type (RULES:Frule.S) : (Rule_type with type t = int * RULES.t) = struct
  open RULES
  type t = int * RULES.t
  let compare (i1, r1) (i2, r2) = 
    if (i1 != i2) then (i1-i2)
    else
      (match (r1, r2) with
      |	({params = params1; premises = prems1; conclusion = (assumps1, s1)}, {params = params2; premises = prems2; conclusion = (assumps2, s2)}) ->
	  if (Ftop.TagSet.equal params1 params2 = false) then Ftop.TagSet.compare params1 params2
	  else
	    if (RULES.compare_seq (assumps1, s1) (assumps2, s2) != 0) then RULES.compare_seq (assumps1, s1) (assumps2, s2)
	    else
	      if (List.length prems1 != List.length prems2) then List.length prems1 - List.length prems2
	      else
		if (List.length prems1 == 0) then 0
		else
		  if (List.length prems1 == 1) then 
		    (match (prems1, prems2) with
		    | ([(assumps1', s1')], [(assumps2', s2')]) -> RULES.compare_seq (assumps1', s1') (assumps2', s2'))
		  else 
		    (match (prems1, prems2) with
		    | ( ((assumps11, s11)::[(assumps12, s12)]),  ((assumps21, s21)::[(assumps22, s22)])) ->
			let q1 = RULES.compare_seq (assumps11, s11) (assumps12, s12) in
			let q2 = RULES.compare_seq (assumps21, s21) (assumps22, s22) in
			let b1 = q1 < 0 in
			let b2 = q2 < 0 in
			(match (b1, b2) with
			| (true, true) -> RULES.compare_seq (assumps11, s11) (assumps21, s21)
			| (true, false) -> RULES.compare_seq (assumps11, s11) (assumps22, s22)
			| (false, true) -> RULES.compare_seq (assumps12, s12) (assumps21, s21)
			| (false, false) -> RULES.compare_seq (assumps12, s12) (assumps22, s22))))
end

module Make (RULES:Frule.S) = Set.Make(Make_Rule_type(RULES))
