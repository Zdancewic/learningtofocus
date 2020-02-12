(*module type Rule_type = 
  sig 
    type t
    val compare : t -> t -> int
  end

module Make_Rule_type (RULES:Frule.S) : (Rule_type with type t = int * RULES.t) = struct
  type t = int * RULES.t
  let compare (i1, r1) (i2, r2) = i1 - i2
end

module RuleSet (RULES:Frule.S) = Set.Make(Make_Rule_type(RULES))*)

module Make (G:Fglobals.T)(TMS:Ftm.S)(PROPS:Fprop.S)(RULES:Frule.S)(* RULE_SET:Set.S with type elt = int * RULES.t *) = struct
  open Ftm_rep
  open Fprop_rep
  open Fpp
  open Hashcons
  open TMS
  open PROPS
  open RULES


type rule_t = (int, RULES.t) Hashtbl.t
let rules : rule_t = Hashtbl.create 251

(* type cln_t = (int, int) Hashtbl.t
let clns : cln_t = Hashtbl.create 251
*)		

  (* let rules = ref RULE_SET.empty *)
  let target = ref 0
  let final_rule = ref {params = Ftop.TagSet.empty; premises = []; conclusion = (Frule.AssumpSet.empty, PROPS.sp_emp Pos)}
  let ctxt = ref (Frule.AssumpSet.empty)
      
  let debug_flag = ref false
  let backtrack_flag = ref false
      
  let backtrack s n =
    if !backtrack_flag && n > 0 then
      Printf.printf "%s (depth %d)\n" s n
    else ()
	
  let debug s =
    if !debug_flag then
      print_endline s
    else ()
	
  let debug_breakpt () =
    if !debug_flag then
      let _ = Printf.printf "[Continue]\n"; read_line () in
      ()
    else () 
	
  let get_sign (sp: s_prop) : sign =
    match sp.Hashcons.node with
    | SProp_pred (v, sn) -> sn
    | SProp_and (i, sn) -> sn
    | SProp_imp (i, sn) -> sn
    | SProp_or (i, sn) -> sn
    | SProp_not (i, sn) -> sn
    | SProp_bot sn -> sn
    | SProp_top sn -> sn
    | SProp_Emp sn -> sn
  
  let rec flip_sp sp = 
    let n = sp.Hashcons.node in
    match n with 
    | SProp_pred ((t, l), sn) -> 
	if (mem_flip_sp sp = true) 
	then (Fglobals.FProp.hashcons G.fprop_table (SProp_pred ((t, l), flip sn)))
	else raise Not_found

    | SProp_and ((sp1, sp2), sn) -> 
	if ( (mem_flip_sp sp1 = false) or (mem_flip_sp sp2 = false)) then raise Not_found
	else 
	  let p1 = flip_sp sp1 in
	  let p2 = flip_sp sp2 in
	  if (Fglobals.FProp.mem G.fprop_table (SProp_and ((p1, p2), flip sn)) = true) 
	  then (Fglobals.FProp.hashcons G.fprop_table (SProp_and ((p1,p2), flip sn)))
	  else raise Not_found
	      
    | SProp_imp ((sp1, sp2), sn) -> 
	if ( (mem_flip_sp sp1 = false) or (mem_flip_sp sp2 = false)) then raise Not_found
	else 
	  let p1 = flip_sp sp1 in
	  let p2 = flip_sp sp2 in
	  if (Fglobals.FProp.mem G.fprop_table (SProp_imp ((p1, p2), flip sn)) = true) 
	  then (Fglobals.FProp.hashcons G.fprop_table (SProp_imp ((p1,p2), flip sn)))
	  else raise Not_found
	      
    | SProp_or ((sp1, sp2), sn) ->
	if ( (mem_flip_sp sp1 = false) or (mem_flip_sp sp2 = false)) then raise Not_found
	else 
	  let p1 = flip_sp sp1 in
	  let p2 = flip_sp sp2 in
	  if (Fglobals.FProp.mem G.fprop_table (SProp_or ((p1, p2), flip sn)) = true) 
	  then (Fglobals.FProp.hashcons G.fprop_table (SProp_or ((p1,p2), flip sn)))
	  else raise Not_found
	      
    | SProp_not (sp1, sn) -> 
	if (mem_flip_sp sp1 = false) then raise Not_found
	else
	  let p1 = flip_sp sp1 in
	  if (Fglobals.FProp.mem G.fprop_table (SProp_not (p1, flip sn)) = true) 
	  then (Fglobals.FProp.hashcons G.fprop_table (SProp_not (p1, flip sn)))
	  else raise Not_found
	      
    | SProp_top sn ->  
	if (Fglobals.FProp.mem G.fprop_table (SProp_top (flip sn)) = true) 
	then (Fglobals.FProp.hashcons G.fprop_table (SProp_top (flip sn)))
	else raise Not_found
	    
    | SProp_bot sn -> 
	if (Fglobals.FProp.mem G.fprop_table (SProp_bot (flip sn)) = true) 
	then (Fglobals.FProp.hashcons G.fprop_table (SProp_bot (flip sn)))
	else raise Not_found
	    
    | SProp_Emp sn -> Fglobals.FProp.hashcons G.fprop_table (SProp_Emp (flip sn))
	  
  and mem_flip_sp sp =
    let n = sp.Hashcons.node in
    match n with 
    | SProp_pred ((t, l), sn) -> Fglobals.FProp.mem G.fprop_table (SProp_pred ((t, l), flip sn))
	  
    | SProp_and ((sp1, sp2), sn) -> 
	if ( (mem_flip_sp sp1 = false) or (mem_flip_sp sp2 = false)) then false
	else 
	  let p1 = flip_sp sp1 in
	  let p2 = flip_sp sp2 in
	  Fglobals.FProp.mem G.fprop_table (SProp_and ((p1, p2), flip sn))
	    
    | SProp_imp ((sp1, sp2), sn) ->
	if ( (mem_flip_sp sp1 = false) or (mem_flip_sp sp2 = false)) then false
	else 
	  let p1 = flip_sp sp1 in
	  let p2 = flip_sp sp2 in
	  Fglobals.FProp.mem G.fprop_table (SProp_imp ((p1, p2), flip sn))
	    
    | SProp_or ((sp1, sp2), sn) -> 
	if ( (mem_flip_sp sp1 = false) or (mem_flip_sp sp2 = false)) then false
	else 
	  let p1 = flip_sp sp1 in
	  let p2 = flip_sp sp2 in
	  Fglobals.FProp.mem G.fprop_table (SProp_or ((p1, p2), flip sn))
	    
    | SProp_not (sp1, sn) -> 
	if ( (mem_flip_sp sp1 = false)) then false
	else 
	  let p1 = flip_sp sp1 in
	  Fglobals.FProp.mem G.fprop_table (SProp_not (p1, flip sn))
    | SProp_top sn ->  Fglobals.FProp.mem G.fprop_table (SProp_top (flip sn))
    | SProp_bot sn -> Fglobals.FProp.mem G.fprop_table (SProp_bot (flip sn))
    | SProp_Emp sn-> Fglobals.FProp.mem G.fprop_table (SProp_Emp (flip sn))
	  
  let make_init_rules sp = 
    let _ = debug ("\n\nmake_init_rules: " ^ Fpp.string_of_sprop G.lookup_sym sp) in
    let sn = get_sign sp in
    match sn with
    | Neg -> 
	(try 
	  let sp' = flip_sp sp in 
	  Hashtbl.add rules (sp'.Hashcons.tag) {params = Ftop.TagSet.empty; premises = []; conclusion = (Frule.AssumpSet.singleton sp, sp') }
	 (* rules := RULE_SET.add ((sp'.Hashcons.tag), {params = Ftop.TagSet.empty; premises = []; conclusion = (Frule.AssumpSet.singleton sp, sp') }) !rules *)
	with Not_found -> ()
	)
	  
    | Pos -> ()
	  
(*exception Found*)
	  
(*let res : RULES.t list= ref [] *) (* {params = Ftop.TagSet.empty; premises = []; conclusion = ([], Any)} *)
	  
  let find_right sp res t {params = p; premises = prems; conclusion = (assumps, sp') } =
    if (sp.Hashcons.tag == t) then
      (*let _ = Printf.printf "t = %d\n" t in *****************************************) 
      res := {params = p; premises = prems; conclusion = (assumps, sp')} :: !res
    else ()
    (*| Any -> ()*)
	  
	  
  let find_r sp =
    let res = ref [] in
    (* let _ = RULE_SET.iter (find_right sp res) !rules in *)
    let _ = Hashtbl.iter (find_right sp res) rules in
    !res
      
  let find_right_Emp res t {params = p; premises = prems; conclusion = (assumps, sp') } =
    if (Fglobals.FProp.mem G.fprop_table (SProp_Emp Pos) = true) then
      let sp1 = Fglobals.FProp.hashcons G.fprop_table (SProp_Emp Pos) in
      if (sp'.Hashcons.tag = sp1.Hashcons.tag) then
	res := {params = p; premises = prems; conclusion = (assumps, sp')} :: !res
      else ()
	  
  let find_r_Emp () = 
    let res = ref [] in
    (* let _ = RULE_SET.iter (find_right_Emp res) !rules in *)
    let _ = Hashtbl.iter (find_right_Emp res) rules in
    !res
      
(*let rec find_sp (sp: s_prop) (g: RULES.assumptions): RULES.assumptions =
   match g with 
  | [] -> raise Not_found
  | hd::tl ->
      if (sp = hd) then tl else hd::(find_sp sp tl)
*)

  let rec fw_pos_and_1 hd1 res2 sp t =
    match res2 with
    | [] -> ()
    | hd2::tl2 ->
	let {params = params1; premises = prems1; conclusion = (assumps1, s1)} = hd1 in
	let {params = params2; premises = prems2; conclusion = (assumps2, s2)} = hd2 in
	let _ =
	  let l = Hashtbl.find_all rules t in
	  let assms = Frule.AssumpSet.union assumps1 assumps2 in
	  let ele  = {params = Ftop.TagSet.union params1 params2; 
				 premises = [(assumps1, s1)] @ [(assumps2, s2)]; 
				 conclusion = (assms,  sp)} in 
	  if (List.mem ele l) then ()
	  else
	    let _ = Hashtbl.add rules t ele in
	    if (!target = t && Frule.AssumpSet.subset assms !ctxt) then 
	      let _ = final_rule := ele in
	      raise Exit 
	    else ()
	in
	fw_pos_and_1 hd1 tl2 sp t
	  
  let rec fw_pos_and res1 res2 sp t =
    match res1 with
    | [] -> ()
    | hd1::tl1 ->
	let _ = fw_pos_and_1 hd1 res2 sp t in
	fw_pos_and tl1 res2 sp t
	  
  let rec fw_pos_imp sp1 res2 sp t =
    match res2 with
    | [] -> ()
    | hd2::tl2 ->
	let {params = params2; premises = prems2; conclusion = (assumps2, s2)} = hd2 in
	let _ =
	  let assms = Frule.AssumpSet.remove sp1 assumps2 in                          (* Just remove A from G of G|-B if it exists, otherwise leave G unchanged *)
	  let l = Hashtbl.find_all rules t in
	  let ele = {params = Ftop.TagSet.diff params2 (fv_s_prop sp1); 
				  premises = [(assumps2, s2)]; 
				  conclusion = (assms, sp)} in
	  if (List.mem ele l) then ()
	  else 
	    let _ = Hashtbl.add rules t ele in
	    (* let _ = Printf.printf "Add  RULE Pos Imp (S:%d)\n%s\n" t (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) ele) in *)
	    if (!target = t && Frule.AssumpSet.subset assms !ctxt) then 
	      let _ = final_rule := ele in
	      raise Exit 
	    else ()
	in
	fw_pos_imp sp1 tl2 sp t
	  
  let rec fw_pos_or res1 sp t =
    match res1 with
    | [] -> ()
    | hd1::tl1 ->
	let {params = params1; premises = prems1; conclusion = (assumps1, s1)} = hd1 in
	let _ =
	  let l = Hashtbl.find_all rules t in
	  let ele = {params = params1; 
				  premises = [(assumps1, s1)]; 
				  conclusion = (assumps1,  sp)} in
	  if (List.mem ele l) then ()
	  else
	    (* let _ = Printf.printf "Add  RULE Pos Or (S:%d)\n%s\n" t (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) ele) in *)
	    let _ = Hashtbl.add rules t ele in
            (* let _ = Frule.AssumpSet.iter (fun x -> Printf.printf " %s\n" (Fpp.string_of_sprop G.lookup_sym x)) assumps1 in
            let _ = Frule.AssumpSet.iter (fun x -> Printf.printf " %s\n" (Fpp.string_of_sprop G.lookup_sym x)) !ctxt in
            let _ = Printf.printf "check subset = %b\n" (Frule.AssumpSet.subset assumps1 !ctxt) in *)
	    if (!target = t && Frule.AssumpSet.subset assumps1 !ctxt) then 
	      let _ = final_rule := ele in
	      raise Exit 
	    else ()
	in
	fw_pos_or tl1 sp t
	  
  let rec fw_pos_not res1 sp1 sp t =
    match res1 with
    | [] -> ()
    | hd1::tl1 ->
	let {params = params1; premises = prems1; conclusion = (assumps1, s1)} = hd1 in 
	let _ =
	  if (Frule.AssumpSet.mem sp1 assumps1) then
	    let l = Hashtbl.find_all rules t in
	    let assms = Frule.AssumpSet.remove sp1 assumps1 in
	    let ele = {params = Ftop.TagSet.diff params1 (fv_s_prop sp1);
				    premises = [(assumps1, s1)]; 
				    conclusion = (assms, sp)} in
	    if (List.mem ele l) then ()
	    else
	      (* let _ = Printf.printf "Add  RULE Pos Not (S:%d)\n%s\n" t (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) ele) in *)
	      let _ = Hashtbl.add rules t ele in
	      if (!target = t && Frule.AssumpSet.subset assms !ctxt) then 
		let _ = final_rule := ele in
		raise Exit 
	      else ()
	in
	fw_pos_not tl1 sp1 sp t

 (* let print_debug t = 
    Hashtbl.iter rules (fun t1 r1 -> if t1 = t then Printf.printf "debug here t1 = %d\n" t1 else ()) *)
	  
  let fw_search_pos (sp: s_prop) : unit = 
    let t = sp.Hashcons.tag in 
    (match sp.Hashcons.node with
    | SProp_pred ((tg, tl), sn) -> ()
	  
    | SProp_and ((sp1, sp2), sn) ->
	let res1 = find_r sp1 in 
	let res2 = find_r sp2 in
	fw_pos_and res1 res2 sp t
	  
    | SProp_imp ((sp1, sp2),sn) ->
	let res2 = find_r sp2 in
	(* let _ = if (!target = sp.Hashcons.tag) then let _ = print_debug sp2.Hashcons.tag in Printf.printf "Here!length = %d sp2.tag = %d\n" (List.length res2) sp2.Hashcons.tag else () in*)
	let _ = fw_pos_imp sp1 res2 sp t in
	let res_emp = find_r_Emp () in     (* Imp R3: if G,A|-Any, then G |- A -> B *) 
	fw_pos_imp sp1 res_emp sp t
	  
    | SProp_or ((sp1, sp2),sn) ->
	let res1 = find_r sp1 in
	let _ = fw_pos_or res1 sp t in
	let res2 = find_r sp2 in
	 fw_pos_or res2 sp t
	  
       (*if (Hashtbl.mem clns t = false) then  
          try match (find_r sp1) with 
          | {params = params1; premises = prems1; conclusion = (assumps1, s1)} ->
	  let _ = Hashtbl.add rules t {params = params1; 
	  premises = [(assumps1, s1)]; 
	  conclusion = (assumps1, Normal sp)} in
	  if (target = t && assumps1 = []) then raise Exit
	  else
	  let _ = Hashtbl.add clns t t in
          try match (find_r sp2) with
          | {params = params2; premises = prems2; conclusion = (assumps2, s2)} ->
	  let _ =  Hashtbl.add rules t {params = params2; 
	  premises = [(assumps2, s2)]; 
	  conclusion = (assumps2, Normal sp)} in
	  if (target = t && assumps2 = []) then raise Exit else ()
	  with Not_found ->
	  ()
          with Not_found ->
          try match (find_r sp2) with
          | {params = params2; premises = prems2; conclusion = (assumps2, s2)} ->
	  let _ = Hashtbl.add rules t {params = params2; 
	  premises = [(assumps2, s2)]; 
	  conclusion = (assumps2, Normal sp)} in
	  if (target = t && assumps2 = []) then raise Exit
	  else Hashtbl.add clns t t
	  with Not_found ->
          ()                                  
	  else () *)
	
    | SProp_not (sp1,sn) -> 
	(* if (Fglobals.FProp.mem G.fprop_table SProp_Emp = true) then *)
	  let res1 = find_r (PROPS.sp_emp Pos) in
	  fw_pos_not res1 sp1 sp t
	(* else () *)
	    
    | SProp_top sn ->
	let l = Hashtbl.find_all rules t in
	let ele = {params = Ftop.TagSet.empty;
				premises = []; 
				conclusion = (Frule.AssumpSet.empty, sp)} in
	if (List.mem ele l) then ()
	else
	  let _ = Hashtbl.add rules t ele in
	  if (!target = t) then raise Exit 
	  else ()
	      
    | SProp_bot sn -> failwith "Cannot Prove False"
	  
    | SProp_Emp sn -> ())
      
   (* | _ -> failwith "unimplemented" *)
  let find_left sp res t {params = p; premises = prems; conclusion = (assumps, cln) } =
    if (Frule.AssumpSet.mem sp assumps) then
      res := (t, {params = p; premises = prems; conclusion = (assumps, cln)}) :: !res
    else ()																		  
   

  let find_l sp = 
    let res = ref [] in
    (* let _ = RULE_SET.iter (find_left sp res) !rules in *)
    let _ = Hashtbl.iter (find_left sp res) rules in
    !res
   
  let rec fw_neg_and res1 sp1 sp =
    match res1 with
    | [] -> ()
    | hd1::tl1 ->
	let (t1, {params = params1; premises = prems1; conclusion = (assumps1, s1)}) = hd1 in
	let _ = 
	  let l = Hashtbl.find_all rules t1 in
          let assms = Frule.AssumpSet.add sp (Frule.AssumpSet.remove sp1 assumps1) in
	  let ele = {params = Ftop.TagSet.union params1 (fv_s_prop sp);
				   premises = [(assumps1, s1)]; 
				   conclusion = (assms, s1)} in
	  if (List.mem ele l) then ()
	  else
	    (* let _ = Printf.printf "Add  RULE Neg And (S:%d)\n%s\n" t1 (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) ele) in *)
	    let _ = Hashtbl.add rules t1 ele in
            if (!target = t1 && Frule.AssumpSet.subset assms !ctxt) then 
	      let _ = final_rule := ele in
	      raise Exit 
	    else ()
	in
	fw_neg_and tl1 sp1 sp

  let rec fw_neg_imp_2 res1 hd2 sp2 sp =
    match res1 with
    | [] -> ()
    | hd1::tl1 ->
	let {params = params1; premises = prems1; conclusion = (assumps1, s1)} = hd1 in
	let (t2, {params = params2; premises = prems2; conclusion = (assumps2, s2)}) = hd2 in
	let _ = 
	  let l = Hashtbl.find_all rules t2 in
          let assms = (Frule.AssumpSet.add sp (Frule.AssumpSet.union assumps1 (Frule.AssumpSet.remove sp2 assumps2))) in
	  let ele = {params = Ftop.TagSet.union params1 params2;
					 premises = [(assumps1, s1)]@[(assumps2, s2)]; 
					 conclusion = (assms, s2)} in
	  if (List.mem ele l) then ()
	  else
	    (* let _ = Printf.printf "Add  RULE Neg Imp (S:%d)\n%s\n" t2 (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) ele) in *)
	    let _ =  Hashtbl.add rules t2 ele in
            if (!target = t2 && Frule.AssumpSet.subset assms !ctxt) then 
	      let _ = final_rule := ele in
	      raise Exit 
	    else ()
	in
	fw_neg_imp_2 tl1 hd2 sp2 sp

  let rec fw_neg_imp res1 res2 sp2 sp =
    match res2 with
    | [] -> ()
    | hd2::tl2 ->
	let _ = fw_neg_imp_2 res1 hd2 sp2 sp in
	fw_neg_imp res1 tl2 sp2 sp

  let rec fw_neg_or_1 hd1 res2 sp1 sp2 sp =
    match res2 with
    | [] -> ()
    | hd2::tl2 ->
	let (t1, {params = params1; premises = prems1; conclusion = (assumps1, s1)}) = hd1 in
	let (t2, {params = params2; premises = prems2; conclusion = (assumps2, s2)}) = hd2 in
	let _ = 
          if (s1.Hashcons.tag = s2.Hashcons.tag) then
	    let t = s1.Hashcons.tag in
	    let assumps = Frule.AssumpSet.add sp (Frule.AssumpSet.union (Frule.AssumpSet.remove sp1 assumps1) (Frule.AssumpSet.remove sp2 assumps2)) in
	    let l = Hashtbl.find_all rules t in
	    let ele =  {params = Ftop.TagSet.union params1 params2;
				   premises = [(assumps1, s1)]@[(assumps2, s2)]; 
				   conclusion = (assumps, s1)} in
	    if (List.mem ele l) then ()
	    else
	      (* let _ = Printf.printf "Add  RULE Neg Or (S:%d)\n%s\n" t (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) ele) in *)
	      let _ = Hashtbl.add rules t ele in
              if (!target = t && Frule.AssumpSet.subset assumps !ctxt) then 
	        let _ = final_rule := ele in
	        raise Exit 
	      else ()
	  else ()
	in
	fw_neg_or_1 hd1 tl2 sp1 sp2 sp

  let rec fw_neg_or res1 res2 sp1 sp2 sp =
    match res1 with
    | [] -> ()
    | hd1::tl1 ->
	let _ = fw_neg_or_1 hd1 res2 sp1 sp2 sp in
	fw_neg_or tl1 res2 sp1 sp2 sp

  let rec fw_neg_not res1 sp =
    match res1 with
    | [] -> ()
    | hd1::tl1 ->
	let {params = params1; premises = prems1; conclusion = (assumps1, s1)} = hd1 in
	let _ = 
	  let sp' = PROPS.sp_emp Pos in
	  let t = sp'.Hashcons.tag in
	  let l = Hashtbl.find_all rules t in
          let assms = Frule.AssumpSet.add sp assumps1 in
	  let ele = {params = Ftop.TagSet.union params1 (fv_s_prop sp);
				  premises = [(assumps1, s1)];
				  conclusion = (assms, sp')} in
	  if (List.mem ele l) then ()
	  else
	    (* let _ = Printf.printf "Add  RULE Neg Not (S:%d)\n%s\n" t (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) ele) in *)
	    let _ = Hashtbl.add rules t ele in
            if (!target = t && Frule.AssumpSet.subset assms !ctxt) then 
	      let _ = final_rule := ele in
	      raise Exit 
	    else ()
	in
	fw_neg_not tl1 sp
          
  let fw_neg_emp emp sp =
    let sn = get_sign sp in
    if (sn = Neg) then () else
      let t = sp.Hashcons.tag in
      let l = Hashtbl.find_all rules t in
      let assms = Frule.AssumpSet.singleton emp in
      let ele = {params = Ftop.TagSet.empty;
				  premises = [];
				  conclusion = (assms, sp)} in
	  if (List.mem ele l) then ()
	  else
	    let _ = Hashtbl.add rules t ele in
            if (!target = t && Frule.AssumpSet.subset assms !ctxt) then 
	      let _ = final_rule := ele in
	      raise Exit 
	    else ()

  let fw_search_neg (sp : s_prop): unit= 
    (* let t = sp.Hashcons.tag in *)
    match sp.Hashcons.node with 
    | SProp_pred ((tg, tl), sn) -> ()
	  
    | SProp_and ((sp1, sp2), sn) ->
	let res1 = find_l sp1 in
	let _ = fw_neg_and res1 sp1 sp in
	let res2 = find_l sp2 in
	fw_neg_and res2 sp2 sp 
     (*(let _ = 
	 (try 
	   match (find_l sp1) with
	   | {params = params1; premises = prems1; conclusion = (assumps1, s1)} ->
	       match s1 with
	       | Normal s1sp ->
		   let ts1 = s1sp.Hashcons.tag in
		   Hashtbl.add rules ts1 {params = Ftop.TagSet.union params1 (fv_s_prop sp2); 
						    premises = [(assumps1 @ [sp1], s1)]; 
						    conclusion = (assumps1 @ [sp], s1)}
	       | Any -> raise Exit
          with Not_found -> ()) in
       try 
	 (match (find_l sp2) with 
	 | {params = params2; premises = prems2; conclusion = (assumps2, s2)} ->
	     match s2 with
	     | Normal s2sp ->
		 let ts2 = s2sp.Hashcons.tag in
		 Hashtbl.add rules ts2 {params = Ftop.TagSet.union params2 (fv_s_prop sp1); 
						  premises = [(assumps2 @[sp2], s2)]; 
						  conclusion = (assumps2 @[sp], s2)}
	     | Any -> raise Exit)
       with Not_found -> ())*)
   
  	       
    | SProp_imp ((sp1, sp2),sn) -> 
	(*let _ =  Printf.printf "Here!%s Number = %d\n" (Fpp.string_of_sprop G.lookup_sym sp) (Hashtbl.length rules) in
	 let _ = Hashtbl.iter (fun i r -> Printf.printf "RULE(S:%d)\n%s\n" i (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r)) rules in *)
	let res2 = find_l sp2 in
	(* let _ = List.iter (fun (i, r) ->  Printf.printf "RES2 RULE(S:%d)\n%s\n" i (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r)) res2 in *)
	
	let res1 = find_r sp1 in
	(* let _ = List.iter (fun r ->  Printf.printf "RES1 RULE\n %s\n" (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r)) res1 in *)
	fw_neg_imp res1 res2 sp2 sp 

    | SProp_or ((sp1, sp2),sn) ->
	let res1 = find_l sp1 in
	let res2 = find_l sp2 in
	fw_neg_or res1 res2 sp1 sp2 sp

  | SProp_not (sp1,sn) -> 
      let res1 = find_r sp1 in
      fw_neg_not res1 sp 

  | SProp_top sn -> ()

  | SProp_bot sn ->
      let sp' = PROPS.sp_emp Pos in
      let t = sp'.Hashcons.tag in
      let l = Hashtbl.find_all rules t in
      let ele = {params = Ftop.TagSet.empty;
			     premises = [];
			     conclusion = (Frule.AssumpSet.singleton sp,sp')} in
      if (List.mem ele l) then ()
      else
	Hashtbl.add rules t ele 

  | SProp_Emp sn -> 
      Fglobals.FProp.iter (fw_neg_emp sp) G.fprop_table
      (*let sp' = PROPS.sp_emp Pos in
      let t = sp'.Hashcons.tag in
      let l = Hashtbl.find_all rules t in
      let ele = {params = Ftop.TagSet.empty;
			     premises = [];
			     conclusion = (Frule.AssumpSet.singleton sp,sp')} in
      if (List.mem ele l) then ()
      else
	Hashtbl.add rules t ele *)

   (*|_ -> failwith "unimplemented"*)

let fw_search_seq sp = 
  let _ = debug ("\n\nfw_search_seq: " ^ Fpp.string_of_sprop G.lookup_sym sp) in
  let sn = get_sign sp in
  match sn with
  | Pos -> fw_search_pos sp
  | Neg -> fw_search_neg sp 

exception Found
 
let find_sequent seq res i r = 
  let {params = p; premises = prems; conclusion = (assms, cln)} = r in
  let (a, c) = seq in
  if ( Frule.AssumpSet.equal a assms && cln.Hashcons.tag = c.Hashcons.tag)
  then
    let _ = res := r in raise Found 
  else ()


let rec fw_steps t r d = 
  (* let r = Hashtbl.find_all rules t in *)
  let {params = p; premises = prems; conclusion = (assms, c)} = r in
  match prems with
  | [] -> Printf.printf "Depth = %d Premise = [] RULE(S:%d)\n%s\n" d c.Hashcons.tag (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r)
  | [hd] ->
      let (_, sh) = hd in
      let _ = Printf.printf "Depth = %d Premise = %d RULE(S:%d)\n%s\n" d sh.Hashcons.tag c.Hashcons.tag (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r) in
      let res = ref r in
      (try 
	 Hashtbl.iter (find_sequent hd res) rules
      with Found ->
	fw_steps sh.Hashcons.tag !res (d+1))

  | hd::[tl] ->
      let (_, sh) = hd in
      let (_, st) = tl in
      let _ = Printf.printf "Depth = %d Premise = %d and %d RULE(S:%d)\n%s\n" d sh.Hashcons.tag st.Hashcons.tag c.Hashcons.tag (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r) in
      let res = ref r in
      let _ = 
	try 
	  Hashtbl.iter (find_sequent hd res) rules
	with Found ->
	  fw_steps sh.Hashcons.tag !res (d+1) in
      try 
	  Hashtbl.iter (find_sequent tl res) rules
	with Found ->
	  fw_steps st.Hashcons.tag !res (d+1) 
    (* List.iter (fun (a, g) -> fw_steps g.Hashcons.tag (d+1)) prems *)
 
let fw_search g goal =
  let _ = ctxt := g in 
  let _ = Frule.AssumpSet.iter (fun x -> Printf.printf " %s\n" (Fpp.string_of_sprop G.lookup_sym x)) g in
   let _ = Fglobals.FProp.iter (make_init_rules) G.fprop_table in
   let _ =   Hashtbl.iter (fun i r -> Printf.printf "Number %d\nRULE(S:%d)\n%s\n" (Hashtbl.length rules) i (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r)) rules in 
   target := goal.Hashcons.tag;
   let ss = ref 0 in
   (*let round = ref 0 in *)
   try 
     while (!ss != Hashtbl.length rules) do
       (* Printf.printf "Round %d\n" !round;*)
       ss := Hashtbl.length rules;
       Fglobals.FProp.iter fw_search_seq G.fprop_table;
      (*Hashtbl.iter (fun i r -> Printf.printf "Round = %d Number %d\nRULE(S:%d)\n%s\n" !round (Hashtbl.length rules) i (Fpp.string_of_x (RULES.pp_rule G.lookup_sym) r)) rules;
        round := !round + 1; *)
       (* if (!round = 1) then raise Exit else ();*)
     done; 
     Printf.printf "false\n"
   with Exit -> 
     let _ = fw_steps !target !final_rule 0 in
     Printf.printf "true\n"
   (* Printf.printf "target tag is %d\n" target *)
end 
