open Fol
open Pp
open List

type sign = 
  | Pos
  | Neg

type s_prop =     (* signed propositions *)
  | SProp_param of var * sign
  | SProp_pred of (id * (tm list)) * sign
  | SProp_and of (s_prop * s_prop) * sign
  | SProp_imp of (s_prop * s_prop) * sign
  | SProp_or  of (s_prop * s_prop) * sign
  | SProp_not of (s_prop) * sign
  | SProp_top of sign
  | SProp_bot of sign
  | SProp_Emp
  (*| SProp_all of (string * s_prop) * sign
  | SProp_ex  of (string * s_prop) * sign *)

type fw_ctxt = (lab * s_prop) list 

let rec rev_lookup (p:s_prop) (g:fw_ctxt) =
	match g with
		| [] -> raise Not_found
		| (l,q)::rest -> if p = q then l else rev_lookup p rest 

let debug_flag = ref false

let debug s =
	if !debug_flag then
		print_endline s
  else ()

let debug_breakpt () =
	if !debug_flag then
		let _ = Printf.printf "[Continue]\n"; read_line () in
		 ()
  else () 

let flip (s: sign) : sign = 
        match s with
	| Pos -> Neg
	| Neg -> Pos

let rec sign_form (ps:prop * sign) : (s_prop)=
	let (p,s) = ps in
	match p with 
	  | Prop_param v -> SProp_param (v, s)
	  | Prop_pred (h, l) -> SProp_pred ((h,l), s)
	  | Prop_and (p1, p2) -> SProp_and ((sign_form (p1, s), sign_form (p2, s)), s)
	  | Prop_imp (p1, p2) -> SProp_imp ((sign_form (p1, flip s), sign_form (p2, s)),s)
	  | Prop_or  (p1, p2) -> SProp_or ((sign_form (p1, s), sign_form (p2, s)),s)
          | Prop_not p1 -> SProp_not (sign_form (p1, flip s), s)
	  | Prop_top -> SProp_top s
	  | Prop_bot -> SProp_bot s
	 (*| Prop_all (h, p1) -> SProp_all ((h, sign_form (p1,s)), s) 
	  | Prop_ex  (h, p1) -> SProp_ex ((h, sign_form (p1, s)), s)   *)
	  | _ -> failwith "unimplemented"	

let rec fw_decompose_goal (sp:s_prop) : (s_prop list) =
        match sp with 
	| SProp_param _ -> [sp]
	| SProp_pred ((s, l), sn) -> [sp]
	| SProp_and ((sp1, sp2), s) -> append (fw_decompose_goal sp1) (append (fw_decompose_goal sp2) [sp])
	| SProp_imp ((sp1, sp2), s) -> append (fw_decompose_goal sp1) (append (fw_decompose_goal sp2) [sp])
	| SProp_or ((sp1, sp2), s) -> append (fw_decompose_goal sp1) (append (fw_decompose_goal sp2) [sp])
	| SProp_not (sp1, s) -> append (fw_decompose_goal sp1) [sp]
	| SProp_top s-> [sp]
	| SProp_bot s-> [sp]
     (* | SProp_all _ ->  *)
     (*	| SProp_ex  _ -> *)
	| SProp_Emp -> []

type sequent = fw_ctxt * s_prop

type init_seq = s_prop * s_prop

let fw_decompose_goal_seq (seq: init_seq): (s_prop list) =
       let (sp1, sp2) = seq in 
       append (fw_decompose_goal sp1) (fw_decompose_goal sp2)

exception Not_Found

let rec find_r (sp: s_prop) (s: sequent list) : fw_ctxt =
  match s with
  | [] -> raise Not_Found
  | (g, sp1)::tl ->
      if sp1 = sp then g
	  else find_r sp tl

let rec find_l (sp: s_prop) (s: sequent list) : (fw_ctxt * s_prop) =
  match s with 
  | [] -> raise Not_Found
  | (g, sp1)::tl ->
      (match g with
      |	sp::tl1 -> (tl1, sp1)
      |	_ -> find_l sp tl)

let rec find_cln (sp: s_prop) (s: sequent list) : bool =
   match s with 
   | [] -> false
   | hd :: tl ->
       let (g', sp') = hd in
       if (sp = sp') then true 
	else find_cln sp tl



let  find_sp (sp: s_prop) (g: fw_ctxt): fw_ctxt =
  match g with 
  | [] -> raise Not_Found
  | hd::tl ->
      let (l1, sp') = hd in
      if (sp = sp') then tl else 
       raise Not_Found

let fw_init_seq (sp_list: s_prop list) (i:int) (s:sequent list) : (sequent list) =
       let ele = nth sp_list i in
       
       match ele with 
       | SProp_param (v, sn) ->
	   (match sn with 
	   | Pos -> s
	   | Neg -> 
               try match (find_r (SProp_param (v,Pos)) s) with
               | g->s
               with 
                 Not_Found -> 
                   let l1 = gensym_lab () in
                   ([(l1, ele)], SProp_param (v, Pos)) ::s
           )
       | _ -> s

let atom_SProp (sp: s_prop) : bool = 
   match sp with
   | SProp_param (v, sn) -> true
   | _  -> false

let rec sub_form (sp: s_prop) (cln: s_prop) : bool = 
   if sp = cln then true
   else 
     (if atom_SProp sp = true then false
      else match cln with
      |	SProp_and ((c1, c2), sn) -> (sub_form sp c1) or (sub_form sp c2)
      |	SProp_imp ((c1, c2), sn) -> (sub_form sp c1) or (sub_form sp c2)
      |	SProp_or ((c1, c2), sn) -> (sub_form sp c1) or (sub_form sp c2)
      |	SProp_top sn -> false
      |	SProp_bot sn -> false
      |	SProp_Emp -> false
      |	_ -> failwith "unimplemented")

let fw_search_pos (ele: s_prop) (s: sequent list) (cln: s_prop) : (sequent list) = 
   if (sub_form ele cln = false) then s else

   match ele with
   |  SProp_and ((sp1, sp2), sn) ->
	if (find_cln ele s= false) then
          try match ( find_r sp1 s) with
	  | g1 -> 
             try match ( find_r sp2 s) with 
             | g2 -> (append g2 g1, ele) :: s
             with Not_Found -> s
          with Not_Found -> s
	else s

   | SProp_imp ((sp1, sp2),sn) ->
        if (find_cln ele s = false) then 
	  (try match (find_r sp2 s) with
           | g -> 
              try match (find_sp sp1 g) with
              | g' -> (g', ele):: s
               with Not_Found -> (g, ele):: s
           with Not_Found -> s)
        else s

   | SProp_or ((sp1, sp2),sn) ->
       if (find_cln ele s = false) then  
         try match (find_r sp1 s) with 
         | g1 ->
             let l1 = gensym_lab () in 
             try match (find_r sp2 s) with
             | g2 ->
                 let l2 = gensym_lab () in 
	         ((l2,sp2):: g2, ele):: (((l1,sp1):: g1, ele):: s)
	     with Not_Found ->
               ((l1,sp1)::g1, ele):: s
         with Not_Found ->
           try match(find_r sp2 s) with
           | g2 ->
               let l2 = gensym_lab () in 
               ((l2, sp2)::g2, ele)::s
           with Not_Found -> s                                    
       else s

   | SProp_not (sp1,sn) -> failwith "unimplemented"
   | SProp_top sn ->
       (try match (find_r ele s) with
       | g -> s
       with Not_Found -> ([], ele)::s)

   | SProp_bot sn -> s
   | _ -> failwith "unimplemented" 
         
let fw_search_neg (ele: s_prop) (s: sequent list) (cln: s_prop): (sequent list) = 
   match ele with 

   | SProp_and ((sp1, sp2), sn) ->
       (try match (find_l sp1 s) with
       | (g1, r1) ->
           try match (find_l sp2 s) with 
	   | (g2, r2) ->
	       if (find_cln r1 s=false && find_cln r2 s=false) then      (* To be fixed *)
                 let l1 = gensym_lab () in
		 ((l1,ele)::g1, r1)::(((l1,ele):: g2, r2):: s)
	       else (if (find_cln r1 s = false) then
                 let l1 = gensym_lab () in
		 ((l1,ele)::g1, r1):: s
	       else (if (find_cln r2 s = false) then 
                 let l1 = gensym_lab () in
                 ((l1,ele):: g2, r2):: s
	       else s))
	   with Not_Found ->
	     if (find_cln r1 s = false) then 
               let l1 = gensym_lab () in
               ((l1,ele):: g1, r1):: s 
             else s
       with Not_Found ->
         (try match (find_l sp2 s) with 
	 | (g2, r2) -> 
             if (sub_form r2 cln = true && find_cln r2 s = false) then 
               let l1 = gensym_lab () in
               ((l1,ele):: g2, r2):: s
	     else s
         with Not_Found -> s))
  | SProp_imp ((sp1, sp2),sn) -> 
      (try match (find_l sp2 s) with
      | (g2, c) ->
          if (sub_form c cln = true && find_cln c s = false) then
	    try match (find_r sp1 s) with
            | g1 ->    
                let l1 = gensym_lab () in 
		((l1,ele):: (append g2 g1),c):: s
	    with Not_Found -> s
          else s
      with Not_Found -> s)
  | SProp_or ((sp1, sp2),sn) ->
      (try match (find_l sp1 s) with
      | (g1,r1) ->
	  (try match (find_l sp2 s) with
          | (g2, r2) ->
              let sp =  SProp_or ((r1,r2),Pos) in
              if (sub_form sp cln = true && find_cln sp s = false) then
                let l1 = gensym_lab () in
		((l1, ele)::(append g2 g1),sp):: s
              else s
	  with Not_Found -> 
            if (sub_form r1 cln = true && find_cln r1 s = false) then
              let l1 = gensym_lab () in
              ((l1, ele)::g1, r1)::s
            else s)
      with Not_Found -> 
        (try match (find_l sp2 s) with
        | (g2, r2) ->
            if (sub_form r2 cln = true && find_cln r2 s = false) then
              let l1 = gensym_lab () in
	      ((l1, ele)::g2,r2):: s
            else s
	with Not_Found -> s))
  | SProp_not (sp1,sn) -> failwith "unimplemented"
  | SProp_top sn -> s
  | SProp_bot sn -> []
  | _ -> failwith "unimplemented"

let get_sign (sp: s_prop) : sign =
  match sp with
  | SProp_param (v, sn) -> sn
  | SProp_and (i, sn) -> sn
  | SProp_imp (i, sn) -> sn
  | SProp_or (i, sn) -> sn
  | SProp_not (i, sn) -> sn
  | SProp_bot sn -> sn
  | SProp_top sn -> sn
  | SProp_Emp -> Pos
  | _ -> failwith "unimplemented"


let fw_search_seq (sp_list: s_prop list) (i: int) (s: sequent list) (cln: s_prop): (sequent list) =
  let ele = nth sp_list i in 
  let sn = get_sign ele in
  match sn with
  | Pos -> fw_search_pos ele s cln
  | Neg -> fw_search_neg ele s cln

let fw_search (seq: init_seq):bool =
       let s = [] in
       let (sp_pre, sp_cln) = seq in
       let sp_list = fw_decompose_goal_seq seq in
       let len = length sp_list in
             
       for i = 1 to len do
	  s  = fw_init_seq sp_list i s
       done;

       let ss = [] in
       try while ss != s do
	 ss = s;
	 for i = 1 to len do 
	   s = fw_search_seq sp_list i s sp_cln
	 done;
	 if find_cln sp_cln s then 
	   raise Exit
       done ;
       false
       with Exit -> true

