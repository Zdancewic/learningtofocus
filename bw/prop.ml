module type S = 
	sig
		open Tm_rep
		open Prop_rep
		
		val p_one : unit -> pprop
		val p_zero : unit -> pprop
		val p_or : pprop -> pprop -> pprop
		val p_ex : pprop -> pprop
		val p_shift : nprop -> pprop
		
		val n_top  : unit -> nprop
		val n_prop : Top.tag -> (tm list) -> nprop
		val n_and  : nprop -> nprop -> nprop
		val n_imp  : pprop -> nprop -> nprop
		val n_all  : nprop -> nprop
		val n_shift : pprop -> nprop 
	
		val open_pt_aux : int -> tm -> pprop -> pprop
		val open_pt : tm -> pprop -> pprop
		val open_nt_aux : int -> tm -> nprop -> nprop
		val open_nt : tm -> nprop -> nprop
		
	  val close_pt_aux : int -> Top.tag -> pprop -> pprop
		val close_pt : Top.tag -> pprop -> pprop
		val close_nt_aux : int -> Top.tag -> nprop -> nprop
		val close_nt : Top.tag -> nprop -> nprop

		val subst_tp : Top.tag -> tm -> pprop -> pprop
		val subst_tn : Top.tag -> tm -> nprop -> nprop
		val msubst_tp : (Top.tag * tm) list -> pprop -> pprop
		val msubst_tn : (Top.tag * tm) list -> nprop -> nprop
		
		val fv_pprop : pprop -> Top.TagSet.t
		val fv_nprop : nprop -> Top.TagSet.t
	end
	
module Make(G : Globals.T)(TMS:Tm.S) : S = struct
	open Tm_rep
	open Prop_rep 
	
	let p_one () =   Globals.PProp.hashcons G.pprop_table P_one
	let p_zero () =  Globals.PProp.hashcons G.pprop_table P_zero
	let p_or p1 p2 = Globals.PProp.hashcons G.pprop_table (P_or (p1, p2))
	let p_ex p =     Globals.PProp.hashcons G.pprop_table (P_ex p)
	let p_shift n =  Globals.PProp.hashcons G.pprop_table (P_shift n)
	
	let n_top () =    Globals.NProp.hashcons G.nprop_table N_top
	let n_prop t l =  Globals.NProp.hashcons G.nprop_table (N_prop (t, l))
	let n_and n1 n2 = Globals.NProp.hashcons G.nprop_table (N_and (n1, n2))
	let n_imp p1 n2 = Globals.NProp.hashcons G.nprop_table (N_imp (p1, n2))
	let n_all n =     Globals.NProp.hashcons G.nprop_table (N_all n)
	let n_shift p =   Globals.NProp.hashcons G.nprop_table (N_shift p)

	let rec open_pt_aux i u p =
    let open_pt_iu = open_pt_aux i u in 
    match p.Hashcons.node with
    | P_one -> p
		| P_zero -> p
		| P_or (p1, p2) -> p_or (open_pt_iu p1) (open_pt_iu p2)
		| P_ex p1 -> p_ex (open_pt_aux (i+1) u p1)
		| P_shift n -> p_shift (open_nt_aux i u n)
	and open_nt_aux i u n = 
	  let open_nt_iu = open_nt_aux i u in
		match n.Hashcons.node with
    | N_top -> n
		| N_prop (t, l) -> n_prop t (List.map (TMS.open_tt_aux i u) l)
		| N_and (n1, n2) -> n_and (open_nt_iu n1) (open_nt_iu n2)
		| N_imp (p1, n2) -> n_imp (open_pt_aux i u p1) (open_nt_iu n2)
		| N_all n1 -> n_all (open_nt_aux (i+1) u n1)
		| N_shift p -> n_shift (open_pt_aux i u p)

  let open_pt = open_pt_aux 0
	let open_nt = open_nt_aux 0

  let rec close_pt_aux i x p =
    let close_pt_ix = close_pt_aux i x in 
    match p.Hashcons.node with
		| P_one -> p
		| P_zero -> p
		| P_or (p1, p2) -> p_or (close_pt_ix p1) (close_pt_ix p2)
		| P_ex p1 -> p_ex (close_pt_aux (i+1) x p1)
		| P_shift n -> p_shift (close_nt_aux i x n)
	and close_nt_aux i x n =
		let close_nt_ix = close_nt_aux i x in
		match n.Hashcons.node with
	  | N_top -> n
		| N_prop (t, l)  -> n_prop t (List.map (TMS.close_tt_aux i x) l)
		| N_and (n1, n2) -> n_and (close_nt_ix n1) (close_nt_ix n2)
		| N_imp (p1, n2) -> n_imp (close_pt_aux i x p1) (close_nt_ix n2)
		| N_all n1 -> n_all (close_nt_aux (i+1) x n1)
		| N_shift p -> n_shift (close_pt_aux i x p) 
    
  let close_pt = close_pt_aux 0
	let close_nt = close_nt_aux 0
	
	let rec subst_tp x u p =
    let subst_tp_xu = subst_tp x u in
    match p.Hashcons.node with
    | P_one -> p
		| P_zero -> p
    | P_or (p1, p2) -> p_or (subst_tp_xu p1) (subst_tp_xu p2)
    | P_ex p1 -> p_ex (subst_tp_xu p1)
		| P_shift n -> p_shift (subst_tn x u n)
	and subst_tn x u n =
		let subst_tn_xu = subst_tn x u in
		match n.Hashcons.node with
		| N_top -> n
		| N_prop (t, l)  -> n_prop t (List.map (TMS.subst_tt x u) l)
		| N_and (n1, n2) -> n_and (subst_tn_xu n1) (subst_tn_xu n2)
		| N_imp (p1, n2) -> n_imp (subst_tp x u p1) (subst_tn_xu n2)
		| N_all n1 -> n_all (subst_tn_xu n1)
		| N_shift p -> n_shift (subst_tp x u p) 

  let rec msubst_tp m p =
    let msubst_tp_m = msubst_tp m in
    match p.Hashcons.node with
    | P_one -> p
		| P_zero -> p
    | P_or (p1, p2) -> p_or (msubst_tp_m p1) (msubst_tp_m p2)
    | P_ex p1 -> p_ex (msubst_tp_m p1)
		| P_shift n -> p_shift (msubst_tn m n)
	and msubst_tn m n =
		let msubst_tn_m = msubst_tn m in
		match n.Hashcons.node with
		| N_top -> n
		| N_prop (t, l)  -> n_prop t (List.map (TMS.msubst_tt m) l)
		| N_and (n1, n2) -> n_and (msubst_tn_m n1) (msubst_tn_m n2)
		| N_imp (p1, n2) -> n_imp (msubst_tp m p1) (msubst_tn_m n2)
		| N_all n1 -> n_all (msubst_tn_m n1)
		| N_shift p -> n_shift (msubst_tp m p) 

	let rec fv_pprop p : Top.TagSet.t =
		match p.Hashcons.node with
			| P_one -> Top.TagSet.empty
			| P_zero -> Top.TagSet.empty
			| P_or (p1, p2) -> Top.TagSet.union (fv_pprop p1) (fv_pprop p2)
			| P_ex p1 -> fv_pprop p1
			| P_shift n1 -> fv_nprop n1
	and fv_nprop n : Top.TagSet.t=
		match n.Hashcons.node with
			| N_top -> Top.TagSet.empty
			| N_prop(t, l) -> List.fold_left (fun a t -> Top.TagSet.union a (TMS.fv_t t)) Top.TagSet.empty l
			| N_and(n1, n2) -> Top.TagSet.union (fv_nprop n1) (fv_nprop n2)
			| N_imp(p1, n2) -> Top.TagSet.union (fv_pprop p1) (fv_nprop n2)
			| N_all n1 -> fv_nprop n1
			| N_shift p1 -> fv_pprop p1						
																					
end