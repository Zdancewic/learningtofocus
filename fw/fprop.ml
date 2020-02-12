module type S = 
	sig
		open Ftm_rep
		open Fprop_rep

		val sp_pred : Ftop.tag -> (tm list) -> sign -> s_prop
		val sp_and : s_prop -> s_prop -> sign -> s_prop
		val sp_imp : s_prop -> s_prop -> sign -> s_prop    
		val sp_or : s_prop -> s_prop -> sign -> s_prop
		val sp_not : s_prop -> sign -> s_prop
                val sp_top : sign -> s_prop
                val sp_bot : sign -> s_prop
                val sp_emp : sign -> s_prop

		val subst_tsp : Ftop.tag -> tm -> s_prop -> s_prop
		val msubst_tsp : (Ftop.tag * tm) list -> s_prop -> s_prop
		
		val fv_s_prop : s_prop -> Ftop.TagSet.t
	end
	
module Make(G : Fglobals.T)(TMS:Ftm.S) : S = struct
	open Ftm_rep
	open Fprop_rep 
	
	let sp_pred t l sn =   Fglobals.FProp.hashcons G.fprop_table (SProp_pred ((t,l),sn))
	let sp_and sp1 sp2 sn =  Fglobals.FProp.hashcons G.fprop_table (SProp_and ((sp1,sp2),sn))
	let sp_imp sp1 sp2 sn = Fglobals.FProp.hashcons G.fprop_table (SProp_imp ((sp1,sp2),sn))
	let sp_or sp1 sp2 sn = Fglobals.FProp.hashcons G.fprop_table (SProp_or ((sp1, sp2), sn))
	let sp_not sp sn =  Fglobals.FProp.hashcons G.fprop_table (SProp_not (sp, sn))
	
	let sp_top sn =    Fglobals.FProp.hashcons G.fprop_table (SProp_top sn)
	let sp_bot sn =  Fglobals.FProp.hashcons G.fprop_table (SProp_bot sn)
	let sp_emp sn = Fglobals.FProp.hashcons G.fprop_table (SProp_Emp sn)
	
  let rec subst_tsp x u p =
    let subst_tsp_xu = subst_tsp x u in
    match p.Hashcons.node with
    | SProp_pred ((t, l), sn) ->  sp_pred t (List.map (TMS.subst_tt x u) l) sn
    | SProp_and ((sp1, sp2), sn) -> sp_and (subst_tsp_xu sp1) (subst_tsp_xu sp2) sn
    | SProp_imp ((sp1, sp2), sn) -> sp_imp (subst_tsp_xu sp1) (subst_tsp_xu sp2) sn
    | SProp_or ((sp1, sp2),sn) -> sp_or (subst_tsp_xu sp1) (subst_tsp_xu sp2) sn
    | SProp_not (sp, sn) -> sp_not (subst_tsp_xu sp) sn
    | SProp_top sn -> p
    | SProp_bot sn -> p
    | SProp_Emp sn-> p

  let rec msubst_tsp m p =
    let msubst_tsp_m = msubst_tsp m in
    match p.Hashcons.node with
    | SProp_pred ((t, l), sn) ->  sp_pred t (List.map (TMS.msubst_tt m) l) sn
    | SProp_and ((sp1, sp2), sn) -> sp_and (msubst_tsp_m sp1) (msubst_tsp_m sp2) sn
    | SProp_imp ((sp1, sp2), sn) -> sp_imp (msubst_tsp_m sp1) (msubst_tsp_m sp2) sn
    | SProp_or ((sp1, sp2),sn) -> sp_or (msubst_tsp_m sp1) (msubst_tsp_m sp2) sn
    | SProp_not (sp, sn) -> sp_not (msubst_tsp_m sp) sn
    | SProp_top sn -> p
    | SProp_bot sn -> p
    | SProp_Emp sn -> p

  let rec fv_s_prop p : Ftop.TagSet.t =
    match p.Hashcons.node with
    | SProp_pred ((t, l), sn) ->  List.fold_left (fun a t -> Ftop.TagSet.union a (TMS.fv_t t)) Ftop.TagSet.empty l
    | SProp_and ((sp1, sp2), sn) -> Ftop.TagSet.union (fv_s_prop sp1) (fv_s_prop sp2)
    | SProp_imp ((sp1, sp2), sn) -> Ftop.TagSet.union (fv_s_prop sp1) (fv_s_prop sp2)
    | SProp_or ((sp1, sp2),sn) -> Ftop.TagSet.union (fv_s_prop sp1) (fv_s_prop sp2)
    | SProp_not (sp, sn) -> fv_s_prop sp
    | SProp_top sn -> Ftop.TagSet.empty
    | SProp_bot sn -> Ftop.TagSet.empty
    | SProp_Emp sn-> Ftop.TagSet.empty					
																					
end
