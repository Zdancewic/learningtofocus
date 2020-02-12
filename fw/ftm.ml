module type S =
	sig
		open Ftm_rep
		val tm_uvar  : int -> tm
		val tm_param : Ftop.tag -> tm
		val tm_fun   : Ftop.tag -> (tm list) -> tm
		
		val open_tt_aux : int -> tm -> tm -> tm
		val open_tt  : tm -> tm -> tm
		
		val close_tt_aux : int -> Ftop.tag -> tm -> tm
		val close_tt : Ftop.tag -> tm -> tm
		
		val subst_tt : Ftop.tag -> tm -> tm -> tm 
		val msubst_tt : (Ftop.tag * tm) list -> tm -> tm
		
		val fv_t : tm -> Ftop.TagSet.t  
	end  
		
module Make(G:Fglobals.T) : S = struct
	open Ftm_rep
	let tm_uvar i  = Fglobals.HTm.hashcons G.tm_table (Tm_uvar i)
	let tm_param a = Fglobals.HTm.hashcons G.tm_table (Tm_param a)
	let tm_fun f l = Fglobals.HTm.hashcons G.tm_table (Tm_fun (f, l)) 
	
	(* open replaces a *bound* variable with a term *)
  let rec open_tt_aux i u t =
  match t.Hashcons.node with
    | Tm_uvar j -> if i = j then u else tm_uvar j
    | Tm_param _ -> t
    | Tm_fun (f, ts) -> tm_fun f (List.map (open_tt_aux i u) ts)

  let open_tt = open_tt_aux 0							

  let rec close_tt_aux i x t =
	match t.Hashcons.node with
		| Tm_uvar _ -> t
		| Tm_param y -> if x = y then tm_uvar i else t
		| Tm_fun (f, ts) -> tm_fun f (List.map (close_tt_aux i x) ts)

  let close_tt = close_tt_aux 0

  let rec subst_tt x u t =
  match t.Hashcons.node with
		| Tm_uvar _ -> t
    | Tm_param y -> if x = y then u else t
    | Tm_fun (f, ts) -> tm_fun f (List.map (subst_tt x u) ts)

  let rec msubst_tt m t =
	match t.Hashcons.node with
			| Tm_uvar _ -> t
			| Tm_param y -> (try List.assoc y m with Not_found -> t)
			| Tm_fun (f, ts) -> tm_fun f (List.map (msubst_tt m) ts)
			
  let rec fv_t t =
	match t.Hashcons.node with
		| Tm_uvar _ -> Ftop.TagSet.empty
		| Tm_param y -> Ftop.TagSet.singleton y
		| Tm_fun (f, ts) -> List.fold_left (fun a t -> Ftop.TagSet.union a (fv_t t)) Ftop.TagSet.empty ts
end 
