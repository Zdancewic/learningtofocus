open Util
open Globals
open Tm_rep

  (** Bound variable (dB index) *)
  let tm_bvar (i : int) : tm  = HTm.hashcons G.tm_table (Tm_bvar i)

  (** Free variable *)
  let tm_fvar (a : Top.tag) : tm = HTm.hashcons G.tm_table (Tm_fvar a)

  (** Term-level uninterpreted function application *)
  let tm_fun f (l : tm list) : tm = HTm.hashcons G.tm_table (Tm_fun (f, l))

  (** replace a *bound* variable (index i) with a term u in t *)
  let rec open_tt_aux (i:int) (u:tm) (t:tm) : tm =
    match t.Hashcons.node with
    | Tm_bvar j -> if i = j then u else tm_bvar j
    | Tm_fvar _ -> t
    | Tm_fun (f, ts) -> tm_fun f (List.map (open_tt_aux i u) ts)

  let open_tt : tm -> tm -> tm = open_tt_aux 0

  (** Replace bound variables whose index corresponds to a term in us *)
  let rec mopen_tt (us:tm list) (t:tm) : tm =
    match t.Hashcons.node with
    | Tm_bvar j ->
      begin match List.nth_opt us j with
        | Some u -> u
        | None -> t
      end
    | Tm_fvar _ -> t
    | Tm_fun (f, ts) -> tm_fun f (List.map (mopen_tt us) ts)

  let rec close_tt_aux (i:int) (x:Top.tag) (t:tm) : tm =
    match t.Hashcons.node with
    | Tm_bvar _ -> t
    | Tm_fvar y -> if x = y then tm_bvar i else t
    | Tm_fun (f, ts) -> tm_fun f (List.map (close_tt_aux i x) ts)

  let close_tt : Top.tag -> tm -> tm = close_tt_aux 0

  let rec subst_tt (x:Top.tag) (u:tm) (t:tm) : tm =
    match t.Hashcons.node with
    | Tm_bvar _ -> t
    | Tm_fvar y -> if x = y then u else t
    | Tm_fun (f, ts) -> tm_fun f (List.map (subst_tt x u) ts)

  let rec msubst_tt (m:(Top.tag * tm) list) (t:tm) : tm =
    match t.Hashcons.node with
    | Tm_bvar _ -> t
    | Tm_fvar y -> (try List.assoc y m with Not_found -> t)
    | Tm_fun (f, ts) -> tm_fun f (List.map (msubst_tt m) ts)

  let rec fv_t (t:tm) : Top.TagSet.t =
    match t.Hashcons.node with
    | Tm_bvar _ -> Top.TagSet.empty
    | Tm_fvar y -> Top.TagSet.singleton y
    | Tm_fun (_, ts) -> List.fold_left (fun a t -> Top.TagSet.union a (fv_t t)) Top.TagSet.empty ts
