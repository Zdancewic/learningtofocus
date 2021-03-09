  open Prop_rep

  val p_one : unit -> pprop
  val p_zero : unit -> pprop
  val p_or : pprop -> pprop -> pprop
  val p_ex : pprop -> pprop
  val p_shift : nprop -> pprop

  val n_top  : unit -> nprop
  val n_prop : Top.tag -> (Tm_rep.tm list) -> nprop
  val n_and  : nprop -> nprop -> nprop
  val n_imp  : pprop -> nprop -> nprop
  val n_all  : nprop -> nprop
  val n_shift : pprop -> nprop

  val open_pt_aux : int -> Tm_rep.tm -> pprop -> pprop
  val open_pt : Tm_rep.tm -> pprop -> pprop
  val open_nt_aux : int -> Tm_rep.tm -> nprop -> nprop
  val open_nt : Tm_rep.tm -> nprop -> nprop

  val close_pt_aux : int -> Top.tag -> pprop -> pprop
  val close_pt : Top.tag -> pprop -> pprop
  val close_nt_aux : int -> Top.tag -> nprop -> nprop
  val close_nt : Top.tag -> nprop -> nprop

  val subst_tp : Top.tag -> Tm_rep.tm -> pprop -> pprop
  val subst_tn : Top.tag -> Tm_rep.tm -> nprop -> nprop
  val msubst_tp : (Top.tag * Tm_rep.tm) list -> pprop -> pprop
  val msubst_tn : (Top.tag * Tm_rep.tm) list -> nprop -> nprop

  val fv_pprop : pprop -> Top.TagSet.t
  val fv_nprop : nprop -> Top.TagSet.t
