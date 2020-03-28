(* Datatypes for first-order logic *)
(* represented using locally-nameless *)

(* Metavariable conventions:

  i, j : int   for bound variables, bound labels
  t, u : tm    for terms
  x, y : var   for term variables
  f, g : id    for term functions
  p, q : prop  for propositions
  a, b : var   for parameters
  m, n : pf    for proof terms  
  l, k : lab   for labels
  c, d : uvar  for unification variables
  r, s : un    for unification goals
*)

type atom = string
type var = atom
type id = string * int   (* int is the arity of the identifier *)
type uvar = int * var
type lab = string * int  (* string is just a printing hint *)

let (gensym_lab, gensym_lab_hint) =
  let l = ref 0 in
  ((function () ->
       let a = !l in
       incr l; ("l", a)),
   (function (h:string) ->
      let a = !l in
      incr l; (h, a)))

let (gensym_var, gensym_var_hint) =
  let l = ref 0 in
  ((function () ->
       let a = !l in
       incr l; "v" ^ (string_of_int a)),
   (function h ->
      let a = !l in
      incr l; h ^ (string_of_int a)))

let gensym_uvar : int -> uvar =
  let l = ref 0 in
  function (s:int) ->
    let a = !l in
    incr l; (s, "X" ^ (string_of_int a))


let arity (x:id) = snd x

type tm =
  | Tm_uvar of uvar  (* int is the "level",  var is a unique id *)
  | Tm_bv of int     (* de Bruijn index *)
  | Tm_fv of var     (* what is the difference between a free variable and a parameter? *)
  | Tm_fun of id * (tm list)  (* length of the list should agree with id's arity *)

type prop =
  | Prop_param of var
  | Prop_pred of id * (tm list)
  | Prop_and of prop * prop
  | Prop_imp of prop * prop
  | Prop_or  of prop * prop
  | Prop_not of prop
  | Prop_top 
  | Prop_bot
  | Prop_all of string * prop   (* string is a variable name hint *)
  | Prop_ex  of string * prop

(* open replaces a *bound* variable with a term *)
let rec open_tt_aux i u t =
  match t with
  | Tm_uvar _ -> t
  | Tm_bv j -> if i = j then u else Tm_bv j
  | Tm_fv _ -> t
  | Tm_fun (f, ts) -> Tm_fun (f, (List.map (open_tt_aux i u) ts))

let open_tt = open_tt_aux 0							

let rec close_tt_aux i x t =
  match t with
  | Tm_uvar _ -> t
  | Tm_bv   _ -> t
  | Tm_fv y   ->  if x = y then (Tm_bv i) else t
  | Tm_fun (f, ts) -> Tm_fun (f, (List.map (close_tt_aux i x) ts))

let close_tt = close_tt_aux 0

let rec open_pt_aux i u p =
  let open_pt_iu = open_pt_aux i u in 
  match p with
  | Prop_param _ -> p
  | Prop_pred (q, ts) -> Prop_pred (q, (List.map (open_tt_aux i u) ts))
  | Prop_and (p1, p2) -> Prop_and (open_pt_iu p1, open_pt_iu p2)
  | Prop_imp (p1, p2) -> Prop_imp (open_pt_iu p1, open_pt_iu p2)
  | Prop_or  (p1, p2) -> Prop_or (open_pt_iu p1, open_pt_iu p2)
  | Prop_not p1 -> Prop_not (open_pt_iu p1)
  | Prop_top    -> Prop_top
  | Prop_bot    -> Prop_bot
  | Prop_all (h, p1) -> Prop_all (h, open_pt_aux (i+1) u p1)
  | Prop_ex  (h, p1) -> Prop_ex  (h, open_pt_aux (i+1) u p1)

let open_pt = open_pt_aux 0

let rec close_pt_aux i x p =
  let close_pt_ix = close_pt_aux i x in 
  match p with
  | Prop_param _ -> p
  | Prop_pred (q, ts) -> Prop_pred (q, (List.map (close_tt_aux i x) ts))
  | Prop_and (p1, p2) -> Prop_and (close_pt_ix p1, close_pt_ix p2)
  | Prop_imp (p1, p2) -> Prop_imp (close_pt_ix p1, close_pt_ix p2)
  | Prop_or  (p1, p2) -> Prop_or (close_pt_ix p1, close_pt_ix p2)
  | Prop_not p1 -> Prop_not (close_pt_ix p1)
  | Prop_top    -> Prop_top
  | Prop_bot    -> Prop_bot
  | Prop_all (h, p1) -> Prop_all (h, close_pt_aux (i+1) x p1)
  | Prop_ex  (h, p1) -> Prop_ex  (h, close_pt_aux (i+1) x p1)

let close_pt = close_pt_aux 0


(* Note: could separate these into left and right forms, where
   let binds only left forms *)
type pf =
  | Pf_flab   of lab    (* these are witnesses for primitive propositions *)
  | Pf_blab   of int
  | Pf_pair   of pf * pf
  | Pf_fst    of pf
  | Pf_snd    of pf
  | Pf_abs    of prop * pf  
  | Pf_app    of pf * pf
  | Pf_inl    of prop * pf
  | Pf_inr    of prop * pf
  | Pf_case   of pf * pf * pf
  | Pf_not    of prop * pf
  | Pf_contra of pf * prop * pf
  | Pf_unit
  | Pf_abort  of prop * pf
  | Pf_all    of string * pf   (* string is a hint for var generation *)
  | Pf_inst   of pf * tm
  | Pf_pack   of tm * pf
  | Pf_unpack of string * pf * pf (* string is a hint for var generation *)
  | Pf_let    of pf * pf

(* [n/i]m *)
let rec open_mm_aux i n m =
  let open_mm_in = open_mm_aux i n in
  match m with
  | Pf_flab _        -> m
  | Pf_blab j        -> if i = j then n else m
  | Pf_pair (m1, m2) -> Pf_pair (open_mm_in m1, open_mm_in m2)
  | Pf_fst m1        -> Pf_fst (open_mm_in m1)
  | Pf_snd m1        -> Pf_snd (open_mm_in m1)
  | Pf_abs (p, m1)   -> Pf_abs (p, open_mm_aux (i+1) n m1)
  | Pf_app  (m1, m2) -> Pf_app (open_mm_in m1, open_mm_in m2)
  | Pf_inl (p, m1)        -> Pf_inl (p, open_mm_in m1)
  | Pf_inr (p, m1)        -> Pf_inr (p, open_mm_in m1)
  | Pf_case (m1, m2, m3)  -> Pf_case (open_mm_in m1,
			 	      open_mm_aux (i+1) n m2,
				      open_mm_aux (i+1) n m3)
  | Pf_not (p, m1)        -> Pf_not (p, open_mm_aux (i+1) n m1)
  | Pf_contra (m1, p, m2) -> Pf_contra (open_mm_in m1, p, open_mm_in m2)
  | Pf_unit               -> Pf_unit
  | Pf_abort (p, m1)      -> Pf_abort (p, open_mm_in m1)
  | Pf_all (h, m1)        -> Pf_all (h, open_mm_in m1)
  | Pf_inst (m1, t)       -> Pf_inst (open_mm_in m1, t)
  | Pf_pack (t, m1)       -> Pf_pack (t, open_mm_in m1)
  | Pf_unpack (h, m1, m2) -> Pf_unpack (h, open_mm_in m1, open_mm_aux (i+1) n m2)
  | Pf_let (m1, m2)       -> Pf_let (open_mm_in m1, open_mm_aux (i+1) n m2)

let open_mm = open_mm_aux 0

let rec close_mm_aux i (l:lab) m =
  let close_mm_il = close_mm_aux i l in
  match m with
  | Pf_flab k        -> if (snd k) = (snd l) then (Pf_blab i) else m
  | Pf_blab _        -> m
  | Pf_pair (m1, m2) -> Pf_pair (close_mm_il m1, close_mm_il m2)
  | Pf_fst m1        -> Pf_fst (close_mm_il m1)
  | Pf_snd m1        -> Pf_snd (close_mm_il m1)
  | Pf_abs (p, m1)   -> Pf_abs (p, close_mm_aux (i+1) l m1)
  | Pf_app  (m1, m2) -> Pf_app (close_mm_il m1, close_mm_il m2)
  | Pf_inl (p, m1)        -> Pf_inl (p, close_mm_il m1)
  | Pf_inr (p, m1)        -> Pf_inr (p, close_mm_il m1)
  | Pf_case (m1, m2, m3)  -> Pf_case (close_mm_il m1,
			 	      close_mm_aux (i+1) l m2,
				      close_mm_aux (i+1) l m3)
  | Pf_not (p, m1)        -> Pf_not (p, close_mm_aux (i+1) l m1)
  | Pf_contra (m1, p, m2) -> Pf_contra (close_mm_il m1, p, close_mm_il m2)
  | Pf_unit               -> Pf_unit
  | Pf_abort (p, m1)      -> Pf_abort (p, close_mm_il m1)
  | Pf_all (h, m1)        -> Pf_all (h, close_mm_il m1)
  | Pf_inst (m1, t)       -> Pf_inst (close_mm_il m1, t)
  | Pf_pack (t, m1)       -> Pf_pack (t, close_mm_il m1)
  | Pf_unpack (h, m1, m2) -> Pf_unpack (h, close_mm_il m1, close_mm_aux (i+1) l m2)
  | Pf_let (m1, m2)       -> Pf_let (close_mm_il m1, close_mm_aux (i+1) l m2)

let close_mm = close_mm_aux 0

let rec open_mt_aux i u m =
  let open_mt_iu = open_mt_aux i u in
  match m with
  | Pf_flab _        -> m
  | Pf_blab _        -> m
  | Pf_pair (m1, m2) -> Pf_pair (open_mt_iu m1, open_mt_iu m2)
  | Pf_fst m1        -> Pf_fst (open_mt_iu m1)
  | Pf_snd m1        -> Pf_snd (open_mt_iu m1)
  | Pf_abs (p, m1)   -> Pf_abs (open_pt_aux i u p, open_mt_iu m1)
  | Pf_app  (m1, m2) -> Pf_app (open_mt_iu m1, open_mt_iu m2)
  | Pf_inl (p, m1)        -> Pf_inl (open_pt_aux i u p, open_mt_iu m1)
  | Pf_inr (p, m1)        -> Pf_inr (open_pt_aux i u p, open_mt_iu m1)
  | Pf_case (m1, m2, m3)  -> Pf_case (open_mt_iu m1,
			 	      open_mt_iu m2,
				      open_mt_iu m3)
  | Pf_not (p, m1)        -> Pf_not (open_pt_aux i u p, open_mt_iu m1)
  | Pf_contra (m1, p, m2) -> Pf_contra (open_mt_iu m1, open_pt_aux i u p, open_mt_iu m2)
  | Pf_unit               -> Pf_unit
  | Pf_abort (p, m1)      -> Pf_abort (open_pt_aux i u p, open_mt_iu m1)
  | Pf_all (h, m1)        -> Pf_all (h, open_mt_aux (i+1) u m1)
  | Pf_inst (m1, t)       -> Pf_inst (open_mt_iu m1, open_tt_aux i u t)
  | Pf_pack (t, m1)       -> Pf_pack (open_tt_aux i u t, open_mt_iu m1)
  | Pf_unpack (h, m1, m2) -> Pf_unpack (h, open_mt_iu m1, open_mt_aux (i+1) u m2)
  | Pf_let (m1, m2)       -> Pf_let (open_mt_iu m1, open_mt_iu m2)

let open_mt = open_mt_aux 0

let rec close_mt_aux i x m =
  let close_mt_ix = close_mt_aux i x in
  match m with
  | Pf_flab _        -> m
  | Pf_blab _        -> m
  | Pf_pair (m1, m2) -> Pf_pair (close_mt_ix m1, close_mt_ix m2)
  | Pf_fst m1        -> Pf_fst (close_mt_ix m1)
  | Pf_snd m1        -> Pf_snd (close_mt_ix m1)
  | Pf_abs (p, m1)   -> Pf_abs (close_pt_aux i x p, close_mt_ix m1)
  | Pf_app  (m1, m2) -> Pf_app (close_mt_ix m1, close_mt_ix m2)
  | Pf_inl (p, m1)        -> Pf_inl (close_pt_aux i x p, close_mt_ix m1)
  | Pf_inr (p, m1)        -> Pf_inr (close_pt_aux i x p, close_mt_ix m1)
  | Pf_case (m1, m2, m3)  -> Pf_case (close_mt_ix m1,
			 	      close_mt_ix m2,
				      close_mt_ix m3)
  | Pf_not (p, m1)        -> Pf_not (close_pt_aux i x p, close_mt_ix m1)
  | Pf_contra (m1, p, m2) -> Pf_contra (close_mt_ix m1, close_pt_aux i x p, close_mt_ix m2)
  | Pf_unit               -> Pf_unit
  | Pf_abort (p, m1)      -> Pf_abort (close_pt_aux i x p, close_mt_ix m1)
  | Pf_all (h, m1)        -> Pf_all (h, close_mt_aux (i+1) x m1)
  | Pf_inst (m1, t)       -> Pf_inst (close_mt_ix m1, close_tt_aux i x t)
  | Pf_pack (t, m1)       -> Pf_pack (close_tt_aux i x t, close_mt_ix m1)
  | Pf_unpack (h, m1, m2) -> Pf_unpack (h, close_mt_ix m1, close_mt_aux (i+1) x m2)
  | Pf_let (m1, m2)       -> Pf_let (close_mt_ix m1, close_mt_ix m2)

let close_mt = close_mt_aux 0



(* NOTE: This unification stuff needs to be fixed.*)
(* It's currently very broken. *)
type un =
  | Un_top
  | Un_eq_prop of prop * prop
  | Un_eq_tm   of tm * tm
  | Un_and     of un * un
  | Un_all     of un
  | Un_ex      of un

let rec open_rt_aux i u r =
  let open_rt_iu = open_rt_aux i u in
  match r with
  | Un_top              -> Un_top
  | Un_eq_prop (p1, p2) -> Un_eq_prop (open_pt_aux i u p1, open_pt_aux i u p2)
  | Un_eq_tm (t1, t2)   -> Un_eq_tm (open_tt_aux i u t1, open_tt_aux i u t2)
  | Un_and (r1, r2)     -> Un_and (open_rt_iu r1, open_rt_iu r2)
  | Un_all r1           -> Un_all (open_rt_aux (i+1) u r1)
  | Un_ex  r1           -> Un_ex (open_rt_aux (i+1) u r1)

let open_rt = open_rt_aux 0

let rec close_rt_aux i x r =
  let close_rt_ix = close_rt_aux i x in
  match r with
  | Un_top              -> Un_top
  | Un_eq_prop (p1, p2) -> Un_eq_prop (close_pt_aux i x p1, close_pt_aux i x p2)
  | Un_eq_tm (t1, t2)   -> Un_eq_tm (close_tt_aux i x t1, close_tt_aux i x t2)
  | Un_and (r1, r2)     -> Un_and (close_rt_ix r1, close_rt_ix r2)
  | Un_all r1           -> Un_all (close_rt_aux (i+1) x r1)
  | Un_ex  r1           -> Un_ex (close_rt_aux (i+1) x r1)

let close_rt = close_rt_aux 0

(* Substitution:  [u/x]t    [u/x]p    [u/x]m  [u/x]r
   assumes that u is locally closed *)
let rec subst_tt x u t =
  match t with
  | Tm_uvar _ -> t
  | Tm_bv _ -> t
  | Tm_fv y -> if x = y then u else t
  | Tm_fun (f, ts) -> Tm_fun (f, (List.map (subst_tt x u) ts))

let rec subst_tp x u p =
  let subst_tp_xu = subst_tp x u in
  match p with
  | Prop_param _ -> p
  | Prop_pred (q, ts) -> Prop_pred (q, (List.map (subst_tt x u) ts))
  | Prop_and (p1, p2) -> Prop_and (subst_tp_xu p1, subst_tp_xu p2)
  | Prop_imp (p1, p2) -> Prop_imp (subst_tp_xu p1, subst_tp_xu p2)
  | Prop_or  (p1, p2) -> Prop_or (subst_tp_xu p1, subst_tp_xu p2)
  | Prop_not p1 -> Prop_not (subst_tp_xu p1)
  | Prop_top    -> Prop_top
  | Prop_bot    -> Prop_bot
  | Prop_all (h, p1) -> Prop_all (h, subst_tp_xu p1)
  | Prop_ex  (h, p1) -> Prop_ex  (h, subst_tp_xu p1)

let rec subst_tm x u m =
  let subst_tm_xu = subst_tm x u in
  let subst_tp_xu = subst_tp x u in 
  match m with
  | Pf_flab _        -> m
  | Pf_blab _        -> m
  | Pf_pair (m1, m2) -> Pf_pair (subst_tm_xu m1, subst_tm_xu m2)
  | Pf_fst m1        -> Pf_fst (subst_tm_xu m1)
  | Pf_snd m1        -> Pf_snd (subst_tm_xu m1)
  | Pf_abs (p, m1)   -> Pf_abs (subst_tp_xu p, subst_tm_xu m1)
  | Pf_app  (m1, m2) -> Pf_app (subst_tm_xu m1, subst_tm_xu m2)
  | Pf_inl (p, m1)        -> Pf_inl (subst_tp_xu p, subst_tm_xu m1)
  | Pf_inr (p, m1)        -> Pf_inr (subst_tp_xu p, subst_tm_xu m1)
  | Pf_case (m1, m2, m3)  -> Pf_case (subst_tm_xu m1,
			 	      subst_tm_xu m2,
				      subst_tm_xu m3)
  | Pf_not (p, m1)        -> Pf_not (subst_tp_xu p, subst_tm_xu m1)
  | Pf_contra (m1, p, m2) -> Pf_contra (subst_tm_xu m1, subst_tp_xu p, subst_tm_xu m2)
  | Pf_unit               -> Pf_unit
  | Pf_abort (p, m1)      -> Pf_abort (subst_tp_xu p, subst_tm_xu m1)
  | Pf_all (h, m1)        -> Pf_all (h, subst_tm_xu m1)
  | Pf_inst (m1, t)       -> Pf_inst (subst_tm_xu m1, t)
  | Pf_pack (t, m1)       -> Pf_pack (subst_tt x u t, subst_tm_xu m1)
  | Pf_unpack (h, m1, m2) -> Pf_unpack (h, subst_tm_xu m1, subst_tm_xu m2)
  | Pf_let (m1, m2)       -> Pf_let (subst_tm_xu m1, subst_tm_xu m2)

let rec subst_tr x u r =
  let subst_tr_xu = subst_tr x u in
  match r with
  | Un_top              -> Un_top
  | Un_eq_prop (p1, p2) -> Un_eq_prop (subst_tp x u p1, subst_tp x u p2)
  | Un_eq_tm (t1, t2)   -> Un_eq_tm (subst_tt x u t1, subst_tt x u t2)
  | Un_and (r1, r2)     -> Un_and (subst_tr_xu r1, subst_tr_xu r2)
  | Un_all r1           -> Un_all (subst_tr_xu r1)
  | Un_ex  r1           -> Un_ex (subst_tr_xu r1)


(* [q/a]p [q/a]m [q/a]r *)
let rec subst_pp a q p =
  let subst_pp_aq = subst_pp a q in
  match p with
  | Prop_param b -> if a = b then q else p
  | Prop_pred (_, _) -> p
  | Prop_and (p1, p2) -> Prop_and (subst_pp_aq p1, subst_pp_aq p2)
  | Prop_imp (p1, p2) -> Prop_imp (subst_pp_aq p1, subst_pp_aq p2)
  | Prop_or  (p1, p2) -> Prop_or (subst_pp_aq p1, subst_pp_aq p2)
  | Prop_not p1 -> Prop_not (subst_pp_aq p1)
  | Prop_top    -> Prop_top
  | Prop_bot    -> Prop_bot
  | Prop_all (h, p1) -> Prop_all (h, subst_pp_aq p1)
  | Prop_ex  (h, p1) -> Prop_ex  (h, subst_pp_aq p1)

(*-* substitute a proposition in a term *)
let rec subst_pm a q m =
  let subst_pm_aq = subst_pm a q in
  let subst_pp_aq = subst_pp a q in
  match m with
  | Pf_flab _        -> m
  | Pf_blab _        -> m
  | Pf_pair (m1, m2) -> Pf_pair (subst_pm_aq m1, subst_pm_aq m2)
  | Pf_fst m1        -> Pf_fst (subst_pm_aq m1)
  | Pf_snd m1        -> Pf_snd (subst_pm_aq m1)
  | Pf_abs (p, m1)   -> Pf_abs (subst_pp_aq p, subst_pm_aq m1)
  | Pf_app  (m1, m2) -> Pf_app (subst_pm_aq m1, subst_pm_aq m2)
  | Pf_inl (p, m1)        -> Pf_inl (subst_pp_aq p, subst_pm_aq m1)
  | Pf_inr (p, m1)        -> Pf_inr (subst_pp_aq p, subst_pm_aq m1)
  | Pf_case (m1, m2, m3)  -> Pf_case (subst_pm_aq m1,
			 	      subst_pm_aq m2,
				      subst_pm_aq m3)
  | Pf_not (p, m1)        -> Pf_not (subst_pp_aq p, subst_pm_aq m1)
  | Pf_contra (m1, p, m2) -> Pf_contra (subst_pm_aq m1, subst_pp_aq p, subst_pm_aq m2)
  | Pf_unit               -> Pf_unit
  | Pf_abort (p, m1)      -> Pf_abort (subst_pp_aq p, subst_pm_aq m1)
  | Pf_all (h, m1)        -> Pf_all (h, subst_pm_aq m1)
  | Pf_inst (m1, t)       -> Pf_inst (subst_pm_aq m1, t)
  | Pf_pack (t, m1)       -> Pf_pack (t, subst_pm_aq m1)
  | Pf_unpack (h, m1, m2)    -> Pf_unpack (h, subst_pm_aq m1, subst_pm_aq m2)
  | Pf_let (m1, m2)       -> Pf_let (subst_pm_aq m1, subst_pm_aq m2)

let rec subst_pr a q r =
  let subst_pr_aq = subst_pr a q in
  match r with
  | Un_top              -> Un_top
  | Un_eq_prop (p1, p2) -> Un_eq_prop (subst_pp a q p1, subst_pp a q p2)
  | Un_eq_tm (t1, t2)   -> Un_eq_tm (t1, t2)
  | Un_and (r1, r2)     -> Un_and (subst_pr_aq r1, subst_pr_aq r2)
  | Un_all r1           -> Un_all (subst_pr_aq r1)
  | Un_ex  r1           -> Un_ex (subst_pr_aq r1)

let rec subst_mm (l:lab) n m =
  let subst_mm_ln = subst_mm l n in
  match m with
  | Pf_flab k        -> if k = l then n else m 
  | Pf_blab _        -> m
  | Pf_pair (m1, m2) -> Pf_pair (subst_mm_ln m1, subst_mm_ln m2)
  | Pf_fst m1        -> Pf_fst (subst_mm_ln m1)
  | Pf_snd m1        -> Pf_snd (subst_mm_ln m1)
  | Pf_abs (p, m1)   -> Pf_abs (p, subst_mm_ln m1)
  | Pf_app  (m1, m2) -> Pf_app (subst_mm_ln m1, subst_mm_ln m2)
  | Pf_inl (p, m1)        -> Pf_inl (p, subst_mm_ln m1)
  | Pf_inr (p, m1)        -> Pf_inr (p, subst_mm_ln m1)
  | Pf_case (m1, m2, m3)  -> Pf_case (subst_mm_ln m1,
			 	      subst_mm_ln m2,
				      subst_mm_ln m3)
  | Pf_not (p, m1)        -> Pf_not (p, subst_mm_ln m1)
  | Pf_contra (m1, p, m2) -> Pf_contra (subst_mm_ln m1, p, subst_mm_ln m2)
  | Pf_unit               -> Pf_unit
  | Pf_abort (p, m1)      -> Pf_abort (p, subst_mm_ln m1)
  | Pf_all (h, m1)        -> Pf_all (h, subst_mm_ln m1)
  | Pf_inst (m1, t)       -> Pf_inst (subst_mm_ln m1, t)
  | Pf_pack (t, m1)       -> Pf_pack (t, subst_mm_ln m1)
  | Pf_unpack (h, m1, m2) -> Pf_unpack (h, subst_mm_ln m1, subst_mm_ln m2)
  | Pf_let (m1, m2)       -> Pf_let (subst_mm_ln m1, subst_mm_ln m2)


let rec usubst_tt c u t =
  match t with
  | Tm_uvar (_, d) -> if c = d then u else t
  | Tm_bv _ -> t
  | Tm_fv _ -> t
  | Tm_fun (f, l) -> Tm_fun (f, List.map (usubst_tt c u) l)

let rec usubst_tp c u p =
  let usubst_tp_cu = usubst_tp c u in
  match p with
  | Prop_param _ -> p
  | Prop_pred (q, ts) -> Prop_pred (q, List.map (usubst_tt c u) ts)
  | Prop_and (q1, q2) -> Prop_and (usubst_tp_cu q1, usubst_tp_cu q2) 
  | Prop_imp (q1, q2) -> Prop_imp (usubst_tp_cu q1, usubst_tp_cu q2)
  | Prop_or (q1, q2)  -> Prop_or (usubst_tp_cu q1, usubst_tp_cu q2)
  | Prop_not q1       -> Prop_not (usubst_tp_cu q1)
  | Prop_top          -> Prop_top
  | Prop_bot          -> Prop_bot
  | Prop_all (h, q1)  -> Prop_all (h, usubst_tp_cu q1)
  | Prop_ex (h, q1)   -> Prop_ex (h, usubst_tp_cu q1)

let rec usubst_tm c u m =
  let usubst_tm_cu = usubst_tm c u in
  match m with
  | Pf_flab _        -> m
  | Pf_blab _        -> m
  | Pf_pair (m1, m2) -> Pf_pair (usubst_tm_cu m1, usubst_tm_cu m2)
  | Pf_fst m1        -> Pf_fst (usubst_tm_cu m1)
  | Pf_snd m1        -> Pf_snd (usubst_tm_cu m1)
  | Pf_abs (p, m1)   -> Pf_abs (usubst_tp c u p, usubst_tm_cu m1)
  | Pf_app  (m1, m2) -> Pf_app (usubst_tm_cu m1, usubst_tm_cu m2)
  | Pf_inl (p, m1)        -> Pf_inl (usubst_tp c u p, usubst_tm_cu m1)
  | Pf_inr (p, m1)        -> Pf_inr (usubst_tp c u p, usubst_tm_cu m1)
  | Pf_case (m1, m2, m3)  -> Pf_case (usubst_tm_cu m1,
			 	      usubst_tm_cu m2,
				      usubst_tm_cu m3)
  | Pf_not (p, m1)        -> Pf_not (usubst_tp c u p, usubst_tm_cu m1)
  | Pf_contra (m1, p, m2) -> Pf_contra (usubst_tm_cu m1, usubst_tp c u p, usubst_tm_cu m2)
  | Pf_unit               -> Pf_unit
  | Pf_abort (p, m1)      -> Pf_abort (usubst_tp c u p, usubst_tm_cu m1)
  | Pf_all (h, m1)        -> Pf_all (h, usubst_tm_cu m1)
  | Pf_inst (m1, t)       -> Pf_inst (usubst_tm_cu m1, t)
  | Pf_pack (t, m1)       -> Pf_pack (usubst_tt c u t, usubst_tm_cu m1)
  | Pf_unpack (h, m1, m2) -> Pf_unpack (h, usubst_tm_cu m1, usubst_tm_cu m2)
  | Pf_let (m1, m2)       -> Pf_let (usubst_tm_cu m1, usubst_tm_cu m2)

let rec usubst_tr c u r = 
  let usubst_tr_cu = usubst_tr c u in
  match r with
  | Un_top              -> Un_top
  | Un_eq_prop (p1, p2) -> Un_eq_prop (usubst_tp c u p1, usubst_tp c u p2)
  | Un_eq_tm (t1, t2)   -> Un_eq_tm (usubst_tt c u t1, usubst_tt c u t2)
  | Un_and (r1, r2)     -> Un_and (usubst_tr_cu r1, usubst_tr_cu r2)
  | Un_all r1           -> Un_all (usubst_tr_cu r1)
  | Un_ex  r1           -> Un_ex (usubst_tr_cu r1)

