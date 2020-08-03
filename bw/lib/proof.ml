module type S = sig
  open Proof_rep
  open Prop_rep
  open Tm_rep

  val pr_var : int -> proof

  val pr_p_one : unit -> proof

  val pr_p_inL : proof -> pprop -> proof

  val pr_p_inR : pprop -> proof -> proof

  val pr_p_case : proof -> proof -> proof -> proof

  val pr_p_sigpair : pprop -> tm -> proof -> proof

  val pr_p_sigmatch : proof -> proof -> proof

  val pr_p_shift : proof -> proof

  val pr_n_top : unit -> proof

  val pr_n_pair : proof -> proof -> proof

  val pr_n_projL : proof -> proof -> proof

  val pr_n_projR : proof -> proof -> proof

  val pr_n_abs : pprop -> proof -> proof

  val pr_n_app : proof -> proof -> proof -> proof

  val pr_n_piabs : proof -> proof

  val pr_n_piapp : proof -> tm -> proof -> proof

  val pr_n_shift : proof -> proof

  type context_item = Term | Prop of prop

  type context = context_item list

  val empty_context : context

  (* these functions return `None` if the index is invalid in the provided context
     else they return the type of that index, along with the offset for that item's
     context *)
  (* val nth_prop : context -> int -> (prop * context) option *)
  (* val nth_term : context -> int -> context option *)

  val infer_type : context -> proof -> prop option
end

module Make (G : Globals.T) (TMS : Tm.S) (PRPS : Prop.S) = (* : S *) struct
  open Proof_rep
  open Prop_rep
  open Tm_rep
  open List

  let pr_var (i : int) = Globals.HProof.hashcons G.proof_table (Pr_var i)

  let pr_p_one () = Globals.HProof.hashcons G.proof_table Pr_p_one

  let pr_p_inL pr_l pp_r =
    Globals.HProof.hashcons G.proof_table (Pr_p_inL (pr_l, pp_r))

  let pr_p_inR pp_l pr_r =
    Globals.HProof.hashcons G.proof_table (Pr_p_inR (pp_l, pr_r))

  let pr_p_case pr_disj pr_then pr_else =
    Globals.HProof.hashcons G.proof_table
      (Pr_p_case (pr_disj, pr_then, pr_else))

  let pr_p_sigpair pp tm_witness pr =
    Globals.HProof.hashcons G.proof_table (Pr_p_sigpair (pp, tm_witness, pr))

  let pr_p_sigmatch pr_existential pr_cont =
    Globals.HProof.hashcons G.proof_table
      (Pr_p_sigmatch (pr_existential, pr_cont))

  let pr_p_shift pr = Globals.HProof.hashcons G.proof_table (Pr_p_shift pr)

  let pr_n_top () = Globals.HProof.hashcons G.proof_table Pr_n_top

  let pr_n_pair pr_l pr_r =
    Globals.HProof.hashcons G.proof_table (Pr_n_pair (pr_l, pr_r))

  let pr_n_projL pr_conj pr_cont =
    Globals.HProof.hashcons G.proof_table (Pr_n_projL (pr_conj, pr_cont))

  let pr_n_projR pr_conj pr_cont =
    Globals.HProof.hashcons G.proof_table (Pr_n_projR (pr_conj, pr_cont))

  let pr_n_abs pp_arg pr_body =
    Globals.HProof.hashcons G.proof_table (Pr_n_abs (pp_arg, pr_body))

  let pr_n_app pr_abs pr_arg pr_cont =
    Globals.HProof.hashcons G.proof_table (Pr_n_app (pr_abs, pr_arg, pr_cont))

  let pr_n_piabs pr_body =
    Globals.HProof.hashcons G.proof_table (Pr_n_piabs pr_body)

  let pr_n_piapp pr_piabs tm_arg pr_cont =
    Globals.HProof.hashcons G.proof_table
      (Pr_n_piapp (pr_piabs, tm_arg, pr_cont))

  let pr_n_shift pr = Globals.HProof.hashcons G.proof_table (Pr_n_shift pr)

  type context_item = Term | Prop of prop

  type context = context_item list

  let empty_context = []

  let rec pprop_replace_terms (f : int -> tm -> tm) (p : pprop) (d : int) :
      pprop =
    match p.node with
    | P_one -> PRPS.p_one ()
    | P_zero -> PRPS.p_zero ()
    | P_or (p1, p2) ->
        PRPS.p_or (pprop_replace_terms f p1 d) (pprop_replace_terms f p2 d)
    | P_ex p -> PRPS.p_ex (pprop_replace_terms f p (d + 1))
    | P_shift p -> PRPS.p_shift (nprop_replace_terms f p d)

  and nprop_replace_terms (f : int -> tm -> tm) (p : nprop) (d : int) : nprop =
    match p.node with
    | N_prop (tag, tms) ->
        let tms' = map (fun tm -> f d tm) tms in
        PRPS.n_prop tag tms'
    | N_top -> PRPS.n_top ()
    | N_and (p1, p2) ->
        PRPS.n_and (nprop_replace_terms f p1 d) (nprop_replace_terms f p2 d)
    | N_imp (p1, p2) ->
        PRPS.n_imp (pprop_replace_terms f p1 d) (nprop_replace_terms f p2 d)
    | N_all p -> PRPS.n_all (nprop_replace_terms f p (d + 1))
    | N_shift p -> PRPS.n_shift (pprop_replace_terms f p d)

  (* this replaces free variable `i` with `t` and decrememnts other variable indices as appropriate *)
  let prop_replace_terms (f : int -> tm -> tm) (p : prop) (d : int) : prop =
    match p with
    | Pos p' -> Pos (pprop_replace_terms f p' d)
    | Neg p' -> Neg (nprop_replace_terms f p' d)

  let rec term_replace_uvars (f : int -> tm) (t : tm) : tm =
    match t.node with
    | Tm_uvar i -> f i
    | Tm_param tag -> TMS.tm_param tag
    | Tm_fun (tag, tms) -> TMS.tm_fun tag (map (term_replace_uvars f) tms)

  (* this is sortof the reverse of `subst_for_free_var`, in that it will increment variable indices
   * except that this will do it multiple (n) times. in particular, dooing `n` substitutions on the same
   * index `i`, followed by this function, should result in the original term, with substitutions, but
   * *without* changing the indices of any other variables *)
  let add_free_term_vars (first_idx_to_incr : int) (incr_count : int) : tm -> tm
      =
    term_replace_uvars (fun (leaf_idx : int) ->
        if leaf_idx < first_idx_to_incr then TMS.tm_uvar leaf_idx
        else TMS.tm_uvar (leaf_idx + incr_count))

  let subst_for_free_term_var (p : prop) (t : tm) (idx_to_replace : int) : prop
      =
    let f (depth : int) (leaf_idx : int) : tm =
      let idx_to_replace_adjusted = idx_to_replace + depth in
      if leaf_idx = idx_to_replace_adjusted then
        (* do the substitution: we mangle the variables in t to account for how many binders deep we are, then we return it *)
        add_free_term_vars 0 depth t
      else if leaf_idx < idx_to_replace_adjusted then
        (* this variable refers to an index lower than the one we're replacing, so it is unaffected *)
        TMS.tm_uvar leaf_idx
      else
        (* this variable refers to an index higher than the one we're replacing, so we have to shift it down one *)
        TMS.tm_uvar (leaf_idx - 1)
    in

    prop_replace_terms (fun (depth : int) -> term_replace_uvars (f depth)) p 0

  (* gets the nth prop from the context, if it exists, and ajusts its de Brujin indicies to be valid in the current context *)
  type _get_mangled_var_state = {
    term_count : int;
    prop_count : int;
    found : prop option;
  }

  let get_mangled_var (gamma : context) (n : int) : prop option =
    let f (state : _get_mangled_var_state) (item : context_item) =
      match (state.found = None, item) with
      | false, _ -> state
      | true, Term -> { state with term_count = state.term_count + 1 }
      | true, Prop p ->
          {
            state with
            prop_count = state.prop_count + 1;
            found = (if state.prop_count = n then Some p else None);
          }
    in
    match
      fold_left f { term_count = 0; prop_count = 0; found = None } gamma
    with
    (* when we return the prop from the context, we need to adjust the term variable indices in it to account for the
     * additional items in the context. however we only adjust those variables that are free, which is why we only
     * change those with index >= depth *)
    | { found = Some p; term_count; _ } ->
        Some
          (prop_replace_terms
             (fun depth -> add_free_term_vars depth term_count)
             p 0)
    | _ -> None

  let rec infer_type gamma (proof : proof) =
    match proof.node with
    | Pr_var i -> get_mangled_var gamma i
    | Pr_p_one -> Some (Pos (PRPS.p_one ()))
    | Pr_p_inL (t1, p2) -> (
        match infer_type gamma t1 with
        | Some (Pos p1') -> Some (Pos (PRPS.p_or p1' p2))
        | _ -> None )
    | Pr_p_inR (p1, t2) -> (
        match infer_type gamma t2 with
        | Some (Pos p2') -> Some (Pos (PRPS.p_or p1 p2'))
        | _ -> None )
    | Pr_p_case (c, t1, t2) -> (
        match infer_type gamma c with
        | Some (Pos { node = P_or (q1, q2); _ }) ->
            let p1 = infer_type (Prop (Pos q1) :: gamma) t1 in
            let p2 = infer_type (Prop (Pos q2) :: gamma) t2 in
            if p1 = p2 then p1 else None
        | _ -> None )
    | Pr_p_shift t -> (
        match infer_type gamma t with
        | Some (Neg p) -> Some (Pos (PRPS.p_shift p))
        | _ -> None )
    | Pr_n_top -> Some (Neg (PRPS.n_top ()))
    | Pr_n_pair (t1, t2) -> (
        match (infer_type gamma t1, infer_type gamma t2) with
        | Some (Neg p1), Some (Neg p2) -> Some (Neg (PRPS.n_and p1 p2))
        | _ -> None )
    | Pr_n_projL (p, c) -> (
        match infer_type gamma p with
        | Some (Neg { node = N_and (p1, _); _ }) ->
            infer_type (Prop (Neg p1) :: gamma) c
        | _ -> None )
    | Pr_n_projR (p, c) -> (
        match infer_type gamma p with
        | Some (Neg { node = N_and (_, p2); _ }) ->
            infer_type (Prop (Neg p2) :: gamma) c
        | _ -> None )
    | Pr_n_abs (q, t) -> infer_type (Prop (Pos q) :: gamma) t
    (*
      G |- t1 : P     G, q : Q |- t2 : T
      -------------------------------------
      G', f : P -> Q |- T_N_app (var f) t1 t2 : T
     *)
    | Pr_n_app (f, x, c) -> (
        let pf = infer_type gamma f in
        let px = infer_type gamma x in
        match (pf, px) with
        | Some (Neg { node = N_imp (pf1, pf2); _ }), Some (Pos px') ->
            if px' = pf1 then infer_type (Prop (Neg pf2) :: gamma) c else None
        | _ -> None )
    | Pr_n_shift t -> (
        match infer_type gamma t with
        | Some (Pos p) -> Some (Neg (PRPS.n_shift p))
        | _ -> None )
    | Pr_p_sigpair (p, x, t) ->
        if Some (subst_for_free_term_var (Pos p) x 0) = infer_type gamma t then
          Some (Pos (PRPS.p_ex p))
        else None
    | Pr_p_sigmatch (ex, t) -> (
        match infer_type gamma ex with
        (* we don't need to mangle the indices in `p`, since while part of `P_ex p`, term index 0
         * referred to the thing that was existentially quantified, and now because of the positions
         * in the context, 0 will refer to the new term variable *)
        | Some (Pos { node = P_ex p; _ }) ->
            infer_type (Prop (Pos p) :: Term :: gamma) t
        | _ -> None )
    | Pr_n_piabs t -> infer_type (Term :: gamma) t
    | Pr_n_piapp (f, x, c) -> (
        let pf = infer_type gamma f in
        match pf with
        | Some (Neg { node = N_all pf'; _ }) ->
            let pf'' = subst_for_free_term_var (Neg pf') x 0 in
            infer_type (Prop pf'' :: gamma) c
        | _ -> None )
end
