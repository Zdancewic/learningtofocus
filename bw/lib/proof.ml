module type S = sig
  open Proof_rep
  open Proof_rep.ProofRep
  open Proof_rep.ValueRep
  open Proof_rep.StackRep
  open Prop_rep
  type ppat = int Proof_rep.ppat
  type npat = int Proof_rep.npat

  val pat_p_unit : ppat
  val pat_p_inj : tag -> ppat -> ppat
  val pat_p_sigpair : ppat -> ppat
  val pat_p_var : int -> ppat

  val pat_n_proj : tag -> npat -> npat
  val pat_n_app : ppat -> npat -> npat
  val pat_n_piapp : npat -> npat
  val pat_n_covar : npat

  val pr_p_match  : (ppat -> proof) -> proof (* pattern match on the next variable *)
  val pr_n_match  : (npat -> proof) -> proof (* co-pattern matching i.e. lambda or matching on the current stack *)
  val pr_p_rfoc   : value -> proof
  val pr_n_lfoc   : int -> stack -> proof

  val check       : (int * nprop) list -> pprop list -> proof -> nprop -> bool
  val check_value : (int * nprop) list -> pprop list -> value -> pprop -> bool
  val check_stack : (int * nprop) list -> pprop list -> stack -> nprop -> nprop -> bool
end

module Make (G : Globals.T) (TMS : Tm.S) (PRPS : Prop.S) : S = struct
  open Proof_rep.ProofRep
  open Proof_rep.ValueRep
  open Proof_rep.StackRep
  open Prop_rep
  open List
  module PPatRep = Proof_rep.PPatRep
  module NPatRep = Proof_rep.NPatRep
  type ppat = int Proof_rep.ppat
  type npat = int Proof_rep.npat

  let pat_p_unit : ppat = Globals.PPat.hashcons G.ppat_table Pat_p_unit
  let pat_p_inj tag ppat : ppat = Globals.PPat.hashcons G.ppat_table (Pat_p_inj (tag, ppat))
  let pat_p_sigpair ppat : ppat = Globals.PPat.hashcons G.ppat_table (Pat_p_sigpair ppat)
  let pat_p_var v : ppat = Globals.PPat.hashcons G.ppat_table (Pat_p_var v)

  let pat_n_proj tag npat : npat = Globals.NPat.hashcons G.npat_table (Pat_n_proj (tag, npat))
  let pat_n_app ppat npat : npat = Globals.NPat.hashcons G.npat_table (Pat_n_app (ppat, npat))
  let pat_n_piapp npat : npat = Globals.NPat.hashcons G.npat_table (Pat_n_piapp npat)
  let pat_n_covar : npat = Globals.NPat.hashcons G.npat_table Pat_n_covar

  let pr_p_match body : proof = Globals.HProof.hashcons G.proof_table (Pr_p_match body)
  let pr_n_match body : proof = Globals.HProof.hashcons G.proof_table (Pr_n_match body)
  let pr_p_rfoc value : proof = Globals.HProof.hashcons G.proof_table (Pr_p_rfoc value)
  let pr_n_lfoc var stack : proof = Globals.HProof.hashcons G.proof_table (Pr_n_lfoc (var, stack))

  let pr_value subst tms ppat = Globals.PValue.hashcons G.value_table (Pr_value (subst, tms, ppat))
  let pr_stack subst tms k npat = Globals.NStack.hashcons G.stack_table (Pr_stack (subst, tms, k, npat))

  type ppat_rec = {
    pat : ppat;
    vars : (int * nprop) list
  }
  type ppat_set = ppat_rec list

  type npat_rec = {
    pat : npat;
    (* types of variables in the pattern *)
    vars : (int * nprop) list;
    (* type of the output *)
    out : nprop;
  }
  type npat_set = npat_rec list

  (** Generate all the fully-expanded patterns that can match against the given proposition. *)
  let rec pat_for_p (prop : pprop) (fresh : unit -> 'a) : ppat_set =
    match prop.node with
    | P_one -> [{pat = pat_p_unit; vars = []}]
    | P_zero -> []
    | P_or (prop1, prop2) ->
      let inl = List.map (fun ({pat; vars} : ppat_rec) -> {pat = pat_p_inj Proof_rep.Left pat; vars}) (pat_for_p prop1 fresh) in
      let inr = List.map (fun ({pat; vars} : ppat_rec) -> {pat = pat_p_inj Proof_rep.Right pat; vars}) (pat_for_p prop2 fresh) in
      inl @ inr
    | P_ex prop' ->
      List.map (fun ({pat; vars} : ppat_rec) -> {pat = pat_p_sigpair pat; vars}) (pat_for_p prop' fresh)
    | P_shift nprop ->
      let v = fresh () in
      [{pat = pat_p_var v; vars = [(v, nprop)]}]

  (** Generate all the fully-expanded co-patterns that can match against the given proposition. *)
  let rec pat_for_n (prop: nprop) (fresh : unit -> 'a) : npat_set =
    match prop.node with
    | N_prop (_, _) -> [{ pat = pat_n_covar; vars = []; out = prop }]
    | N_top -> []
    | N_and (prop1, prop2) ->
      let projl = List.map (fun {pat; vars; out} ->
                              { pat = pat_n_proj Proof_rep.Left pat;
                                vars; out })
                           (pat_for_n prop1 fresh)
      in
      let projr = List.map (fun {pat; vars; out} ->
                              { pat = pat_n_proj Proof_rep.Right pat;
                                vars; out })
                           (pat_for_n prop2 fresh) in
      projl @ projr
    | N_imp (pprop, nprop) ->
      let ppats = pat_for_p pprop fresh in
      let npats = pat_for_n nprop fresh in
      List.concat_map (fun ({pat = ppat; vars = vars1} : ppat_rec) ->
        List.map (fun {pat = npat; vars = vars2; out} -> { pat = pat_n_app ppat npat; vars = vars1 @ vars2; out })
                 npats)
        ppats
    | N_all prop' ->
      List.map (fun {pat; vars; out} -> {pat = pat_n_piapp pat; vars; out}) (pat_for_n prop' fresh)
    | N_shift _ ->
      [{pat = pat_n_covar; vars = []; out = prop}]

  let rec check (stable_env : (int * nprop) list) (env : pprop list) (proof : proof)  (nprop : nprop) : bool =
    (* TODO how to we avoid clashing wth free variables already in proof???? *)
    let counter = ref 0 in
    let fresh = (fun () -> let name = !counter in counter := name + 1; name) in
    match proof.node, env, nprop.node with
    | Pr_p_match body, pprop :: env', _ ->
      List.for_all (fun ({pat; vars} : ppat_rec) -> check (vars @ stable_env) env' (body pat) nprop) (pat_for_p pprop fresh)
    | Pr_n_match body, _, _ ->
      List.for_all (fun ({pat; vars; out} : npat_rec) -> check (vars @ stable_env) env (body pat) out) (pat_for_n nprop fresh)
    | Pr_p_rfoc value, _, N_shift pprop ->
      check_value stable_env env value  pprop
    | Pr_n_lfoc (v, stack), _, _ ->
      check_stack stable_env env stack (List.assoc v stable_env) nprop
    | _, _, _ -> false

and check_value (stable_env : (int * nprop) list) (env : pprop list) (value : value)  (pprop : pprop) : bool =
  match value.node, pprop.node with
  | Pr_value (_, _, {node = Pat_p_unit; _}), P_one -> true
  | Pr_value (subst, tms, {node = Pat_p_inj (tag, ppat); _}), P_or (pprop1, pprop2) ->
    let value' = pr_value subst tms ppat in
    begin match tag with
      | Left -> check_value stable_env env value' pprop1
      | Right -> check_value stable_env env value' pprop2
    end
  | Pr_value (subst, tm::tms, {node = Pat_p_sigpair ppat; _}), P_ex pprop_body ->
    let value' = pr_value subst tms ppat in
    let pprop' = PRPS.open_pt tm pprop_body in
    check_value stable_env env value' pprop'
  | Pr_value (subst, _, {node = Pat_p_var v; _}), P_shift nprop ->
    check stable_env env (subst v) nprop ||
    NPropRep.equal (List.assoc v stable_env).node nprop.node
  | _, _ -> false

and check_stack (stable_env : (int * nprop) list) (env : pprop list) (stack : stack) (nprop_hole : nprop) (nprop_ret : nprop) : bool =
  match stack.node, nprop_hole.node, nprop_ret.node with
  | Pr_stack (_, [], None, {node = Pat_n_covar; _}), N_prop (_, _), N_prop (_, _) ->
    NPropRep.equal nprop_hole.node nprop_ret.node
  | Pr_stack (subst_p, tms, subst_n, {node = Pat_n_proj (tag, npat); _}), N_and (nprop_l, nprop_r), _ ->
    let stack' = pr_stack subst_p tms subst_n npat in
    begin match tag with
      | Left ->  check_stack stable_env env stack' nprop_l nprop_ret
      | Right -> check_stack stable_env env stack' nprop_r nprop_ret
    end
  | Pr_stack (subst_p, tms, subst_n, {node = Pat_n_app (ppat, npat); _}), N_imp (pprop, nprop), _ ->
    let stack' = pr_stack subst_p tms subst_n npat in
    let value = pr_value subst_p tms ppat in
    check_value stable_env env value pprop &&
    check_stack stable_env env stack' nprop nprop_ret
  | Pr_stack (subst_p, tm::tms, subst_n, {node = Pat_n_piapp npat; _}), N_all nprop, _ ->
    let stack' = pr_stack subst_p tms subst_n npat in
    let nprop_hole' = PRPS.open_nt tm nprop in
    check_stack stable_env env stack' nprop_hole' nprop_ret
  | Pr_stack (_, [], Some k, {node = Pat_n_covar; _}), N_shift pprop, _ ->
    check stable_env (pprop :: env) k nprop_ret
  | _, _, _ -> false
end
