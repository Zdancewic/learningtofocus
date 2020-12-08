module type S = sig
  open Proof_rep
  open Proof_rep.ProofRep
  open Proof_rep.ValueRep
  open Proof_rep.StackRep
  open Prop_rep
  open Tm_rep
  type ppat = Top.tag Proof_rep.ppat
  type npat = Top.tag Proof_rep.npat
  type stable_env = (int * nprop) list

  val pat_p_unit : ppat
  val pat_p_inj : tag -> ppat -> ppat
  val pat_p_sigpair : ppat -> ppat
  val pat_p_bvar : int -> ppat

  val pat_n_proj : tag -> npat -> npat
  val pat_n_app : ppat -> npat -> npat
  val pat_n_piapp : npat -> npat
  val pat_n_covar : npat

  val pr_p_match  : (ppat -> proof) -> proof (* pattern match on the next variable *)
  val pr_n_match  : (npat -> proof) -> proof (* co-pattern matching i.e. lambda or matching on the current stack *)
  val pr_p_rfoc   : value -> proof
  val pr_n_lfoc   : Top.tag Proof_rep.var -> stack -> proof
  val pr_ex_falso : proof
  val pr_bvar     : int -> proof

  val pr_value : proof list -> tm list -> ppat -> value

  val pr_value_unit : value
  val pr_value_shift : proof -> value

  val pr_stack_app : value -> stack -> stack
  val pr_stack_proj : tag -> stack -> stack
  val pr_stack_projL : stack -> stack
  val pr_stack_projR : stack -> stack
  val pr_stack_covar : stack
  val pr_stack_shift : proof -> stack

  val check       : stable_env -> pprop list -> proof -> nprop -> bool
  val check_value : stable_env -> pprop list -> value -> pprop -> bool
  val check_stack : stable_env -> pprop list -> stack -> nprop -> nprop -> bool
end

module Make (G : Globals.T) (TMS : Tm.S) (PROP : Prop.S) : S = struct
  open Util.Hashcons
  open Proof_rep.ProofRep
  open Proof_rep.ValueRep
  open Proof_rep.StackRep
  open Prop_rep
  open Tm_rep
  open List
  module PPatRep = Proof_rep.PPatRep
  module NPatRep = Proof_rep.NPatRep
  type ppat = Top.tag Proof_rep.ppat
  type npat = Top.tag Proof_rep.npat
  type stable_env = (int * nprop) list


  let rec buildList f n = if n > 0 then f n :: (buildList f (n - 1)) else []


  let pat_p_unit : ppat = Globals.PPat.hashcons G.ppat_table Pat_p_unit
  let pat_p_inj tag ppat : ppat = Globals.PPat.hashcons G.ppat_table (Pat_p_inj (tag, ppat))
  let pat_p_sigpair ppat : ppat = Globals.PPat.hashcons G.ppat_table (Pat_p_sigpair ppat)
  let pat_p_bvar i : ppat = Globals.PPat.hashcons G.ppat_table (Pat_p_bvar i)

  let pat_n_proj tag npat : npat = Globals.NPat.hashcons G.npat_table (Pat_n_proj (tag, npat))
  let pat_n_app ppat npat : npat = Globals.NPat.hashcons G.npat_table (Pat_n_app (ppat, npat))
  let pat_n_piapp npat : npat = Globals.NPat.hashcons G.npat_table (Pat_n_piapp npat)
  let pat_n_covar : npat = Globals.NPat.hashcons G.npat_table Pat_n_covar

  let pr_p_match body : proof = Globals.HProof.hashcons G.proof_table (Pr_p_match body)
  let pr_n_match body : proof = Globals.HProof.hashcons G.proof_table (Pr_n_match body)
  let pr_p_rfoc value : proof = Globals.HProof.hashcons G.proof_table (Pr_p_rfoc value)
  let pr_n_lfoc var stack : proof = Globals.HProof.hashcons G.proof_table (Pr_n_lfoc (var, stack))
  let pr_ex_falso : proof = pr_p_match (fun _ -> failwith "absurd")

  let pr_value subst tms ppat = Globals.PValue.hashcons G.value_table (Pr_value (subst, tms, ppat))


  let pr_stack subst tms k npat = Globals.NStack.hashcons G.stack_table (Pr_stack (subst, tms, k, npat))


  type ppat_rec = {
    pat : ppat;
    (* free term variables bound in the pattern & present in the types in vars *)
    tms : Top.tag list;
    (* types of variables in the pattern *)
    vars : nprop list
  }
  type ppat_set = ppat_rec list

  type npat_rec = {
    pat : npat;
    (* free term variables bound in the pattern & present in the types in vars *)
    tms : Top.tag list;
    (* types of variables in the pattern *)
    vars : nprop list;
    (* type of the output *)
    out : nprop;
  }
  type npat_set = npat_rec list

  (** Generate all the fully-expanded patterns that can match against the given proposition. *)
  let rec pat_for_p (prop : pprop) : (ppat_set) =
      match prop.node with
      | P_one -> [{pat = pat_p_unit; tms = []; vars = []}]
      | P_zero -> []
      | P_or (prop1, prop2) ->
        let inl = List.map (fun ({pat; tms; vars} : ppat_rec) -> {pat = pat_p_inj Proof_rep.Left pat; tms; vars}) (pat_for_p prop1) in
        let inr = List.map (fun ({pat; tms; vars} : ppat_rec) -> {pat = pat_p_inj Proof_rep.Right pat; tms; vars}) (pat_for_p prop2) in
        inl @ inr
      | P_ex prop' ->
        let t = G.gen_tag () in
        let prop'' = PROP.open_pt (TMS.tm_param t) prop' in
        List.map (fun ({pat; tms; vars} : ppat_rec) ->
          {pat = pat_p_sigpair pat; tms = t :: tms; vars}) (pat_for_p prop'')
      | P_shift nprop ->
        [{pat = pat_p_bvar 0; tms = []; vars = [nprop]}]

  (** Generate all the fully-expanded co-patterns that can match against the given proposition. *)
  let rec pat_for_n (prop: nprop) : npat_set =
    match prop.node with
    | N_prop (_, _) -> [{ pat = pat_n_covar; tms = []; vars = []; out = prop }]
    | N_top -> []
    | N_and (prop1, prop2) ->
      let projl = List.map (fun {pat; tms; vars; out} ->
                              { pat = pat_n_proj Proof_rep.Left pat;
                                tms; vars; out })
                           (pat_for_n prop1)
      in
      let projr = List.map (fun {pat; tms; vars; out} ->
                              { pat = pat_n_proj Proof_rep.Right pat;
                                tms; vars; out })
                           (pat_for_n prop2) in
      projl @ projr
    | N_imp (pprop, nprop) ->
      let ppats = pat_for_p pprop in
      let npats = pat_for_n nprop in
      List.concat_map (fun ({pat = ppat; tms = tms1; vars = vars1} : ppat_rec) ->
        List.map (fun {pat = npat; tms = tms2; vars = vars2; out} -> { pat = pat_n_app ppat npat; tms = tms1 @ tms2; vars = vars1 @ vars2; out })
                 npats)
        ppats
    | N_all prop' ->
      let t = G.gen_tag () in
      let prop'' = PROP.open_nt (TMS.tm_param t) prop' in
      List.map (fun {pat; tms; vars; out} -> {pat = pat_n_piapp pat; tms = t :: tms; vars; out}) (pat_for_n prop'')
    | N_shift _ ->
      [{pat = pat_n_covar; tms = []; vars = []; out = prop}]

  let (<+>) (tm1, pf1) (tm2, pf2) = (tm1 + tm2, pf1 + pf2)

  (** Take a binding pattern and count the number of (term, proof) variables it binds. *)
  let rec count_binders_ppat (ppat : ppat) : int * int =
    match ppat.node with
    | Pat_p_unit -> (0, 0)
    | Pat_p_inj (_, ppat') ->
      count_binders_ppat ppat'
    | Pat_p_sigpair ppat' -> (1, 0) <+> count_binders_ppat ppat'
    | Pat_p_bvar 0 -> (0, 1)
    | _ -> failwith "unexpected pattern"

  let rec count_binders_npat (npat : npat) : int * int  =
    match npat.node with
    | Pat_n_proj (_, npat') ->
      count_binders_npat npat'
    | Pat_n_app (ppat, npat') ->
      count_binders_ppat ppat <+> count_binders_npat npat'
    | Pat_n_piapp npat' ->
      (1, 0) <+> count_binders_npat npat'
    | Pat_n_covar -> (0, 0)

  let rec open_ppat (tms_ren : int list) (ren : ppat list) (ppat : ppat) : ppat =
    match ppat.node with
    | Pat_p_unit -> pat_p_unit
    | Pat_p_inj (tag, ppat') ->
      pat_p_inj tag (open_ppat tms_ren ren ppat')
    | Pat_p_sigpair ppat' ->
      let tms_ren' = List.map (fun i -> i + 1) tms_ren in
      pat_p_sigpair (open_ppat (0::tms_ren') ren ppat')
    | Pat_p_bvar i -> List.nth ren i
    (* | _ -> failwith "unexpected pattern" *)

  let rec open_npat (tms_ren : int list) (ren : ppat list) (npat : npat) : npat =
    match npat.node with
    | Pat_n_proj (tag, npat') ->
      pat_n_proj tag (open_npat tms_ren ren npat')
    | Pat_n_app (ppat, npat') ->
      pat_n_app (open_ppat tms_ren ren ppat) (open_npat tms_ren ren npat')
    | Pat_n_piapp npat' ->
      let tms_ren' =  List.map (fun i -> i + 1) tms_ren in
      pat_n_piapp (open_npat (0::tms_ren') ren npat')
    | Pat_n_covar -> pat_n_covar



  (** Rename bound variable i to ren[i] in proof *)
  let rec open_proof (tms_ren : tm list) (ren : 'a Proof_rep.var list) (proof : proof) : proof =
    match proof.node with
    | Pr_p_match body ->
       pr_p_match (fun ppat_new ->
         let (tm_binders, proof_binders) = (count_binders_ppat ppat_new) in
         let tms_ren_new = buildList (fun i -> TMS.tm_uvar i) tm_binders in
         let ren_new = buildList (fun i -> Proof_rep.Bound i) proof_binders in
         let proof' = body ppat_new in
         open_proof (tms_ren_new @ tms_ren) (ren_new @ ren) proof')
    | Pr_n_match body ->
       pr_n_match (fun npat_new ->
         let (tm_binders, proof_binders) = count_binders_npat npat_new in
         let tms_ren_new = buildList (fun i -> TMS.tm_uvar i) tm_binders in
         let ren_new = buildList (fun i -> Proof_rep.Bound i) proof_binders in
         let proof' = body npat_new in
         open_proof (tms_ren_new @ tms_ren) (ren_new @ ren) proof')
    | Pr_p_rfoc value ->
      let value' = open_value tms_ren ren value in
      pr_p_rfoc value'
    | Pr_n_lfoc (Proof_rep.Bound i, stack) ->
      let v = List.nth ren i in
      let stack' = open_stack tms_ren ren stack in
      pr_n_lfoc v stack'
    | Pr_n_lfoc (v, stack) ->
      pr_n_lfoc v (open_stack tms_ren ren stack)

  and open_value (tms_ren : tm list) (ren : 'a Proof_rep.var list) (value : value) : value =
     let Pr_value (subst, tms, ppat) = value.node in
     let subst' = open_subst tms_ren ren subst in
     let tms' = List.map (TMS.mopen_tt tms_ren) tms in
     pr_value subst' tms' ppat

  and open_stack (tms_ren : tm list) (ren : 'a Proof_rep.var list) (stack : stack) : stack =
    let Pr_stack (subst, tms, k, npat) = stack.node in
    let subst' = open_subst tms_ren ren subst in
    let tms' = List.map (TMS.mopen_tt tms_ren) tms in
    let k' = open_cont tms_ren ren k in
    pr_stack subst' tms' k' npat

  and open_subst (tms_ren : tm list) (ren : 'a Proof_rep.var list) : proof list -> proof list =
    List.map (open_proof tms_ren ren)

  and open_cont (tms_ren : tm list) (ren : 'a Proof_rep.var list) : proof option -> proof option =
    Option.map (open_proof tms_ren ren)


  let fail_check s =
    Printf.printf "%s\n" s;
    false

  let rec check (stable_env : (Top.tag * nprop) list) (env : pprop list) (proof : proof)  (nprop : nprop) : bool =
    match proof.node, env, nprop.node with
    | Pr_p_match body, pprop :: env', _ ->
      List.for_all (fun ({pat; tms; vars} : ppat_rec) ->
        let stable_env' = List.map (fun npropx -> (G.gen_tag (), npropx)) vars in
        let tm_subst = List.map TMS.tm_param tms in
        let subst = List.map (fun (v, _) -> Proof_rep.Free v) stable_env' in
        let body' = open_proof tm_subst subst (body pat) in
        check (stable_env @ stable_env') env' body' nprop) (pat_for_p pprop)
    | Pr_n_match body, [], _ ->
      List.for_all (fun ({pat; tms; vars; out = nprop'} : npat_rec) ->
        let stable_env' = List.map (fun npropx -> (G.gen_tag (), npropx)) vars in
        let tm_subst = List.map TMS.tm_param tms in
        let subst = List.map (fun (v, _) -> Proof_rep.Free v) stable_env' in
        let body' = open_proof tm_subst subst (body pat) in
        check (stable_env @ stable_env') [] body' nprop') (pat_for_n nprop)
    | Pr_p_rfoc value, _, N_shift pprop ->
      check_value stable_env env value pprop
    | Pr_n_lfoc (Proof_rep.Free v, stack), _, _ ->
      check_stack stable_env env stack (List.assoc v stable_env) nprop
    | _, _, _ ->
      fail_check "ill-typed expression"

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
    let pprop' = PROP.open_pt tm pprop_body in
    check_value stable_env env value' pprop'
  | Pr_value (subst, _, {node = Pat_p_bvar i; _}), P_shift nprop ->
    let subst_len = List.length subst in
    if i < subst_len then
      check stable_env env (List.nth subst i) nprop
    else
      fail_check "unbound value variable"
  | _, _ ->
      fail_check "ill-typed value"

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
    let nprop_hole' = PROP.open_nt tm nprop in
    check_stack stable_env env stack' nprop_hole' nprop_ret
  | Pr_stack (_, [], Some k, {node = Pat_n_covar; _}), N_shift pprop, _ ->
    check stable_env (pprop :: env) k nprop_ret
  | _, _, _ ->
    fail_check "ill-typed stack"

  let pr_value_unit = pr_value [] [] pat_p_unit
  let pr_value_shift p = pr_value [p] [] (pat_p_bvar 0)
  let pr_stack_app (value : value) (stack : stack) =
    (* We need to shift the bound variables in stack, because they are now bound together with those of value *)
    let Proof_rep.Pr_value (subst1, tms1, ppat) = value.node in
    let shift_subst_amt = List.length subst1 in
    let shift_tms_amt = List.length tms1 in
    let Proof_rep.Pr_stack (subst2, tms2, k, npat) = stack.node in
    let tms2_ren = buildList (fun i -> i + shift_tms_amt) (List.length tms2) in
    let ren = buildList (fun i -> pat_p_bvar (i + shift_subst_amt)) (List.length subst2) in
    let npat' = open_npat tms2_ren ren npat in
      pr_stack (subst1 @ subst2) (tms1 @ tms2) k (pat_n_app ppat npat')
  let pr_stack_proj tag (stack : stack) =
    let Proof_rep.Pr_stack (subst, tms, k, npat) = stack.node in
      pr_stack subst tms k (pat_n_proj tag npat)

  let pr_stack_projL stack = pr_stack_proj Proof_rep.Left stack
  let pr_stack_projR stack = pr_stack_proj Proof_rep.Right stack
  let pr_stack_covar = pr_stack [] [] None pat_n_covar
  let pr_stack_shift k = pr_stack [] [] (Some k) pat_n_covar

  let pr_bvar i : proof = pr_n_lfoc (Bound i) pr_stack_covar
end
