open Debug
open Core
open Util
open Proof_rep.StackRep
open Proof_rep.ValueRep
open Proof_rep.ProofRep
open Prop_rep

module type S = sig

  type rule
  type lrule
  type rrule
  type sequent
  type lrule_table = lrule list Int.Table.t
  type rrule_table = rrule list Int.Table.t

  val lfoc_rules : lrule_table
  val rfoc_rules : rrule_table
  val get_rules : sequent -> rule list

  val make_synthetics : pprop list -> nprop -> Top.TagSet.t * sequent list
end

module Make (G:Globals.T)(TMS:Tm.S)(PROPS:Prop.S)(RULES : Rule.S) (PROOF:Proof.S)
  : (S with type rule := proof RULES.t and
            type lrule := stack RULES.t and
            type rrule := value RULES.t and
            type sequent := RULES.sequent) = struct
  open Tm_rep
  open TMS
  open PROPS
  open RULES

  type rrule = value RULES.t

  type lrule_table = stack RULES.t list Int.Table.t
  let lfoc_rules : lrule_table  = Int.Table.create () ~size:251

  type rrule_table = value RULES.t list Int.Table.t
  let rfoc_rules : rrule_table  = Int.Table.create () ~size:251



  type stable_goal =
    | GAtomic of Top.tag * tm list
    | GProp of pprop
    | GAny

  (* 'stable' asssumptions/sequents are built before synthetic props are generated *)
  type stable_assumptions = (Top.tag * nprop) list
  type stable_sequent = { assumptions : stable_assumptions; goal : stable_goal; }

  type inv_rule = { premises : (Top.TagSet.t * stable_sequent) list; arity : int; builder : proof builder }

  type rfoc_builder = value builder
  type rfoc_rule = { uvars : Top.TagSet.t; params : Top.TagSet.t; premises : sequent list; arity : int; builder : rfoc_builder }

  type lfoc_builder = stack builder
  type lfoc_rule = { uvars : Top.TagSet.t; params : Top.TagSet.t; premises : sequent list; arity : int; conclusion : goal; builder : lfoc_builder }

  let cross_product2
      (prem1 : lfoc_rule list)
      (prem2 : rfoc_rule list) :
      lfoc_rule list =
    List.fold_left prem2 ~init:[] ~f:(fun r ({uvars = uvars2; params = params2; premises = prems2; builder = builder2; arity = arity2 } : rfoc_rule) ->
	    (List.map prem1 ~f:(fun {uvars = uvars1; params = params1; premises = prems1; builder = builder1; arity = arity1; conclusion = goal} ->
             { uvars = Top.TagSet.union uvars1 uvars2; params = Top.TagSet.union params1 params2;
               premises = prems1 @ prems2;
               conclusion = goal;
               arity = arity1 + arity2;
               builder = fun proofs -> let (proofs1, proofs2) = List.split_n proofs arity1 in PROOF.pr_stack_app (builder2 proofs2) (builder1 proofs1) ;
             })) @ r)

  let synthetic_of_pprop p =
    Atomic(p.Hashcons.tag, List.map (Top.TagSet.elements (fv_pprop p)) ~f:tm_param)

  let synthetic_of_nprop n : atomic_prop =
    let id = n.Hashcons.tag in
    match n.Hashcons.node with
    | N_prop(a, ts) -> (a, ts)
    | _ -> (id, List.map (Top.TagSet.elements (fv_nprop n)) ~f:tm_param)


  (* returns a list of open stable sequents -- formulas in those sequents are to be used as synthetic connectives *)
  (* also returns a proof builder with arity *)
  let rec invert_right (m : Top.TagSet.t) (d : stable_assumptions) (g : pprop list) (n : nprop) : inv_rule =
    debug "invert_right: %s" (Pp.string_of_nprop G.lookup_sym n);
    match n.Hashcons.node with
    | N_top    -> {premises = []; arity = 0; builder = fun _ -> PROOF.pr_tt}
    | N_prop(a, ts) ->
      invert_left m d g (GAtomic(a, ts))  (* atomic propositions will always be considered rules *)
    | N_and(n1, n2)  ->
      let ({premises = j1; arity = arity1; builder = builder1} : inv_rule) = invert_right m d g n1 in
      let ({premises = j2; arity = arity2; builder = builder2} : inv_rule) = invert_right m d g n2 in
      {premises = j1 @ j2; arity = arity1 + arity2; builder = fun proofs ->
        let (proofs1, proofs2) = List.split_n proofs arity1 in
        PROOF.pr_n_match (function
          | {node = Pat_n_proj (Left, npat); _} -> PROOF.pr_n_match_exec (builder1 proofs1) npat
          | {node = Pat_n_proj (Right, npat); _} -> PROOF.pr_n_match_exec (builder2 proofs2) npat) }
    | N_imp(p1, n2) ->
      invert_right m d (p1::g) n2
    | N_all n1 ->
      let x = G.gen_tag () in
      invert_right (Top.TagSet.add x m) d g (open_nt (tm_param x) n1)   (* these parameters might end up being "global" *)
    | N_shift p -> invert_left m d g (GProp p)

  and invert_left (m : Top.TagSet.t) (d : stable_assumptions) (g : pprop list) (c : stable_goal) : inv_rule =
    let _ = debug "invert_left: " in
    match g with
    | [] ->
      {premises = [(m, { assumptions = d; goal = c; })]; arity = 1; builder = fun [proof] -> proof}
      (* begin match c with
       * TODO I think the any case below is causing a bug
	     *   | GAny -> []
	     *   | GAtomic(a, ts) -> [(m, (d, GAtomic(a, ts)))]
	     *   | GProp p -> [(m, (d, GProp p))]
       * end *)
    | (p::g') ->
      debug "%s" (Pp.string_of_pprop G.lookup_sym p);
      begin match p.Hashcons.node with
       | P_one  -> invert_left m d g' c
       | P_zero -> { premises = []; arity = 0; builder = fun _ -> PROOF.pr_ex_falso}
       | P_or(p1, p2) ->
           let ({premises = j1; arity = arity1; builder = builder1} : inv_rule) = invert_left m d (p1::g') c in
           let ({premises = j2; arity = arity2; builder = builder2} : inv_rule) = invert_left m d (p2::g') c in
	         { premises = j1 @ j2; arity = arity1 + arity2; builder = fun proofs ->
               let (proofs1, proofs2) = List.split_n proofs arity1 in
               PROOF.pr_p_match (function
                 | {node = Pat_p_inj (Left, ppat)} -> PROOF.pr_p_match_exec (builder1 proofs1) ppat
                 | {node = Pat_p_inj (Right, ppat)} -> PROOF.pr_p_match_exec (builder2 proofs2) ppat) }
       | P_ex p1 ->
	         let x = G.gen_tag () in
	           invert_left (Top.TagSet.add x m) d ((open_pt (tm_param x) p1) :: g') c
       | P_shift n ->
          let x = G.gen_tag () in
          invert_left m ((x, n)::d) g' c
      end


    (* let helper (u_gen, p_gen, prems, goal) =
     *   {params = p_gen;
     *    uvars = Top.TagSet.union u u_gen;
     *    premises = prems;
     *    conclusion = goal;
     *    builder = (??) } *)


  (* u is the unification variables introduced by the outer scopes *)
  (* n is a negative formula that is a synthetic connective *)
  (* returns: *)
  (*  parameters * unification vars * premises * goal??  *)
  (* side effect: *)
  (*   create the left rules for the sub-connectives and add them to the global rules database *)
  and focus_left (uvars : Top.TagSet.t) (n : nprop) : lfoc_rule list =
    debug "focus_left: %s" (Pp.string_of_nprop G.lookup_sym n);
    match n.Hashcons.node with
    | N_top    ->  failwith "shouldn't focus-left on Top"
    | N_prop(_,_) ->
      [{params = Top.TagSet.empty; uvars; premises = [];
	      conclusion = Atomic(synthetic_of_nprop n);
        arity = 0; builder = (fun _ -> PROOF.pr_stack_covar)}]   (* propositions are always considered rules, they have no subrules *)
    | N_and(n1, n2) ->
      let prem1 = focus_left uvars n1 in
      let prem2 = focus_left uvars n2 in
      prem1 @ prem2
    | N_imp(p1, n2) ->
      let prem1 = focus_right uvars p1 in
      let prem2 = focus_left uvars n2 in
      cross_product2 prem2 prem1    (* do the 'goal' side first *)
    | N_all n1 -> (* ? *)
      (* Add a unification variable *)
      let x = G.gen_tag () in
      focus_left (Top.TagSet.add x uvars) (open_nt (tm_param x) n1)
    | N_shift p ->
      let ({premises = ts; arity = _; builder} : inv_rule) = invert_left Top.TagSet.empty [] [p] GAny in
      (* Create the synthetic subrules by side effect *)
      (* then *)
      let (params, premises) = List.fold_left ~f:(fun (params, prems) (p, j) ->
          (Top.TagSet.union params p, (synthetic uvars j)::prems))
          ~init:(Top.TagSet.empty, []) ts in
      [{params; uvars; premises; conclusion = Any; arity = List.length premises;
        builder = fun proofs -> PROOF.pr_stack_shift (builder proofs)}]

  (* takes   uvars, prop *)
  and focus_right uvars pprop : rfoc_rule list =
    debug "focus_right: %s" (Pp.string_of_pprop G.lookup_sym pprop);
    match pprop.Hashcons.node with
    | P_one -> [{uvars = Top.TagSet.empty; params = Top.TagSet.empty; premises = []; arity = 0; builder = fun [] -> PROOF.pr_value_unit}]
    | P_zero -> failwith "Shouldn't focus right on zero"
    | P_or(p1, p2) ->
      let prem1 = focus_right uvars p1 in
      let prem2 = focus_right uvars p2 in
      prem1 @ prem2
    | P_ex p1 ->
      let x = G.gen_tag () in
      focus_right (Top.TagSet.add x uvars) (open_pt (tm_param x) p1)
    | P_shift n ->
      let ts = invert_right Top.TagSet.empty [] [] n in
      let (params, premises) = List.fold_left
          ~f:(fun (params, prems) (p, j) -> (Top.TagSet.union params p, (synthetic uvars j)::prems))
          ~init:(Top.TagSet.empty, []) ts.premises in
      [{params; uvars; premises; arity = List.length premises; builder = fun proofs -> PROOF.pr_value_shift (ts.builder proofs)}]

  (** Convert a stable sequent to a synthetic one. *)
  and synthetic u ({assumptions; goal = g} : stable_sequent) : sequent  =
        {assumptions = List.map ~f:(fun (x, hyp) -> (x, mk_synthetic_rule_of_nprop u hyp)) assumptions; goal = synthetic_of_goal u g}

  (** Add synthetic rules for n to rules, return the synthetic connective *)
  and mk_synthetic_rule_of_nprop (u : Top.TagSet.t) (n : nprop) : atomic_prop =
    let id = n.Hashcons.tag in
    begin if Hashtbl.mem lfoc_rules id then
        ()
      else
        List.iter ~f:(fun value -> Hashtbl.add_multi lfoc_rules ~key:id ~data:value) (make_left_rules u n)
    end;
    synthetic_of_nprop n

  and synthetic_of_goal u g =
    debug "synthetic_of_goal";
    match g with
    | GAny ->
      debug "-> Any";
      Any
    | GAtomic(a, ts) ->
      debug "-> Atomic";
      Atomic(a, ts)
    | GProp p -> debug "-> GProp"; begin let id = p.Hashcons.tag in
		                     begin if Hashtbl.mem rfoc_rules id then
                           debug "right rules already added"
                         else
		                       List.iter ~f:(fun value ->
                             debug "add right rule.";
                             Hashtbl.add_multi rfoc_rules ~key:id ~data:value)
                             (make_right_rules u p)
                         end;
	                       synthetic_of_pprop p
                 end


  and make_left_rules (u : Top.TagSet.t) (n : nprop) : stack RULES.t list =
    debug "\n\nmake_left_rules: %s" (Pp.string_of_nprop G.lookup_sym n);
    let helper ({uvars = u_gen; params; premises; conclusion; arity = _; builder} : lfoc_rule) : stack RULES.t =
      {params;
       uvars = Top.TagSet.union u u_gen;
       premises;
       conclusion;
       builder}
    in match n.Hashcons.node with
    | N_prop _ -> [] (* TODO shouldn't this include the identity rule? (identity rule currently hardcoded in search procedure) *)
    | _ -> List.map ~f:helper (focus_left u n)


  and make_right_rules u p : value RULES.t list =
    debug "\n\nmake_right_rules: %s" (Pp.string_of_pprop G.lookup_sym p);
    let goal = synthetic_of_pprop p in
    let helper ({uvars = u_gen; params; premises; arity = _; builder} : rfoc_rule) : value RULES.t =
      {params;
       uvars = Top.TagSet.union u u_gen;
       premises;
       conclusion = goal;
       builder}
    in
    match p.Hashcons.node with
    | P_zero -> []
    | _ -> 	List.map ~f:helper (focus_right u p)


  (* TODO doc make_synthetics *)
  let make_synthetics (g : pprop list) (n : nprop) : Top.TagSet.t * sequent list =
    debug "make_synthetics";
    (* get a list of open stable sequents to prove *)
    let ts = invert_right Top.TagSet.empty [] g n in


    let synthetic ({assumptions = ns; goal = g} : stable_sequent) : sequent =
      {assumptions = List.map ~f:(fun (x, hyp) -> (x, mk_synthetic_rule_of_nprop Top.TagSet.empty hyp)) ns;
       goal = synthetic_of_goal Top.TagSet.empty g} in

    (* combine all proof obligations from ts and call synthetic to make the synthetic rules *)
    let (params, sequents) = List.fold_left
        ~f:(fun (params, prems) (p, next_prem) -> (Top.TagSet.union params p, (synthetic next_prem)::prems))
        ~init:(Top.TagSet.empty, []) ts.premises in
    (params, sequents)

  (** Get right-focused rules that can solve the given goal *)
  let get_rrules (goal : RULES.goal) : value RULES.t list =
    match goal with
    | Atomic (tag, _) ->
      Hashtbl.find_multi rfoc_rules tag
    | Any -> (failwith "impossible") (* TODO figure out this case ? *)

  (** Get rules for the given formula *)
  let get_lrules ((tag, _) : RULES.atomic_prop) : stack RULES.t list =
    Hashtbl.find_multi lfoc_rules tag

  let rule_of_rrule (rrule:value RULES.t) : proof RULES.t =
    { rrule with builder = fun proofs -> PROOF.pr_p_rfoc (rrule.builder proofs) }

  let rule_of_lrule x (lrule:stack RULES.t) : proof RULES.t =
    { lrule with builder = fun proofs -> PROOF.pr_n_lfoc (Proof_rep.Free x) (lrule.builder proofs)}

  let get_rules ({assumptions; goal} : RULES.sequent) : proof RULES.t list =
    let rrules = List.map ~f:rule_of_rrule (get_rrules goal) in
    let lrules = List.concat_map ~f:(fun (x, prop) -> List.map ~f:(rule_of_lrule x) (get_lrules prop)) assumptions in
    (rrules @ lrules)


end
