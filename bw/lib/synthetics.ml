open Util

module type S = sig
  open Prop_rep

  type rule
  type sequent
  type rule_table = (int, rule) Hashtbl.t

  val rules : rule_table
  val get_rules : sequent -> rule list
  val make_synthetics : pprop list -> nprop -> Top.TagSet.t * sequent list
end

module Make (G:Globals.T)(TMS:Tm.S)(PROPS:Prop.S) (RULES:Rule.S)
  : (S with type rule := RULES.t and type sequent := RULES.sequent) = struct
  open Tm_rep
  open Prop_rep
  open TMS
  open PROPS
  open RULES

  type rule_table = (int, RULES.t) Hashtbl.t
  let rules : rule_table = Hashtbl.create 251


  let debug_flag = ref false
  let debug s =
    if !debug_flag then
      print_endline s
    else ()


  type inversion_goal =
    | GAtomic of Top.tag * tm list
    | GProp of pprop
    | GAny

  let cross_product2
      (prem1 : (Top.TagSet.t * Top.TagSet.t * 'a list * 'b) list)
      (prem2 : (Top.TagSet.t * Top.TagSet.t * 'a list) list) :
      (Top.TagSet.t * Top.TagSet.t * 'a list * 'b) list =
    List.fold_left (fun r (ps2, ts2, l2) ->
	(List.map (fun (ps1, ts1, l1, g1) ->
             (Top.TagSet.union ps1 ps2, Top.TagSet.union ts1 ts2, l1@l2, g1)) prem1) @ r) [] prem2

  let synthetic_of_pprop p =
    Atomic(p.Hashcons.tag, List.map tm_param (Top.TagSet.elements (fv_pprop p)))

  let synthetic_of_nprop n : atomic_prop =
    let id = n.Hashcons.tag in
    match n.Hashcons.node with
    | N_prop(a, ts) -> (a, ts)
    | _ -> (id, List.map tm_param (Top.TagSet.elements (fv_nprop n)))


  (* returns a list of open stable sequents -- formulas in those sequents are to be used as synthetic connectives *)
  let rec invert_right (m : Top.TagSet.t) (d : nprop list) (g : pprop list) (n : nprop)
    : (Top.TagSet.t * (nprop list * inversion_goal)) list =
    debug ("invert_right: " ^ (Pp.string_of_nprop G.lookup_sym n));
    match n.Hashcons.node with
    | N_top    -> []
    | N_prop(a,ts) ->
      invert_left m d g (GAtomic(a, ts))  (* atomic propositions will always be considered rules *)
    | N_and(n1, n2)  ->
      let j1 = (invert_right m d g n1) in
      let j2 = (invert_right m d g n2) in
      j1 @ j2
    | N_imp(p1, n2) ->
      invert_right m d (p1::g) n2
    | N_all n1 ->
      let x = G.gen_tag () in
      invert_right (Top.TagSet.add x m) d g (open_nt (tm_param x) n1)   (* these parameters might end up being "global" *)
    | N_shift p -> invert_left m d g (GProp p)

  and invert_left m d g c =
    let _ = debug "invert_left: " in
    match g with
    | [] ->
      [(m, (d, c))]
      (* begin match c with
       * TODO I think the any case below is causing a bug
	     *   | GAny -> []
	     *   | GAtomic(a, ts) -> [(m, (d, GAtomic(a, ts)))]
	     *   | GProp p -> [(m, (d, GProp p))]
       * end *)
    | (p::g') ->
      debug (Pp.string_of_pprop G.lookup_sym p);
      begin match p.Hashcons.node with
       | P_one  -> invert_left m d g' c
       | P_zero -> []
       | P_or(p1, p2) ->
	         let j1 = (invert_left m d (p1::g') c) in
	         let j2 = (invert_left m d (p2::g') c) in
	           (j1 @ j2)
       | P_ex p1 ->
	         let x = G.gen_tag () in
	           invert_left (Top.TagSet.add x m) d ((open_pt (tm_param x) p1) :: g') c
       | P_shift n -> invert_left m (n::d) g' c
      end


  (* u is the unification variables introduced by the outer scopes *)
  (* n is a negative formula that is a synthetic connective *)
  (* returns: *)
  (*  parameters * unification vars * premises * goal??  *)
  (* side effect: *)
  (*   create the left rules for the sub-connectives and add them to the global rules database *)
  and focus_left (u : Top.TagSet.t) (n : nprop) : (Top.TagSet.t * Top.TagSet.t * sequent list * goal) list =
    debug ("focus_left: " ^ (Pp.string_of_nprop G.lookup_sym n));
    match n.Hashcons.node with
    | N_top    ->  failwith "shouldn't focus-left on Top"
    | N_prop(_,_) ->
      [(Top.TagSet.empty, u, [],
	      Atomic(synthetic_of_nprop n))]   (* propositions are always considered rules, they have no subrules *)
    | N_and(n1, n2) ->
      let prem1 = focus_left u n1 in
      let prem2 = focus_left u n2 in
      prem1 @ prem2
    | N_imp(p1, n2) ->
      let prem1 = focus_right u p1 in
      let prem2 = focus_left u n2 in
      cross_product2 prem2 prem1    (* do the 'goal' side first *)
    | N_all n1 -> (* ? *)
      (* Add a unification variable *)
      let x = G.gen_tag () in
      focus_left (Top.TagSet.add x u) (open_nt (tm_param x) n1)
    | N_shift p ->
      let ts = invert_left Top.TagSet.empty [] [p] GAny in
      (* Create the synthetic subrules by side effect *)
      (* then *)
      let synthetic ((ns, g) : nprop list * inversion_goal) : atomic_prop list * goal  =
        (List.map (mk_synthetic_rule_of_nprop u) ns, synthetic_of_goal u g) in
      let (params, prems) = List.fold_left (fun (params, prems) (p, j) ->
          (Top.TagSet.union params p, (synthetic j)::prems))
          (Top.TagSet.empty, []) ts in
      [(params, u, prems, Any)]

  (* takes   uvars, prop *)
  (* returns (params, uvars, premises) *)
  and focus_right u p : (Top.TagSet.t * Top.TagSet.t * sequent list) list =
    let _ = debug ("focus_right: "^ (Pp.string_of_pprop G.lookup_sym p)) in
    match p.Hashcons.node with
    | P_one -> []
    | P_zero -> failwith "Shouldn't focus right on zero"
    | P_or(p1, p2) ->
      let prem1 = focus_right u p1 in
      let prem2 = focus_right u p2 in
      prem1 @ prem2
    | P_ex p1 ->
      let x = G.gen_tag () in
      focus_right (Top.TagSet.add x u) (open_pt (tm_param x) p1)
    | P_shift n ->
      let ts = invert_right Top.TagSet.empty [] [] n in
      let synthetic (ns, g) = (List.map (mk_synthetic_rule_of_nprop u) ns, synthetic_of_goal u g) in
      let (params, prems) = List.fold_left
          (fun (params, prems) (p, j) -> (Top.TagSet.union params p, (synthetic j)::prems))
          (Top.TagSet.empty, []) ts in
      [(params, u, prems)]

  (** Add synthetic rules for n to rules, return the synthetic connective *)
  and mk_synthetic_rule_of_nprop (u : Top.TagSet.t) (n : nprop) : atomic_prop =
    let id = n.Hashcons.tag in
    begin if Hashtbl.mem rules id then
        ()
      else
        List.iter (Hashtbl.add rules id) (make_left_rules u n)
    end;
    synthetic_of_nprop n

  and synthetic_of_goal u g =
    match g with
    | GAny -> Any
    | GAtomic(a, ts) -> Atomic(a, ts)
    | GProp p -> (let id = p.Hashcons.tag in
		  if Hashtbl.mem rules id then () else
		      List.iter (Hashtbl.add rules id) (make_right_rules u p);
	    synthetic_of_pprop p)


  and make_left_rules (u : Top.TagSet.t) (n : nprop) : RULES.t list =
    debug ("\n\nmake_left_rules: " ^ Pp.string_of_nprop G.lookup_sym n);
    let helper (u_gen, p_gen, prems, goal) =
      {params = p_gen;
       uvars = Top.TagSet.union u u_gen;
       premises = prems;
       conclusion = goal}
    in match n.Hashcons.node with
    | N_prop _ -> [] (* TODO shouldn't this include the identity rule? *)
    | _ -> List.map helper (focus_left u n)


  and make_right_rules u p =
    debug ("\n\nmake_right_rules: " ^ Pp.string_of_pprop G.lookup_sym p);
    let goal = synthetic_of_pprop p in
    let helper (u_gen, p_gen, prems) =
      {params = p_gen;
       uvars = Top.TagSet.union u u_gen;
       premises = prems;
       conclusion = goal}
    in
    match p.Hashcons.node with
    | P_zero -> []
    | _ -> 	List.map helper (focus_right u p)


  let make_synthetics (g : pprop list) (n : nprop) : Top.TagSet.t * sequent list =
    let _ = debug "make_synthetics" in
    (* get a list of open stable sequents to prove *)
    let ts = invert_right Top.TagSet.empty [] g n in


    let synthetic ((ns, g) : nprop list * inversion_goal) : atomic_prop list * goal =
      (List.map (mk_synthetic_rule_of_nprop Top.TagSet.empty) ns,
       synthetic_of_goal Top.TagSet.empty g) in

    (* combine all proof obligations from ts and call synthetic to make the synthetic rules *)
    let (params, sequents) = List.fold_left
        (fun (params, prems) (p, j) -> (Top.TagSet.union params p, (synthetic j)::prems))
        (Top.TagSet.empty, []) ts in

    (params, sequents)

  (** Get right-focused rules that can solve the given goal *)
  let get_rrules (goal : RULES.goal) : RULES.t list =
    match goal with
    | Atomic (tag, _) -> Hashtbl.find_all rules tag
    | Any -> (failwith "what to do") (* TODO figure out this case*)

  (** Get rules for the given formula *)
  let get_lrules ((tag, _) : RULES.atomic_prop) : RULES.t list =
    Hashtbl.find_all rules tag

  let get_rules ((assumptions, goal) : RULES.sequent) : RULES.t list =
    let rrules = get_rrules goal in
    let lrules = List.concat_map get_lrules assumptions in
    (rrules @ lrules)


end
