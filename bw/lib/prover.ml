open Util

module Make (G:Globals.T)(TMS:Tm.S)(PROPS:Prop.S)(RULES:Rule.S) = struct
  open Tm_rep
  open Prop_rep
  (*  open Pp *)
  open TMS
  open PROPS
  open RULES

  type rule_t = (int, RULES.t) Hashtbl.t
  let rules : rule_t = Hashtbl.create 251

  let debug_flag = ref false
  let backtrack_flag = ref false

  let backtrack s n =
    if !backtrack_flag && n > 0 then
      Printf.printf "%s (depth %d)\n" s n
    else ()

  let debug s =
    if !debug_flag then
      print_endline s
    else ()

  let debug_breakpt () =
    if !debug_flag then
      let _ = Printf.printf "[Continue]\n"; read_line () in
      ()
    else ()

  type inversion_goal =
    | GAtomic of Top.tag * tm list
    | GProp of pprop
    | GAny


  let cross_product prem1 prem2 =
    List.fold_left (fun r (ps2, ts2, l2) ->
	(List.map (fun (ps1, ts1, l1) -> (Top.TagSet.union ps1 ps2, Top.TagSet.union ts1 ts2, l1@l2)) prem1)@r) [] prem2

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
  let get_rules ((tag, _) : RULES.atomic_prop) : RULES.t list =
    Hashtbl.find_all rules tag

  type search_result = {
    unifs : tm_unification Seq.t;
    more  : bool
  }

  let seq_is_empty seq =
    match seq with
    | Seq.Nil -> true
    | _ -> false

  let rec seq_append (seq1 : 'a Seq.t) (seq2 : 'a Seq.t) () : 'a Seq.node =
    match seq1 () with
    | Seq.Nil -> seq2 ()
    | Seq.Cons (x, xs) -> Seq.Cons (x, (seq_append xs seq2))

  let result_append { unifs = unifs1; more = more1 } { unifs = unifs2; more = more2 } =
    { unifs = seq_append unifs1 unifs2; more = more1 || more2 }

  let result_empty : search_result = { unifs = Seq.empty; more = false }
  let result_trivial : search_result = { unifs = Seq.return RULES.unif_empty; more = false }
  let result_cons (unif : tm_unification) (result : search_result) =
    { unifs = (fun () -> Seq.Cons (unif, result.unifs)); more = result.more }

  (** Apply a given unification to all rules in a list *)
  let apply_unif_sequents (unif : tm_unification) rules : sequent list =
    List.map (apply_unif_sequent { any = None; terms = unif }) rules

  (* Old behavior: Succeeds if f succeeds on everything in list (or list is
     empty). Fails if f fails on anything in list. *)
  (** Return lazy list of all of the unifications from calling f on *every*
      element of the list.

      Empty sequence indicates there is no suitable unification. *)
  let rec results_for_all (solve_sequent : sequent -> search_result)
                          (list : sequent list) : search_result =
      match list with
      | [] -> result_trivial
      | x :: xs ->
        let res = solve_sequent x in
        Seq.fold_left (fun prev_result (unif : tm_unification) ->
            let rest_result = results_for_all solve_sequent (apply_unif_sequents unif xs) in
            let new_unifs = (Seq.filter_map (RULES.unif_combine unif) rest_result.unifs) in
            let new_result = { unifs = new_unifs; more = rest_result.more } in
            result_append prev_result new_result)
          { unifs = Seq.empty; more = res.more } res.unifs

  (*
    List.fold_right (fun obligation prev_result ->
        apply_unif_seq obligation
      )
      list result_trivial
  *)


  (* Old behavior: Succeeds if f succeeds on anything in list. Fails if f fails
     on everything in list (or list is empty). *)
  (** Return concatenated lazy list of all of the results from calling f on *some*
      element of list. *)
  let results_exists (f : RULES.t -> search_result) (list : RULES.t list) : search_result =
    List.fold_left (fun prev_result x ->
      result_append prev_result (f x))
      result_empty list 

    (* If we reach the depth limit, try to apply another rule to find a shorter
       proof.

       If we hit the depth limit at any point and by the end, we still
       haven't found a proof, then propagate the Limit_reached exception. *)
    (* let (seq, limit_reached) = List.fold_right
     *     (fun x (seq, limit_reached) ->
     *        try seq_append (f x) seq
     *        with
     *        | Limit_reached -> (seq, true))
     *     list
     *     (Seq.empty, false) in
     * if limit_reached && seq_is_empty then
     *   raise Limit_reached
     * else
     *   seq *)

    (* List.fold_left (fun acc x ->
     *     match acc with
     *      | Search_succeeded -> Search_succeeded
     *      | Search_failed -> f x
     *      | Limit_reached ->
     *        begin match f x with
     *          | Search_failed -> Limit_reached
     *          | r -> r
     *        end) Search_failed list *)

  (** Search rules to find a derivation of a given goal that is no more than max_depth rules deep. *)
  let rec solve_sequent_limit (max_depth : int) (obligation : sequent) : search_result =
    debug (Printf.sprintf "Solving %s at max_depth %d\n"
             (Pp.string_of_x (fun fmt -> (RULES.pp_sequent G.lookup_sym fmt)) obligation)
             max_depth);
    if max_depth < 1 then
      { unifs = Seq.empty; more = true }
    else
      let (assumptions, goal) = obligation in

      (* Apply a given rule and, if possible, continue the proof at the next level of depth. *)
      let rule_applies rule =
        begin match RULES.apply rule obligation with
          | None -> { unifs = Seq.empty; more = false }
          | Some (subgoals, _(* unif *)) ->
            debug (Printf.sprintf "apply %s\n" (Pp.string_of_x (RULES.pp_rule G.lookup_sym) rule));
            (* TODO combine unif with the unifications in the result *)
            results_for_all (solve_sequent_limit (max_depth - 1)) subgoals
        end in
      let some_rule_applies rules =
        results_exists rule_applies rules in

      (* Right focus on atomic prop: does ID rule apply? *)
      let immediate =
        let (assumptions, goal) = obligation in
        List.fold_right (fun hyp res ->
            let goal_unif = (unify_goal goal (Atomic hyp)) in
            match goal_unif with
              | None -> res
              | Some unif -> result_cons unif.terms res)
          assumptions result_empty
      in

      let nonimmediate =
        (* Right focus on synthetic connective *)
        let rrules = get_rrules goal in
        let lrules = List.concat_map get_rules assumptions in
        some_rule_applies (rrules @ lrules)
      in

      result_append immediate nonimmediate


  (** Search rules to solve a given goal *)
  let solve_sequent (obligation : sequent) : bool =
    let rec helper max_depth (acc : search_result) =
      let is_empty =
        match acc.unifs () with
        | Seq.Nil -> true
        | _ -> false
      in
      if is_empty then
        (if acc.more then
          let search = solve_sequent_limit max_depth obligation in
          helper (max_depth + 1) search
        else false)
      else
        true
    in
    helper 1 {unifs = Seq.empty; more = true}

  (** Iterate through each proof obligation and check whether it unifies with a hypothesis
      or the conclusion of any rule *)
  let search_goals _ : sequent list -> bool =
    List.for_all solve_sequent
end
