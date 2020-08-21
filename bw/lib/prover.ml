module type S = functor (RULES : Rule.S) (SYNTHF : Synthetics.S) -> sig
  type search_result = {
    unifs : RULES.tm_unification Seq.t;
    more  : bool
  }

  val solve_sequent_limit : int -> RULES.sequent -> search_result
  val solve_sequent : RULES.sequent -> bool
  val search_goals : Top.TagSet.t -> RULES.sequent list -> bool
end
module Make (G:Globals.T)(TMS:Tm.S)(PROPS:Prop.S)(RULES:Rule.S)(SYNTHF:Synthetics.S) = struct
  module SYNTH = SYNTHF (RULES)

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



  type search_result = {
    unifs : RULES.tm_unification Seq.t;
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
  let result_cons (unif : RULES.tm_unification) (result : search_result) =
    { unifs = (fun () -> Seq.Cons (unif, result.unifs)); more = result.more }

  (** Apply a given unification to all rules in a list *)
  let apply_unif_sequents (unif : RULES.tm_unification) rules : RULES.sequent list =
    List.map (RULES.apply_unif_sequent { any = None; terms = unif }) rules

  (* Old behavior: Succeeds if f succeeds on everything in list (or list is
     empty). Fails if f fails on anything in list. *)
  (** Return lazy list of all of the unifications from calling f on *every*
      element of the list.

      Empty sequence indicates there is no suitable unification. *)
  let rec results_for_all (solve_sequent : RULES.sequent -> search_result)
                          (list : RULES.sequent list) : search_result =
      match list with
      | [] -> result_trivial
      | x :: xs ->
        let res = solve_sequent x in
        Seq.fold_left (fun prev_result (unif : RULES.tm_unification) ->
            let rest_result = results_for_all solve_sequent (apply_unif_sequents unif xs) in
            let new_unifs = (Seq.filter_map (RULES.unif_combine unif) rest_result.unifs) in
            let new_result = { unifs = new_unifs; more = rest_result.more } in
            result_append prev_result new_result)
          { unifs = Seq.empty; more = res.more } res.unifs


  (* Old behavior: Succeeds if f succeeds on anything in list. Fails if f fails
     on everything in list (or list is empty). *)
  (** Return concatenated lazy list of all of the results from calling f on *some*
      element of list. *)
  let results_exists (f : RULES.t -> search_result) (list : RULES.t list) : search_result =
    List.fold_left (fun prev_result x ->
      result_append prev_result (f x))
      result_empty list


  (** Search rules to find a derivation of a given goal that is no more than max_depth rules deep. *)
  let rec solve_sequent_limit (max_depth : int) (obligation : RULES.sequent) : search_result =
    debug (Printf.sprintf "Solving %s at max_depth %d\n"
             (Pp.string_of_x (fun fmt -> (RULES.pp_sequent G.lookup_sym fmt)) obligation)
             max_depth);
    if max_depth < 1 then
      { unifs = Seq.empty; more = true }
    else
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
            let goal_unif = (RULES.unify_goal goal (Atomic hyp)) in
            match goal_unif with
              | None -> res
              | Some unif -> result_cons unif.terms res)
          assumptions result_empty
      in

      let nonimmediate = some_rule_applies (SYNTH.get_rules obligation) in
      result_append immediate nonimmediate


  (** Search rules to solve a given goal *)
  let solve_sequent (obligation : RULES.sequent) : bool =
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
  let search_goals _ : RULES.sequent list -> bool =
    List.for_all solve_sequent
end
