module type S = sig
  type sequent
  type tm_unification


  type search_result = {
    unifs : tm_unification Seq.t;
    more  : bool
  }

  val is_success : search_result -> bool
  val debug_flag : bool ref
  val solve_sequent_limit : int -> (sequent list -> int) -> sequent -> search_result
  val solve_sequents_limit : int -> (sequent list -> int) -> sequent list -> bool
  val solve_sequent : (sequent list -> int) -> sequent -> bool
  val search_goals : (sequent list -> int) -> Top.TagSet.t -> sequent list -> bool
end
module Make (G:Globals.T)(TMS:Tm.S)(PROPS:Prop.S)(RULES : Rule.S)
    (SYNTH : Synthetics.S with type rule := RULES.t and type sequent := RULES.sequent)
  : (S with type tm_unification := RULES.tm_unification and type sequent := RULES.sequent) =
  struct


  let debug_flag = ref false

  let debug s =
    if !debug_flag then
      print_endline s
    else ()

  (* let debug_breakpt () =
   *   if !debug_flag then
   *     let _ = Printf.printf "[Continue]\n"; read_line () in
   *     ()
   *   else () *)



  type search_result = {
    unifs : RULES.tm_unification Seq.t;
    more  : bool
  }

  let is_success (result : search_result) : bool =
    match result.unifs () with
    | Seq.Nil -> false
    | _ -> true

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


  type state_cache = { score : int; state : RULES.sequent list }

  (** Return concatenated lazy list of all of the results from calling f on *some*
      element of list.
  *)
  let results_exists (search : RULES.sequent list -> search_result) (obligation : RULES.sequent)
      (heuristic : RULES.sequent list -> int) (list : RULES.t list) : search_result =
    let step rule =
      match RULES.apply rule obligation with
      | None -> None
      | Some (subgoals, _) ->
        Some { score = heuristic subgoals; state = subgoals }
    in
    let next_states = List.sort (fun a b -> compare a.score b.score) (List.filter_map step list) in
    List.fold_left (fun prev_result x ->
      result_append prev_result (search x.state))
      result_empty next_states


  (** Search rules to find a derivation of a given goal that is no more than max_depth rules deep. *)
  let rec solve_sequent_limit (max_depth : int) (heuristic : RULES.sequent list -> int) (obligation : RULES.sequent) : search_result =
    debug (Printf.sprintf "Solving %s at max_depth %d\n"
             (Pp.string_of_x (fun fmt -> (RULES.pp_sequent G.lookup_sym fmt)) obligation)
             max_depth);
    if max_depth < 1 then
      { unifs = Seq.empty; more = true }
    else
      let some_rule_applies rules =
        results_exists (results_for_all (solve_sequent_limit (max_depth - 1) heuristic)) obligation heuristic rules in

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

  let solve_sequents_limit (max_depth : int) (heuristic : RULES.sequent list -> int) : RULES.sequent list -> bool =
    List.for_all (fun obligation -> is_success (solve_sequent_limit max_depth heuristic obligation))

  (** Search rules to solve a given goal *)
  let solve_sequent (heuristic : RULES.sequent list -> int) (obligation : RULES.sequent) : bool =
    let rec helper max_depth (acc : search_result) =
      if not (is_success acc) then
        (if acc.more then
          let search = solve_sequent_limit max_depth heuristic obligation in
          helper (max_depth + 1) search
        else false)
      else
        true
    in
    helper 1 {unifs = Seq.empty; more = true}

  (** Iterate through each proof obligation and check whether it unifies with a hypothesis
      or the conclusion of any rule *)
  let search_goals (heuristic : RULES.sequent list -> int) _ : RULES.sequent list -> bool =
    List.for_all (solve_sequent heuristic)

end
