module type S = sig
  type sequent
  type tm_unification

  (* val solve_sequent_limit : int -> (sequent list -> int) -> sequent -> search_result *)
  val solve_sequents_limit : int -> (sequent list -> int) -> sequent list -> bool
  val solve_sequent : (sequent list -> int) -> sequent -> bool
  val search_goals : (sequent list -> int) -> Top.TagSet.t -> sequent list -> bool
end
module Make (G:Globals.T)(TMS:Tm.S)(PROPS:Prop.S)(RULES : Rule.S)
    (SYNTH : Synthetics.S with type rule := RULES.t and type sequent := RULES.sequent)
    (SEARCH : Search.S with type solution := RULES.tm_unification)
  : (S with type tm_unification := RULES.tm_unification and type sequent := RULES.sequent) =
  struct

  type search_result = SEARCH.t


  let rec fold_right_lazy (f : 'a -> (unit -> 'acc) -> 'acc) (list : 'a list) (init : unit -> 'acc) : 'acc =
    match list with
    | [] -> init ()
    | x::xs -> f x (fun () -> fold_right_lazy f xs init)

  (** Apply a given unification to all rules in a list *)
  let apply_unif_sequents (unif : RULES.tm_unification) rules : RULES.sequent list =
    List.map (RULES.apply_unif_sequent { any = None; terms = unif }) rules

  (* Old behavior: Succeeds if f succeeds on everything in list (or list is
     empty). Fails if f fails on anything in list. *)
  (** Return lazy list of all of the unifications from calling f on *every*
      element of the list.

      Empty sequence indicates there is no suitable unification. *)
  let rec results_for_all (solve_sequent : RULES.sequent -> unit -> search_result)
                          (list : RULES.sequent list) : unit -> search_result =
    fun () ->
      match list with
      | [] -> SEARCH.trivial
      | x :: xs ->
        let res = solve_sequent x () in
        let proc (unif : RULES.tm_unification) (prev_result : unit -> search_result) =
          let rest_result = results_for_all solve_sequent (apply_unif_sequents unif xs) in
          (* the filter_map should not actually filter anything out since we know unif is independent from the solutions in rest_result *)
          let new_result : unit -> search_result = SEARCH.filter_map (RULES.unif_combine unif) rest_result in
          SEARCH.append new_result prev_result ()
        in
        SEARCH.fold_right proc res SEARCH.empty


  type state_cache = { score : int; state : RULES.sequent list }



  (** Return concatenated lazy list of all of the results from calling search on *some*
      element of rules.
  *)
  let results_exists (search : RULES.sequent list -> unit -> search_result) (obligation : RULES.sequent)
      (heuristic : RULES.sequent list -> int) (k : unit -> unit) (rules : RULES.t list) : search_result =
    let step rule =
      match RULES.apply rule obligation with
      | None -> None
      | Some (subgoals, _) ->
        let score = heuristic subgoals in
        Some { score; state = subgoals }
    in
    let next_states = List.sort (fun a b -> compare a.score b.score) (List.filter_map step rules) in
    (* TODO did we get laziness right here? *)
     fold_right_lazy (fun x prev_result ->
        SEARCH.append (search x.state) prev_result ())
       next_states (fun () -> k (); SEARCH.empty false)


  (** Search rules to find a derivation of a given goal that is no more than max_depth rules deep. *)
  let rec solve_sequent_limitk (max_depth : int) (heuristic : RULES.sequent list -> int) (k : unit -> unit) (obligation : RULES.sequent)
    : unit -> search_result =
    let obligation_str = (Pp.string_of_x (fun fmt -> (RULES.pp_sequent G.lookup_sym fmt)) obligation) in
    Debug.debug_start "Solving %s at max_depth %d%!" obligation_str max_depth;
    let new_k () = Debug.debug_end (); k () in
    begin if max_depth < 1 then
          fun () -> new_k (); SEARCH.empty true
      else
        let some_rule_applies rules =
          results_exists (results_for_all (solve_sequent_limit (max_depth - 1) heuristic)) obligation heuristic new_k rules in

        (* Right focus on atomic prop: does ID rule apply? *)
            let immediate =
              let (assumptions, goal) = obligation in
              List.fold_right (fun hyp res ->
              let goal_unif = RULES.unify_goal goal (Atomic hyp) in
              match goal_unif with
              | None -> res
              | Some unif -> SEARCH.cons unif.terms res)
            assumptions (fun () -> SEARCH.empty false)
        in
        let nonimmediate () =
          some_rule_applies (SYNTH.get_rules obligation)
        in
        SEARCH.append immediate nonimmediate
    end
  and solve_sequent_limit (max_depth : int) (heuristic : RULES.sequent list -> int) (obligation : RULES.sequent) =
    solve_sequent_limitk max_depth heuristic (fun _ -> ()) obligation

  let solve_sequents_limit (max_depth : int) (heuristic : RULES.sequent list -> int) : RULES.sequent list -> bool =
    List.for_all (fun obligation -> SEARCH.is_success (solve_sequent_limit max_depth heuristic obligation ()))

  (** Search rules to solve a given goal *)
  let solve_sequent (heuristic : RULES.sequent list -> int) (obligation : RULES.sequent) : bool =
    let rec helper max_depth (acc : search_result) =
      if not (SEARCH.is_success acc) then
        (if SEARCH.has_more acc then
          let search = solve_sequent_limit max_depth heuristic obligation () in
          helper (max_depth + 1) search
        else false)
      else
        true
    in
    helper 1 (SEARCH.empty true)

  (** Iterate through each proof obligation and check whether it unifies with a hypothesis
      or the conclusion of any rule *)
  let search_goals (heuristic : RULES.sequent list -> int) _ : RULES.sequent list -> bool =
    List.for_all (solve_sequent heuristic)

end
