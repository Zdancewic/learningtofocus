open Proof_rep.ProofRep
open Proof_rep.StackRep
open Proof_rep.ValueRep
module G = Globals.G

  type 'a search_result = 'a Search.t
  type 'a solution = 'a Search.solution
  type action = { score : int; rule : proof Rule.t; subgoals : Rule.sequent list; builder : proof Rule.builder; tm_unif : Tm_unif.t }
  type logger = Rule.sequent -> action -> proof Search.t -> unit

  let rec fold_right_lazy (f : 'a -> (unit -> 'acc) -> 'acc) (list : 'a list) (init : unit -> 'acc) : 'acc =
    match list with
    | [] -> init ()
    | x::xs -> f x (fun () -> fold_right_lazy f xs init)

  (** Apply a given unification to all rules in a list *)
  let apply_unif_sequents (unif : Tm_unif.t) rules : Rule.sequent list =
    List.map (Rule.apply_unif_sequent { any = None; terms = unif }) rules

  (** Return sequence of all of the unifications from calling f on *every* element of the list.

      Empty sequence indicates there is no suitable unification.
   *)
  let rec results_for_all (solve_sequent : Rule.sequent -> unit -> proof search_result)
                          (sequents : Rule.sequent list) : unit -> proof list search_result =
    fun () ->
      Debug.debug "results_for_all: %s" (Pp.string_of_x (fun fmt -> Pp.pp_list_aux fmt ", " (Rule.pp_sequent G.lookup_sym fmt) ) sequents);
      match sequents with
      | [] -> Search.trivial []
      | x :: xs ->
        let res_x = solve_sequent x () in
        let proc ({ Search.proof = pf_x; tm_unif = unif_x} : proof solution) (prev_res_xs : unit -> proof list search_result) =
          Debug.debug "sequent: %s  /  unif_x: %s" (Rule.string_of_sequent G.lookup_sym x) (Tm_unif.string_of_tm_unif G.lookup_sym unif_x);
          (* Recursively solve problem for rest of sequents (xs) using unification of first solution *)
          let res_xs = results_for_all solve_sequent (apply_unif_sequents unif_x xs) in
          (* next combine the unifications from the first solution with those of the rest *)
          (* the filter_map should not actually filter anything out since we know unif is independent from the solutions in rest_result *)
          let res_x_xs : unit -> proof list search_result =
            (* we don't need to do any substitution of tm_unif into pfs_xs thanks
               to apply_unif_sequents above *)
            Search.combine_unif unif_x (fun pfs_xs -> pf_x :: pfs_xs) res_xs in
          Debug.debug "for_all combine completed";
          Search.append res_x_xs prev_res_xs ()
        in
        Search.fold_right proc res_x Search.empty

  (** Return concatenated lazy list of all of the results from calling search on *some*
      element of rules.
   *)
  let results_exists (search : Rule.sequent list -> unit -> proof list search_result) (obligation : Rule.sequent)
      (heuristic : Rule.sequent list -> int) (log_result : action -> proof Search.t -> unit) (k : unit -> unit) (rules : proof Rule.t list) : proof search_result =
    Debug.debug_start "result_exists";
    let step rule : action option =
      match Rule.apply rule obligation with
      | None ->
        begin
          Debug.debug "failed rule %s" (Pp.string_of_x (Rule.pp_rule G.lookup_sym) rule);
          None
        end
      | Some { builder; premises = subgoals; tm_unif; params = _ } ->
        Debug.debug "succeeded rule %s \n with: %s" (Pp.string_of_x (Rule.pp_rule G.lookup_sym) rule) (Tm_unif.string_of_tm_unif G.lookup_sym tm_unif);
        let score = heuristic subgoals in
        Debug.debug "heuristic done";
        Some { score; rule; subgoals = subgoals; builder; tm_unif }
    in
    let next_states = List.sort (fun a b -> compare a.score b.score) (List.filter_map step rules) in
    Debug.debug "next states: %d" (List.length next_states);
    (* TODO did we get laziness right here? *)
     let res = fold_right_lazy (fun (action : action) prev_result ->
        Debug.debug "trying one possible rule...";
        let res : unit -> proof list search_result = search action.subgoals  in
        Debug.debug "rule search returned";
        let res' = begin fun () -> let search_result = Search.combine_unif action.tm_unif action.builder res () in
                                   log_result action search_result;
                                   search_result
                   end
                 in
        Debug.debug "combined added term unifications to result";
        Search.append res' prev_result ())
       next_states (fun () -> k (); Search.empty false) in
     Debug.debug_end (); res


  (** Search rules to find a derivation of a given goal that is no more than max_depth rules deep. *)
  let rec solve_sequent_limitk (max_depth : int) (heuristic : Rule.sequent list -> int) (log_result : Rule.sequent -> action -> proof Search.t -> unit) (k : unit -> unit)
      (obligation : Rule.sequent)
    : unit -> proof search_result =
    let obligation_str = (Pp.string_of_x (fun fmt -> (Rule.pp_sequent G.lookup_sym fmt)) obligation) in
    Debug.debug_start "Solving %s at max_depth %d%!" obligation_str max_depth;
    let new_k () = Debug.debug_end (); k () in
    begin if max_depth < 1 then
          (fun () -> new_k (); Search.empty true)
      else
        let some_rule_applies rules =
          results_exists (results_for_all (fun obligation' -> solve_sequent_limit (max_depth - 1) heuristic obligation' log_result))
                         obligation heuristic (log_result obligation) new_k rules in

        (* Right focus on atomic prop: does ID rule apply? *)
            let immediate =
              Debug.debug_start "immediate";
              let ({ uvars; assumptions; goal } : Rule.sequent) = obligation in
              let r = List.fold_right (fun (x, hyp) res ->
                let goal_unif = Rule.unify_goal uvars goal (Atomic hyp) in
                match goal_unif with
                | None -> res
                | Some unif ->
                  Search.cons { proof = Proof.pr_fvar x; tm_unif = unif.terms } res)
                assumptions (fun () -> Search.empty false) in Debug.debug_end (); r
        in
        let nonimmediate () =
          begin
            Debug.debug_start "nonimmediate";
            let r = some_rule_applies (Synthetics.get_rules obligation) in
            Debug.debug_end ();
            r
          end
        in
        Search.append immediate nonimmediate
    end
  and solve_sequent_limit (max_depth : int) (heuristic : Rule.sequent list -> int) (obligation : Rule.sequent)
                          (log_result : Rule.sequent -> action -> proof Search.t -> unit) : unit -> proof search_result =
    solve_sequent_limitk max_depth heuristic log_result (fun _ -> ()) obligation

  let solve_sequents_limit (max_depth : int) (heuristic : Rule.sequent list -> int)
                           (log_result : Rule.sequent -> action -> proof Search.t -> unit) : Rule.sequent list -> bool =
    List.for_all (fun obligation -> Search.is_success (solve_sequent_limit max_depth heuristic obligation log_result ()))

  (** Search rules to solve a given goal

      log_result lets you log the goal, action taken, and result each time the result of a nondeterministic choice is computed
   *)
  let solve_sequent (heuristic : Rule.sequent list -> int) (log_result : Rule.sequent -> action -> proof Search.t -> unit) (obligation : Rule.sequent)
        : proof solution option =
    let rec helper max_depth (acc : proof search_result) =
      if not (Search.is_success acc) then
        (if Search.has_more acc then
          begin Debug.debug "increasing depth to %d" max_depth;
          let search = solve_sequent_limit max_depth heuristic obligation log_result in
          Debug.debug "running search";
          let r = search () in
          Debug.debug "success: %s" (string_of_bool (Search.is_success r));
          helper (max_depth + 1) r
          end
        else
          begin Debug.debug "failing out";
          None end)
      else
        begin Debug.debug "success";
        Search.head acc end
    in
    helper 1 (Search.empty true)


  let rec mapM (f : 'a -> 'b option) (l : 'a list) : 'b list option =
    match l with
    | [] -> Some []
    | x::xs ->
      Debug.debug "begin process goal";
      Option.bind (f x) (fun vx ->
                          Debug.debug "processed goal";
                           Option.bind (mapM f xs) (fun vxs -> Some (vx::vxs)))

  (** Iterate through each proof obligation and check whether it unifies with a hypothesis
      or the conclusion of any rule *)
  let search_goals (heuristic : Rule.sequent list -> int) _ (log_result : logger) (goals : Rule.sequent list)
      : proof solution list option =
    Debug.debug "Goals: %d" (List.length goals);
    mapM (solve_sequent heuristic log_result) goals
