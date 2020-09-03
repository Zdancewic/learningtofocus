
module type Strategy = sig
  type state
  type result

  type mctree = {
    state : state;
    mutable result : result;
    mutable expanded : bool;
    mutable children : mctree list
  }

  (** Pick a child of the given node to move to during the selection phase *)
  val select_child : mctree -> mctree

  (** Expand that child! *)
  val expand_child : state -> state list

  (** Run a playout from the given state *)
  val simulate : state -> result


  (* Monoidal operators on result type *)
  val initial_result : result
  val append_result : result -> result -> result

end

module RuleStrategy (RULES:Rule.S)
    (SYNTH : Synthetics.S with type rule := RULES.t and type sequent := RULES.sequent)
    (PROVER : Prover.S with type sequent := RULES.sequent and type tm_unification := RULES.tm_unification) : Strategy = struct

  open RULES
  open SYNTH

  type state = sequent list

  type result = { games : int; wins : int }
  let initial_result = { games = 0; wins = 0 }
  let append_result r1 r2 = { games = r1.games + r2.games; wins = r1.games + r2.games }

  type mctree = {
    state : state;
    mutable result : result;
    mutable expanded : bool;
    mutable children : mctree list
  }

  let explore_bias = sqrt 2.0

  let ucb1 (wins : int) (games : int) (parent_games : int) : float =
    let exploitation = (float_of_int wins) /. (float_of_int games) in
    let exploration = explore_bias *. sqrt ((log (float_of_int parent_games)) /. (float_of_int games)) in
    exploitation +. exploration

  let select_child (tree : mctree) : mctree =
    let parent_games = tree.result.games in

    (* Find the child of tree with the highest UCB1 value *)
    let best_child_opt = List.fold_left (fun acc child ->
        let { games = child_games; wins = child_wins} = child.result in
        let child_ucb = ucb1 child_wins child_games parent_games in
        begin match acc with
          | Some (max_ucb, best_child) ->
            if child_ucb > max_ucb then
              Some (child_ucb, child)
            else
              Some (max_ucb, best_child)
          | None -> Some (child_ucb, child)
        end) None tree.children in

    match best_child_opt with
    | Some (_, next_child) -> next_child
    | None -> tree (* tree has no children *)

  let step (obligation : sequent) : state list =
    let rule_applies rule : state option =
      begin match RULES.apply rule obligation with
        | None -> None
        | Some (subgoals, _) ->
          Some subgoals
      end
    in
    List.fold_right (fun (rule : RULES.t) states ->
        match rule_applies rule with
        | None -> states
        | Some new_state -> new_state :: states) (get_rules obligation) []

  let expand_child : state -> state list = function
    | [] -> []
    | obligation :: rest ->
      List.map (fun (obligations : state) -> List.append obligations rest) (step obligation)

  (** TODO Run a playout from the given state *)
  let simulate (obligations : state) : result =
    let result = PROVER.solve_sequents_limit 10 List.length obligations in
    let wins = if result then 1 else 0 in
    { games = 1; wins }
end

module Make (STRATEGY:Strategy) = struct
  open STRATEGY

  let select (tree : mctree) : mctree list =
    let rec sel tree path =
      if tree.expanded then
        let next = select_child tree in
        sel next (tree :: path)
      else
        tree :: path
    in
    sel tree []

  let expand (tree : mctree) : unit =
    if tree.expanded then
      failwith "node already expanded"
    else
      let make_child state = {state; result = initial_result; expanded = false; children = []} in
      let new_children = List.map make_child (expand_child tree.state) in
      tree.expanded <- true;
      tree.children <- new_children

  (** After a node's result value has changed, call backprop with its ancestors
     to update their result values. *)
  let rec backprop (path : mctree list) : unit =
    match path with
    | [] -> ()
    | tree :: path' ->
      let new_result = List.fold_left
          (fun r_acc { result = r_child; _ } -> append_result r_child r_acc)
          initial_result tree.children in
      tree.result <- new_result;
      backprop path'

  (** Run one round of MCTS, mutating the values in the tree. *)
  let search_round (tree : mctree) : unit =
    (* Choose element of list at random *)
    let pick l = List.nth l (Random.int (List.length l)) in
    let path = select tree in
    match path with
    | leaf :: _ ->
      expand leaf;
      let child = pick leaf.children in
      child.result <- simulate child.state;
      backprop path
    | [] -> failwith "selection failed"
end
