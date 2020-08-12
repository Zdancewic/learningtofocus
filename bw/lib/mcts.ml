
module type Strategy = sig
  type state
  type result

  type mctree =
    | Node of state * result ref * (mctree list ref)

  (** Pick a child of the given node to move to during the selection phase *)
  val select_child : mctree list -> mctree

  val fully_expanded : mctree -> bool

  val expand_child : state -> state list

  val simulate : state -> result


  (* Monoidal operators on result type *)
  val initial_result : result
  val append_result : result -> result -> result

end


module Make (STRATEGY:Strategy) = struct
  open STRATEGY

  let rec select (tree : mctree) : mctree =
    if fully_expanded tree then
      let Node (_, _, children) = tree in
      let next = select_child !children in
      select next
    else
      tree

  let expand (tree : mctree) : unit =
    let Node (state, _, children) = tree in
    let new_children = List.map (fun s -> Node (s, ref initial_result, ref [])) (expand_child state) in
    children := new_children @ !children

  (** After a node's result value has changed, call backprop with its ancestors
     to update their result values. *)
  let rec backprop (path : mctree list) : unit =
    match path with
    | [] -> ()
    | Node (_, result, children) :: path' ->
      let new_result = List.fold_left
          (fun r_acc (Node (_, r_child, _)) -> append_result !r_child r_acc)
          initial_result !children in
      result := new_result;
      backprop path'
end
