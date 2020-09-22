module type S = sig
  type t
  type solution
  type seq = unit -> t

  val is_success : t -> bool
  val append : seq -> seq -> seq
  val cons : solution -> seq -> seq
  val fold_right : (solution -> (unit -> 'r) -> 'r) -> t -> (bool -> 'r) -> 'r
  val filter_map : (solution -> solution option) -> seq -> seq

  val empty : bool -> t
  val trivial : t

  val has_more : t -> bool
end
module Make (RULES : Rule.S) : S with type solution := RULES.tm_unification = struct
  type solution = RULES.tm_unification

  type node =
    | Nil of bool
    | Cons of solution * seq
  and seq = unit -> node


  type t = node

  let is_success (result : t) : bool =
    match result with
    | Nil _ -> false
    | _ -> true

  (** Some b indicates whether a deeper search might have found more solutions; None means that the search is not complete but so far it has been exhaustive. *)
  let has_more (result : t) : bool =
    match result with
    | Nil more -> more
    | _ -> failwith "Incomplete search."

  let rec map_result (f : bool -> bool) (s : seq) : seq =
    fun () ->
      match s () with
      | Nil more -> Nil (f more)
      | Cons (soln, rest) -> Cons (soln, map_result f rest)

  let rec fold_right (f : solution -> (unit -> 'r) -> 'r) (node : t) (init : bool -> 'r) : 'r =
      match node with
      | Nil more -> init more
      | Cons (soln, rest) -> f soln (fun () -> fold_right f (rest ()) init)

  let rec filter_map (f : solution -> solution option) (s : seq) : seq =
    fun () ->
      match s () with
      | Cons (soln, rest) ->
        begin match f soln with
          | Some soln' -> Cons (soln', filter_map f rest)
          | None -> filter_map f rest ()
        end
      | node -> node

  let rec append (seq1 : seq) (seq2 : seq) : seq =
    fun () ->
      match seq1 () with
      | Nil true -> map_result (fun _ -> true) seq2 ()
      | Nil false -> seq2 ()
      | Cons (soln, rest) ->
        Cons (soln, (append rest seq2))

  let cons (soln : solution) (s : seq) : seq =
    fun () ->
      Cons (soln, s)

  let single soln more : t =  Cons (soln, fun () -> Nil more)
  (* A search which found nothing. *)
  let empty more : t = Nil more
  (* A search which found a single trivial solution. *)
  let trivial : t = single RULES.unif_empty false
end
