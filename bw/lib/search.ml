module G = Globals.G
  type tm_unification = Tm_unif.t
  type 'proof solution = { proof : 'proof; tm_unif : tm_unification }

  type 'proof node =
    | Nil of bool
    | Cons of 'proof solution * 'proof seq
  and 'proof seq = unit -> 'proof node


  type 'a t = 'a node

  let is_success (result : 'a t) : bool =
    match result with
    | Nil _ -> false
    | _ -> true

  let head (res : 'proof t) : ('proof solution) option =
    match res with
    | Nil _ -> None
    | Cons (soln, _) -> Some soln

  (** Some b indicates whether a deeper search might have found more solutions; None means that the search is not complete but so far it has been exhaustive. *)
  let has_more (result : 'a t) : bool =
    match result with
    | Nil more -> more
    | _ -> failwith "Incomplete search."

  let rec map_result (f : bool -> bool) (s : 'a seq) : 'a seq =
    fun () ->
      match s () with
      | Nil more -> Nil (f more)
      | Cons (soln, rest) -> Cons (soln, map_result f rest)

  let rec fold_right (f : 'a solution -> (unit -> 'r) -> 'r) (node : 'a t) (init : bool -> 'r) : 'r =
      match node with
      | Nil more -> init more
      | Cons (soln, rest) -> f soln (fun () -> fold_right f (rest ()) init)

  let rec filter_map : 'a 'b. ('a solution -> 'b solution option) -> ('a seq) -> 'b seq =
    fun f s () ->
      match s () with
      | Cons (soln, rest) ->
        begin match f soln with
          | Some soln' -> Cons (soln', filter_map f rest)
          | None -> filter_map f rest ()
        end
      | Nil b -> Nil b

  let map f s = filter_map (fun x -> Some (f x)) s

  let build (builder : 'a -> 'b) (s : 'a seq) : 'b seq =
    map (fun {proof; tm_unif} -> {proof = builder proof; tm_unif}) s


  (** Take a new search result s and combine tm_unif with all of the result's unifications,
      applying all unifications in s to tm_unif's range.
      f provides a modification to apply to proof terms *)
  let combine_unif (tm_unif : tm_unification) (f : 'a -> 'b) (s : 'a seq) : 'b seq =
     map  (fun { proof; tm_unif = tm_unif' } ->
                   Debug.debug "combining %s with %s" (Tm_unif.string_of_tm_unif G.lookup_sym tm_unif) (Tm_unif.string_of_tm_unif G.lookup_sym tm_unif');
                   begin match Tm_unif.combine tm_unif tm_unif' with
                   | Some tm_unif'' ->
                     Debug.debug "combine succeeded: %s" (Tm_unif.string_of_tm_unif G.lookup_sym tm_unif'');
                     { proof = f proof
                     ; tm_unif = tm_unif''
                     }
                   | None -> failwith "combine_unif: domain of tm_unif should be disjoint from unifications in s\n"
                   end) s

  let rec append (seq1 : 'a seq) (seq2 : 'a seq) : 'a seq =
    fun () ->
      begin match seq1 () with
      | Nil true -> map_result (fun _ -> true) seq2 ()
      | Nil false -> seq2 ()
      | Cons (soln, rest) ->
        Cons (soln, append rest seq2)
      end

  let cons (soln : 'a solution) (s : 'a seq) : 'a seq =
    fun () ->
      Cons (soln, s)

  let single soln more : 'a t = Cons (soln, fun () -> Nil more)
  (* A search which found nothing. *)
  let empty more : 'a t = Nil more
  (* A search which found a single trivial solution. *)
  let trivial proof : 'a t = single { proof; tm_unif = Tm_unif.empty} false
