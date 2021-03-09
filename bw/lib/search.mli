  type 'a t
  type 'proof solution = { proof : 'proof; tm_unif : Tm_unif.t }

  type 'a seq = unit -> 'a t

  val is_success : 'a t -> bool
  val append : 'a seq -> 'a seq -> 'a seq

  val cons : 'a solution -> 'a seq -> 'a seq
  val fold_right : ('a solution -> (unit -> 'r) -> 'r) -> 'a t -> (bool -> 'r) -> 'r
  val head : 'proof t -> ('proof solution) option

  val filter_map : ('a solution -> 'b solution option) -> 'a seq -> 'b seq
  val build : ('a -> 'b) -> 'a seq -> 'b seq

  val combine_unif : Tm_unif.t -> ('a -> 'b) -> 'a seq -> 'b seq

  val empty : bool -> 'a t
  val trivial : 'a -> 'a t

  val has_more : 'a t -> bool
