open Proof_rep.ProofRep

  type 'a solution
  type action = {
    score : int;
    rule : proof Rule.t;
    subgoals : Rule.sequent list;
    builder : proof Rule.builder;
    tm_unif : Tm_unif.t
  }
  type logger = Rule.sequent -> action -> proof Search.t -> unit

  (* val solve_sequent_limit : int -> (sequent list -> int) -> sequent -> search_result *)
  val solve_sequents_limit : int -> (Rule.sequent list -> int) -> logger -> Rule.sequent list -> bool
  val solve_sequent : (Rule.sequent list -> int) -> logger -> Rule.sequent -> proof solution option
  val search_goals : (Rule.sequent list -> int) -> Top.TagSet.t -> logger -> Rule.sequent list -> proof solution list option
