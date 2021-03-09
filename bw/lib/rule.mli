open Proof_rep

  type atomic_prop = Top.tag * Tm_rep.tm list
  type assumptions = (Top.tag * atomic_prop) list
  type goal =
    | Atomic of atomic_prop
    | Any

  type sequent = { uvars: Top.TagSet.t;
                   assumptions: assumptions;
                   goal: goal;
                 }
  type 'pf builder = ProofRep.proof list -> 'pf

  type 'pf t = {
    params : Top.TagSet.t  (* binder for the free variables of this rule *)
  ; uvars : Top.TagSet.t   (* unification variables created by this rule *)
  ; premises : sequent list   (* maybe a set? *)
  ; conclusion : goal
  ; builder : 'pf builder  (* builds a proof term given one proof for each premise *)
  }

  type 'pf app_result = { params : Top.TagSet.t; builder : 'pf builder; premises : sequent list; tm_unif : Tm_unif.t; }
  type prop_unification = goal Prop_unif.t

  val apply_unif_sequent : prop_unification -> sequent -> sequent
  val apply : 'pf t -> sequent -> 'pf app_result option

  val unify_goal : Top.TagSet.t -> goal -> goal -> prop_unification option


  (** Try to use a rule to prove a given sequent. Return a list of premises that
      need to be proven, or none if the rule doesn't apply. *)

  (* val apply_id : Top.TagSet.t -> sequent -> bool *)
  val instantiate : 'pf t -> (Tm_rep.tm list) -> 'pf t
  val string_of_sequent : (Top.tag -> string) -> sequent -> string
  val pp_sequent : (int -> string) -> Format.formatter -> sequent -> unit
  val pp_rule : (int -> string) -> Format.formatter -> 'pf t -> unit
  val pp_goal : (int -> string) -> Format.formatter -> goal -> unit
  val pp_atomic_prop : (int -> string) -> Format.formatter -> atomic_prop -> unit
