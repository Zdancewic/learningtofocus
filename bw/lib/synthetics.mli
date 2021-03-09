open Core
open Prop_rep
open Proof_rep.ProofRep
open Proof_rep.StackRep
open Proof_rep.ValueRep

  type lrule = stack Rule.t
  type rrule = value Rule.t
  type lrule_table = lrule list Int.Table.t
  type rrule_table = rrule list Int.Table.t

  val lfoc_rules : lrule_table
  val rfoc_rules : rrule_table
  val get_rules : Rule.sequent -> proof Rule.t list

  val make_synthetics : pprop list -> nprop -> Top.TagSet.t * Rule.sequent list
