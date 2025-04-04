open Core
open Util

module HTm = Hashcons.Make(Tm_rep)
module PProp = Hashcons.Make(Prop_rep.PPropRep)
module NProp = Hashcons.Make(Prop_rep.NPropRep)
module PPat = Hashcons.Make(Proof_rep.PPatRep)
module NPat = Hashcons.Make(Proof_rep.NPatRep)
module HProof = Hashcons.Make (Proof_rep.ProofRep)
module PValue = Hashcons.Make (Proof_rep.ValueRep)
module NStack = Hashcons.Make (Proof_rep.StackRep)

module type T =
sig
  type tm_t = HTm.t
  val tm_table : tm_t

  type ppat_t = PPat.t
  val ppat_table : ppat_t

  type npat_t = NPat.t
  val npat_table : npat_t

  type pprop_t = PProp.t
  val pprop_table : pprop_t

  type nprop_t = NProp.t
  val nprop_table : nprop_t

  type proof_t = HProof.t
  val proof_table : proof_t

  type value_t = PValue.t
  val value_table : value_t

  type stack_t = NStack.t
  val stack_table : stack_t

  type sym_t = (int, (string * int)) Hashtbl.t
  val sym_table : sym_t
  val gen_sym : string -> int     (* creates a new symbol or returns and existing one *)
  val lookup_sym : int -> string  (* maps a tag generated by gen_sym to the string *)

  val gen_tag : unit -> Top.tag   (* creates a globally unique identifier *)
end

