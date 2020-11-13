open Util
open Prop_rep
open Tm_rep

type prop = Pos of pprop | Neg of nprop

type tag = Left | Right

type 'a var =
  | Free of 'a
  | Bound of int

(** Patterns *)
type 'a ppat = 'a ppat_t Hashcons.hash_consed
and 'a ppat_t =
  | Pat_p_unit
  | Pat_p_inj of tag * 'a ppat
  | Pat_p_sigpair of 'a ppat
  | Pat_p_bvar of int

(** Co-patterns *)
type 'a npat = 'a npat_t Hashcons.hash_consed
and 'a npat_t =
  | Pat_n_proj of tag * ('a npat)
  | Pat_n_app of ('a ppat) * ('a npat)
  | Pat_n_piapp of ('a npat)
  | Pat_n_covar                         (* appears at the end of a stack *)

module PPatRep = struct
  type t = int ppat_t

  let equal _ _ : bool = false
  let hash _ : int = 0
end

module NPatRep = struct
  type t = int npat_t

  let equal _ _ : bool = false
  let hash _ : int = 0
end

type 'a proof_inv = 'a proof_inv_t Hashcons.hash_consed
and 'a proof_inv_t =
  | Pr_p_match  of ('a ppat -> 'a proof_inv) (* pattern match on the next variable *)
  | Pr_n_match  of ('a npat -> 'a proof_inv) (* co-pattern matching i.e. lambda i.e. matching on the current stack *)
  | Pr_p_rfoc   of 'a proof_value
  | Pr_n_lfoc   of 'a var * 'a proof_stack

and 'a proof_value = 'a proof_value_t Hashcons.hash_consed
and 'a proof_value_t =
  | Pr_value of ('a proof_inv) list * tm list * 'a ppat

and 'a proof_stack = 'a proof_stack_t Hashcons.hash_consed
and 'a proof_stack_t =
  | Pr_stack of ('a proof_inv) list * tm list * 'a proof_inv option * 'a npat


module ProofRep = struct
  type t = int proof_inv_t
  type proof = int proof_inv

  let equal _ _ : bool = false
  let hash _ : int = 0
end

module ValueRep = struct
  type t = int proof_value_t
  type value = int proof_value

  let equal _ _ : bool = false
  let hash _ : int = 0
end

module StackRep = struct
  type t = int proof_stack_t
  type stack = int proof_stack

  let equal _ _ : bool = false
  let hash _ : int = 0
end
