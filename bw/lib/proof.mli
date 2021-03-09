  open Proof_rep
  open Proof_rep.ProofRep
  open Proof_rep.ValueRep
  open Proof_rep.StackRep
  open Prop_rep
  open Tm_rep
  type ppat = Top.tag Proof_rep.ppat
  type npat = Top.tag Proof_rep.npat
  type stable_env = (int * nprop) list

  val pat_p_unit : ppat
  val pat_p_inj : tag -> ppat -> ppat
  val pat_p_sigpair : ppat -> ppat
  val pat_p_bvar : int -> ppat

  val pat_n_proj : tag -> npat -> npat
  val pat_n_app : ppat -> npat -> npat
  val pat_n_piapp : npat -> npat
  val pat_n_covar : npat

  val pr_p_match  : (ppat -> proof) -> proof (* pattern match on the next variable *)
  val pr_n_match  : (npat -> proof) -> proof (* co-pattern matching i.e. lambda or matching on the current stack *)
  val pr_p_rfoc   : value -> proof
  val pr_n_lfoc   : Top.tag Proof_rep.var -> stack -> proof

  (** Given a proof you know to be a co-pattern match and a co-pattern, get the corresponding branch. (Partial)*)
  val pr_n_match_exec : proof -> npat -> proof
  val pr_p_match_exec : proof -> ppat -> proof
  val pr_ex_falso : proof
  val pr_bvar     : int -> proof
  val pr_fvar     : int -> proof
  val pr_tt : proof


  (** Build a value out of a pattern and bindings for its free proof/term variables. *)
  val pr_value : proof list -> tm list -> ppat -> value

  val pr_value_unit : value
  val pr_value_shift : proof -> value

  val pr_stack_app : value -> stack -> stack
  val pr_stack_proj : tag -> stack -> stack
  val pr_stack_projL : stack -> stack
  val pr_stack_projR : stack -> stack
  val pr_stack_covar : stack
  val pr_stack_shift : proof -> stack

  val check       : stable_env -> pprop list -> proof -> nprop -> bool
  val check_value : stable_env -> pprop list -> value -> pprop -> bool
  val check_stack : stable_env -> pprop list -> stack -> nprop -> nprop -> bool

  val subst_tm_proof : (Top.tag * Tm_rep.tm) list -> proof -> proof
  val subst_tm_value : (Top.tag * Tm_rep.tm) list -> value -> value
  val subst_tm_stack : (Top.tag * Tm_rep.tm) list -> stack -> stack
