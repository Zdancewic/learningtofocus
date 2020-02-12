(* SYNTHETIC RULES & CONNECTIVES *)
(* A left rule:*)
(* 
G ++ assumptions1[t1...tm] |- C1[t1...tm]  ...  G ++ assumptionsN[t1...tm] |- CN[t1...tm -> ]
-------------------------------------------------------------------------------------------(new ?X1...?Xk,a1..an) L1-rule
G, L1[t1...tm]  |- C

where C is either 'any' or q[t1...tm] 
*)
open Format

module type S = sig
	(* Atomic propositions can either be: *)
	(*   - a primitive proposition instantiated at some terms, or *)
	(*   - the Top.tag identifying a synthetic formula instantiated at some terms *)
	(* Both have the same structure, making unification easier. *)
	type atomic_prop = Top.tag * Tm_rep.tm list  
	type assumptions = atomic_prop list
	type goal = 
		| Atomic of atomic_prop
		| Any       (* arises from the left rule for false *)
	
	type sequent = assumptions * goal
	
	type t = {
		    params : Top.TagSet.t  (* binder for the free variables of this rule *)
		  ; uvars : Top.TagSet.t   (* unification variables created by this rule *)
			; premises : sequent list   (* maybe a set? *)
			; conclusion : goal
		}
	
   val instantiate : t -> (Tm_rep.tm list) -> t
	 val pp_sequent : (int -> string) -> Format.formatter -> sequent -> unit
	 val pp_rule : (int -> string) -> Format.formatter -> t -> unit
end

module Make(G:Globals.T)(TMS:Tm.S) : S  = struct

	(* Atomic propositions can either be: *)
	(*   - a primitive proposition instantiated at some terms, or *)
	(*   - the Top.tag identifying a synthetic formula instantiated at some terms *)
	(* Both have the same structure, making unification easier. *)
	type atomic_prop = Top.tag * Tm_rep.tm list  
	type assumptions = atomic_prop list
	type goal = 
		| Atomic of atomic_prop
		| Any       (* arises from the left rule for false *)
	
	type sequent = assumptions * goal
	
	type t = {
		    params : Top.TagSet.t  (* binder for the free variables of this rule *)
		  ; uvars : Top.TagSet.t   (* unification variables created by this rule *)
			; premises : sequent list   (* maybe a set? *)
			; conclusion : goal
		}
	


let msubst_tap m (id, ts) = (id, List.map (TMS.msubst_tt m) ts)
let msubst_tassm m aps = List.map (msubst_tap m) aps
let msubst_tg m g =
	match g with
		| Atomic ap -> Atomic (msubst_tap m ap)
		| Any -> Any

(* Modify this to take the unification context into account *)
(* Note that the order of the parameters to a synthatic connective is determined by the *)
(* order of the Top.tags of its free parameters *)
let instantiate r ts =
	let m = List.combine (Top.TagSet.elements r.params) ts in
	{params = Top.TagSet.empty;
	 uvars = r.uvars;  (* Need to generate new unification 'frame' and open the premises and conlusions with  that too *)
	                   (* perhaps this can be combined into a single msubst? *)
	 premises = List.map (fun (assms, goal) -> (msubst_tassm m assms, msubst_tg m goal)) r.premises;
	 conclusion = msubst_tg m r.conclusion
	} 


(* Unification maps must keep track of the 'time stamp' of when the variable was generated *)
(* compare the parameter's Top.tag to prevent illegal instances. *)

(* A rule schema is a function from a list of terms to a rule *)
(* given an *instance* of a synthetic connective L1[t1,...,tm] *)
(* and a rule schema L1_rule : (tm list) -> rule *)
(* the instance is given by L1_rule [t1,...,tn] *)

(*
G ++ assumptions1[t1...tm] |- C1[tm...tm] ... G ++ assumptionsN[t1...tm] |- CN[t1...tm]
----------------------------------------------------------------------------------------- R1-rule
G |- R1[t1...tm]
*)


(*   $(%ZERO & Top) -> p(x,y,z) *)
(*   (%ZERO & Top) is a synthetic connective *)
(*                                            *)
(* ---------------                            *)
(* G ++ L1[] |- X?                            *)

let pp_atomic_prop st fmt (tag, ts) =
	let _ = pp_print_string fmt (G.lookup_sym tag) in
	let _ = pp_print_string fmt "[" in
	let _ = Pp.pp_list_aux fmt "," (Pp.pp_tm_aux st fmt 0) ts in
	let _ = pp_print_string fmt "]" in
(*	let _ = pp_synth_defn st fmt tag in *)
	()

let pp_goal st fmt g =
	match g with 
		| Atomic a -> pp_atomic_prop st fmt a
		| Any -> pp_print_string fmt "Any"

let pp_sequent st fmt (assms, g) =
	let _ = pp_open_hovbox fmt 0 in
	let _ = Pp.pp_list_aux fmt "," (pp_atomic_prop st fmt) assms in
	let _ = pp_print_string fmt " |- " in
	let _ = pp_goal st fmt g in
	let _ = pp_close_box fmt () in
	()
	
let pp_rule st fmt {params = p; uvars = u; premises = prems; conclusion = c} =
	let pps = pp_print_string fmt in
	begin
		pp_print_flush fmt ();
		pp_open_hovbox fmt 0;
		pps "[";
		Pp.pp_list_aux fmt "," (fun i -> pps ("x_" ^ (string_of_int i))) (Top.TagSet.elements p);
		pps "] [";
		Pp.pp_list_aux fmt "," (fun i -> pps ("x_" ^ (string_of_int i))) (Top.TagSet.elements u);
		pps "]"; pp_force_newline fmt ();
		Pp.pp_list_aux fmt " " (fun j -> (pp_sequent st fmt j; pp_print_cut fmt ())) prems;
		pp_force_newline fmt ();
		pps "----------------------------------";
		pp_force_newline fmt ();
		pp_goal st fmt c;
		pp_force_newline fmt ()
	end


end