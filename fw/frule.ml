(* SYNTHETIC RULES & CONNECTIVES *)
(* A left rule:*)
(* 
G ++ assumptions1[t1...tm] |- C1[t1...tm]  ...  G ++ assumptionsN[t1...tm] |- CN[t1...tm -> ]
-------------------------------------------------------------------------------------------(new ?X1...?Xk,a1..an) L1-rule
G, L1[t1...tm]  |- C

where C is either 'any' or q[t1...tm] 
*)
open Format

module OrderedSProp = struct
  type t = Fprop_rep.s_prop
  let compare i j = i.Hashcons.tag - j.Hashcons.tag
end

module AssumpSet = Set.Make(OrderedSProp)

type assumptions = AssumpSet.t

type goal = Fprop_rep.s_prop
		(*| Normal of Fprop_rep.s_prop
		| Any*)  
type sequent = AssumpSet.t * goal

type t = {
		    params : Ftop.TagSet.t (* binder for the free variables of this rule *)
		    (* uvars : Ftop.TagSet.t   unification variables created by this rule *)
			; premises : sequent list (* maybe a set? *)
			; conclusion : sequent
		}



module OrderedSeq = struct
   type t = sequent
   let compare (a1, g1) (a2, g2) =
   if (AssumpSet.equal a1 a2 = false) then AssumpSet.compare a1 a2
   else
   g1.Hashcons.tag - g2.Hashcons.tag
end 

module SeqSet : (Set.S with type elt = OrderedSeq.t) = Set.Make(OrderedSeq)

module type S = sig
	(* Atomic propositions can either be: *)
	(*   - a primitive proposition instantiated at some terms, or *)
	(*   - the Ftop.tag identifying a synthetic formula instantiated at some terms *)
	(* Both have the same structure, making unification easier. *)
	(* type atomic_prop = Ftop.tag * Ftm_rep.tm list *)
	(* type assumptions = Fprop_rep.s_prop list *)
        type assumptions = AssumpSet.t
	     (* arises from the left rule for false *)
	type goal = Fprop_rep.s_prop
	  (*| Normal of Fprop_rep.s_prop
	  | Any *) 
	type sequent  = AssumpSet.t * goal
	
	type t = {
		    params : Ftop.TagSet.t (* binder for the free variables of this rule *)
		    (* uvars : Ftop.TagSet.t   unification variables created by this rule *)
			; premises : sequent list (*sequent list*) (* maybe a set? *)
			; conclusion : sequent
		}
	
        (* val instantiate : t -> (Ftm_rep.tm list) -> t *)
	 val pp_sequent : (int -> string) -> Format.formatter -> sequent -> unit
	 val pp_rule : (int -> string) -> Format.formatter -> t -> unit
         val compare_seq : sequent -> sequent -> int
end

module Make(G:Fglobals.T)(TMS:Ftm.S) : S  = struct

	(* Atomic propositions can either be: *)
	(*   - a primitive proposition instantiated at some terms, or *)
	(*   - the Ftop.tag identifying a synthetic formula instantiated at some terms *)
	(* Both have the same structure, making unification easier. *)
	(*type atomic_prop = Ftop.tag * Ftm_rep.tm list  *)
	(* type assumptions = atomic_prop list *)
	(* type assumptions = Fprop_rep.s_prop list *)
	type assumptions = AssumpSet.t
	type goal  = Fprop_rep.s_prop
		(*| Normal of Fprop_rep.s_prop
		| Any*)  
	
	type sequent = AssumpSet.t * goal
	      
	type t = {
		    params : Ftop.TagSet.t  (* binder for the free variables of this rule *)
		 (* ; uvars : Ftop.TagSet.t   unification variables created by this rule *)
			; premises : sequent list (*sequent list*) (* maybe a set? *)
			; conclusion : sequent
		}


(* Unification maps must keep track of the 'time stamp' of when the variable was generated *)
(* compare the parameter's Ftop.tag to prevent illegal instances. *)

(* A rule schema is a function from a list of terms to a rule *)
(* given an *instance* of a synthetic connective L1[t1,...,tm] *)
(* and a rule schema L1_rule : (tm list) -> rule *)
(* the instance is given by L1_rule [t1,...,tn] *)

(*
G ++ assumptions1[t1...tm] |- C1[tm...tm] ... G ++ assumptionsN[t1...tm] |- CN[t1...tm]
----------------------------------------------------------------------------------------- R1-rule
G |- R1[t1...tm]
*)


(*   $(%ZERO & Ftop) -> p(x,y,z) *)
(*   (%ZERO & Ftop) is a synthetic connective *)
(*                                            *)
(* ---------------                            *)
(* G ++ L1[] |- X?                            *)

let pp_goal st fmt g =
	(*match g with*) 
		(*| Normal sp ->*) Fpp.pp_sprop_aux st fmt 0 (g.Hashcons.node)
		(*| Any -> pp_print_string fmt "Any"*)

let pp_sequent st fmt (assms, g) =
	let _ = pp_open_hovbox fmt 0 in
	let _ = Fpp.pp_list_aux fmt "," (Fpp.pp_sprop_aux st fmt 0) (List.map (fun j -> j.Hashcons.node) (AssumpSet.elements assms)) in
	let _ = pp_print_string fmt " |- " in
	let _ = pp_goal st fmt g in
	let _ = pp_close_box fmt () in
	()
	
let pp_rule st fmt {params = p; (*uvars = u; *) premises = prems; conclusion = c} =
	let pps = pp_print_string fmt in
	begin
		pp_print_flush fmt ();
		pp_open_hovbox fmt 0;
		pps "[";
		Fpp.pp_list_aux fmt "," (fun i -> pps ("x_" ^ (string_of_int i))) (Ftop.TagSet.elements p);
		pps "]" (*
		Fpp.pp_list_aux fmt "," (fun i -> pps ("x_" ^ (string_of_int i))) (Ftop.TagSet.elements u);
		pps "]"*); pp_force_newline fmt ();
		Fpp.pp_list_aux fmt " " (fun j -> (pp_sequent st fmt j))  prems;
	       (* SeqSet.iter (fun j-> (pp_sequent1 st fmt j;  
						 						   pp_print_string fmt " ";
						   pp_close_box fmt ();
						   pp_print_space fmt ())) (prems);*)
		pp_force_newline fmt ();
		pps "----------------------------------";
		pp_force_newline fmt ();
		pp_sequent st fmt c; 
                pp_force_newline fmt ()
	end

let compare_seq (a1, g1) (a2, g2) =
   if (AssumpSet.equal a1 a2 = false) then AssumpSet.compare a1 a2
   else
     g1.Hashcons.tag - g2.Hashcons.tag


end
