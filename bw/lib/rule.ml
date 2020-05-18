(* SYNTHETIC RULES & CONNECTIVES *)
(* A left rule:*)
(*
G ++ assumptions1[t1...tm] |- C1[t1...tm]  ...  G ++ assumptionsN[t1...tm] |- CN[t1...tm -> ]
-------------------------------------------------------------------------------------------(new ?X1...?Xk,a1..an) L1-rule
G, L1[t1...tm]  |- C

where C is either 'any' or q[t1...tm]
*)
open Format
open Tm_rep
open Util

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

  (** Try to use a rule to prove a given sequent. Return a list of premises that
      need to be proven, or none if the rule doesn't apply. *)
  val apply : t -> sequent -> (sequent list) option
  val apply_id : sequent -> bool
  val instantiate : t -> (Tm_rep.tm list) -> t
  val pp_sequent : (int -> string) -> Format.formatter -> sequent -> unit
  val pp_rule : (int -> string) -> Format.formatter -> t -> unit
  val pp_goal : (int -> string) -> Format.formatter -> goal -> unit
  val pp_atomic_prop : (int -> string) -> Format.formatter -> atomic_prop -> unit
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
    (** Any is a singleton metavariable that indicates the RHS of a rule can be
       instantiated in any way *)
    | Any

  type tm_unification = (Top.tag * tm) list
  type prop_unification = {
    any: goal option;
    terms: tm_unification;
  }


  let uni_empty : tm_unification = []
  let uni_single (t : Top.tag) (e : tm) : tm_unification =
    [(t, e)]
  let uni_combine (u1 : tm_unification) (u2 : tm_unification) : tm_unification option =
    List.fold_right
      (fun (tag, tm) ->
         function
         | None -> None
         | Some u ->
           if List.mem_assoc tag u then
             None
           else
             Some ((tag, tm) :: u))
      u2 (Some u1)

  let rec unify_terms (l1 : tm list) (l2 : tm list) : tm_unification option =
    List.fold_left2 (fun acc t1' t2' ->
        let t_uni_opt = (unify_term t1' t2') in
        begin match acc, t_uni_opt with
          | None, _ | _, None -> None
          | Some uni, Some t_uni -> uni_combine uni t_uni
        end)
      (Some uni_empty) l1 l2

  and unify_term (t1 : tm) (t2 : tm) : tm_unification option =
    match t1.Hashcons.node, t2.Hashcons.node with
    | Tm_uvar i, Tm_uvar j -> if i == j then Some uni_empty else None
    | t, Tm_param a | Tm_param a, t -> Some (uni_single a (Globals.HTm.hashcons (G.tm_table) t))
    | Tm_fun (f, l1), Tm_fun (g, l2) ->
      let uni_lists = unify_terms l1 l2 in
      if f == g then uni_lists else None
    | _, _ -> None

  let unify_atom atom1 atom2 : tm_unification option =
    let (tag1, args1) = atom1 in
    let (tag2, args2) = atom2 in
    if tag1 == tag2 then unify_terms args1 args2 else None

  let unify_goal (g1:goal) (g2:goal) : prop_unification option =
    begin match g1, g2 with
      | Any, g | g, Any -> Some { any = Some g; terms = uni_empty }
      | Atomic atom1, Atomic atom2 ->
        begin match unify_atom atom1 atom2 with
          | None -> None
          | Some tm_uni -> Some { any = None; terms = tm_uni }
        end
    end

  type sequent = assumptions * goal

  type substitution = (Top.tag * Tm_rep.tm) list

  type t = {
    params : Top.TagSet.t  (* binder for the free variables of this rule *)
  ; uvars : Top.TagSet.t   (* unification variables created by this rule *)
  ; premises : sequent list   (* maybe a set? *)
  ; conclusion : goal
  }

  let apply_id (sequent : sequent) : bool =
    let (assumptions, goal) = sequent in
    List.exists (fun hyp ->
        match unify_goal goal (Atomic hyp) with
        | Some _ -> true
        | None -> false) assumptions

  let rec apply_uni_tm (uni : tm_unification) (t : tm) : tm =
    match t.Hashcons.node with
    | Tm_param tag ->
      if List.mem_assoc tag uni then
        List.assoc tag uni
      else t
    | Tm_fun (tag, args) ->
      (* TODO could tag be in domain of uni??? *)
      TMS.tm_fun tag (List.map (apply_uni_tm uni) args)
    | _ -> t

  and apply_uni_sequent (uni : prop_unification) ((lhs, rhs) : sequent) : sequent =
    ((List.map (apply_uni_atomic uni.terms) lhs), apply_uni_goal uni rhs)

  and apply_uni_atomic (uni : tm_unification) ((tag, args) : atomic_prop) : atomic_prop =
    (tag, List.map (apply_uni_tm uni) args)

  and apply_uni_goal ({any; terms} : prop_unification) : goal -> goal =
    function
    | Any ->
      begin match any with
      | None -> Any
      | Some g -> g
      end
    | Atomic atom -> Atomic (apply_uni_atomic terms atom)

  (** Add some given assumptions to the sequent's LHS *)
  let weaken_sequent (assumptions : assumptions) ((lhs, rhs) : sequent) : sequent =
    (assumptions @ lhs, rhs)

  let apply (rule : t) (obligation : sequent) : (sequent list) option =
    let (assumptions, goal) = obligation in
    let {premises; conclusion;params=_;uvars=_} = rule in
    begin match unify_goal goal conclusion with
      | Some uni ->
        let premises_weakened : sequent list = List.map (weaken_sequent assumptions) premises in
        (* TODO make sure that concatenating the rule's premise's assumptions
                with the goal's assumptions is the correct things to do here. *)
        let premises_unified = List.map (apply_uni_sequent uni) premises_weakened in
        Some premises_unified
      | None -> None
    end


  let msubst_tap   (m : substitution) (id, ts) : atomic_prop =
    (id, List.map (TMS.msubst_tt m) ts)
  let msubst_tassm (m : substitution) : assumptions -> assumptions =
    List.map (msubst_tap m)
  let msubst_tg    (m : substitution) : goal -> goal = function
    | Atomic ap -> Atomic (msubst_tap m ap)
    | Any -> Any

(* Modify this to take the unification context into account *)
(* Note that the order of the parameters to a synthatic connective is determined by the *)
(* order of the Top.tags of its free parameters *)
let instantiate (r : t) (ts : Tm_rep.tm list) =
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
