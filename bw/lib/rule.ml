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
open Proof_rep
module G = Globals.G

(* Atomic propositions can either be: *)
(*   - a primitive proposition instantiated at some terms, or *)
(*   - the Top.tag identifying a synthetic formula instantiated at some terms *)
(* Both have the same structure, making unification easier. *)
(* Both assumptions and goal are already synthetic *)
type atomic_prop = Top.tag * Tm_rep.tm list
type assumptions = (Top.tag * atomic_prop) list
type goal =
  | Atomic of atomic_prop
  | Any       (* arises from the left rule for false *)

type proof = ProofRep.proof


type sequent = { uvars: Top.TagSet.t;
                   assumptions: assumptions;
                   goal: goal;
                 }

type substitution = (Top.tag * Tm_rep.tm) list
type 'pf builder = proof list -> 'pf

type 'pf t = {
    params : Top.TagSet.t  (* binder for the free variables of this rule *)
  ; uvars : Top.TagSet.t   (* unification variables created by this rule *)
  ; premises : sequent list   (* maybe a set? *)
  ; conclusion : goal
  ; builder : 'pf builder (* builds a proof term given one proof for each premise *)
  }

  type prop_unification = goal Prop_unif.t
  type tm_unification = Tm_unif.t

  let rec unify_terms uvars (l1 : tm list) (l2 : tm list) : tm_unification option =
    List.fold_left2 (fun acc t1' t2' ->
        let t_unif_opt = unify_term uvars t1' t2' in
        begin match acc, t_unif_opt with
          | None, _ | _, None ->
             begin
               Debug.debug "unify_terms failed";
               None
             end
          | Some unif, Some t_unif -> Tm_unif.combine unif t_unif
        end)
      (Some Tm_unif.empty) l1 l2

  and unify_term uvars (t1 : tm) (t2 : tm) : tm_unification option =
    match t1.Hashcons.node, t2.Hashcons.node with
    | Tm_bvar i, Tm_bvar j when i == j ->
      Some Tm_unif.empty
    | Tm_fvar a, t
      when Top.TagSet.mem a uvars ->
      Some (Tm_unif.single a (Globals.HTm.hashcons (G.tm_table) t))
    | t, Tm_fvar a
      when Top.TagSet.mem a uvars ->
      Some (Tm_unif.single a (Globals.HTm.hashcons (G.tm_table) t))
    | Tm_fvar a, Tm_fvar b
      when a == b ->
      Some Tm_unif.empty
    | Tm_fun (f, l1), Tm_fun (g, l2) when f == g ->
      unify_terms uvars l1 l2
    | _, _ ->
      (Debug.debug "unfy_term failed %s / %s (u: %s)" (Pp.string_of_tm G.lookup_sym t1) (Pp.string_of_tm G.lookup_sym t2)
          (Pp.string_of_x (fun fmt -> Pp.pp_list_aux fmt "," (fun t -> pp_print_string fmt (string_of_int t))) (Top.TagSet.elements uvars));
      None)

  let unify_atom uvars atom1 atom2 : tm_unification option =
    let (tag1, args1) = atom1 in
    let (tag2, args2) = atom2 in
    if tag1 == tag2 then
      unify_terms uvars args1 args2
    else begin
      Debug.debug "unfy_atom failed %s / %s" (G.lookup_sym tag1) (G.lookup_sym tag2);
      None
    end

  let unify_goal (uvars : Top.TagSet.t)(g1:goal) (g2:goal) : prop_unification option =
    begin match g1, g2 with
      | Any, g | g, Any -> Some { any = Some g; terms = Tm_unif.empty }
      | Atomic atom1, Atomic atom2 ->
        begin match unify_atom uvars atom1 atom2 with
          | None -> None
          | Some tm_uni -> Some { any = None; terms = tm_uni }
        end
    end

  (* let apply_id uvars (sequent : sequent) : bool =
   *   let {assumptions; goal} = sequent in
   *   List.exists (fun (_, hyp) ->
   *       match unify_goal uvars goal (Atomic hyp) with
   *       | Some _ -> true
   *       | None -> false) assumptions *)


  let rec apply_unif_sequent (uni : prop_unification) ({uvars; assumptions; goal} : sequent) : sequent =
    { uvars = Top.TagSet.diff uvars (Tm_unif.domain uni.terms);
      assumptions = (List.map (fun (x, hyp) -> (x, (apply_unif_atomic uni.terms hyp))) assumptions);
      goal = apply_unif_goal uni goal
    }

  and apply_unif_atomic (uni : tm_unification) ((tag, args) : atomic_prop) : atomic_prop =
    (tag, List.map (Tm_unif.apply uni) args)

  and apply_unif_goal ({any; terms} : prop_unification) : goal -> goal =
    function
    | Any ->
      begin match any with
      | None -> Any
      | Some g -> g
      end
    | Atomic atom -> Atomic (apply_unif_atomic terms atom)

  (** Add some given assumptions to the sequent's LHS *)
  let weaken_sequent (assumptions : assumptions) ({ uvars; assumptions = lhs; goal} : sequent) : sequent =
    {uvars; assumptions = assumptions @ lhs; goal}

  type 'pf app_result = { params   : Top.TagSet.t;
                          builder  : 'pf builder;
                          premises : sequent list;
                          tm_unif  : tm_unification; }

  let msubst_tap   (m : substitution) (id, ts) : atomic_prop =
    (id, List.map (Tm.msubst_tt m) ts)
  let msubst_tassm (m : substitution) : assumptions -> assumptions =
    List.map (fun (x, hyp) -> (x, msubst_tap m hyp))
  let msubst_tg    (m : substitution) : goal -> goal = function
    | Atomic ap -> Atomic (msubst_tap m ap)
    | Any -> Any

(* Modify this to take the unification context into account *)
(* Note that the order of the parameters to a synthatic connective is determined by the *)
(* order of the Top.tags of its free parameters *)
let instantiate (r : 'pf t) (ts : Tm_rep.tm list) =
  let old_uvars_set = r.uvars in
  let old_uvars = Top.TagSet.elements old_uvars_set in
  let new_uvars = List.map (fun _ -> G.gen_tag ()) old_uvars in
  let new_uvars_set = Top.TagSet.of_list new_uvars in
	let m = List.append (List.combine (Top.TagSet.elements r.params) ts)
                      (List.combine old_uvars (List.map Tm.tm_fvar new_uvars)) in
	{ params = Top.TagSet.empty;
	  uvars = new_uvars_set;
	  premises = List.map (fun {uvars; assumptions; goal} ->
                         { uvars = Top.TagSet.union (Top.TagSet.diff uvars old_uvars_set) new_uvars_set;
                           assumptions = msubst_tassm m assumptions;
                           goal = msubst_tg m goal
                         }) r.premises;
	  conclusion = msubst_tg m r.conclusion;
    builder = r.builder;
	}


let apply (rule : 'pf t) (obligation : sequent) : 'pf app_result option =
    let new_params = Top.TagSet.map (fun _ -> G.gen_tag ()) rule.params in
    let rule' = instantiate rule (List.map Tm.tm_fvar (Top.TagSet.elements new_params)) in
    let {uvars; assumptions; goal} = obligation in
    begin match unify_goal (Top.TagSet.union uvars rule'.uvars) goal rule'.conclusion with
      | Some uni ->
        let premises_weakened : sequent list = List.map (weaken_sequent assumptions) rule'.premises in
        let premises_unified = List.map (apply_unif_sequent uni) premises_weakened in
        (* TODO apply unification to the output of the builder??? *)
        Some { params = new_params;
               builder = rule'.builder;
               premises = premises_unified;
               tm_unif = uni.terms;
             }
      | None -> None
    end




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

let pp_sequent st fmt ({uvars; assumptions; goal} : sequent) =
  pp_open_hovbox fmt 0;
  pp_print_string fmt "[";
  Pp.pp_list_aux fmt "," (fun i -> pp_print_string fmt ("x_" ^ (string_of_int i))) (Top.TagSet.elements uvars);
  pp_print_string fmt "] ";
  Pp.pp_list_aux fmt "," (pp_atomic_prop st fmt) (List.map snd assumptions);
  pp_print_string fmt " |- ";
  pp_goal st fmt goal;
  pp_close_box fmt ()

let string_of_sequent st = Pp.string_of_x (fun fmt -> pp_sequent st fmt)

let pp_rule st fmt {params = p; uvars = u; premises = prems; conclusion = c; builder = _ } =
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
