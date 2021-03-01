open Core
open Util
open Common

module G : Globals.T = struct
  type tm_t = Globals.HTm.t
  let tm_table = Globals.HTm.create 251    (* or, load from a file based on flags *)

  type ppat_t = Globals.PPat.t
  let ppat_table = Globals.PPat.create 251

  type npat_t = Globals.NPat.t
  let npat_table = Globals.NPat.create 251

  type pprop_t = Globals.PProp.t
  let pprop_table = Globals.PProp.create 251

  type nprop_t = Globals.NProp.t
  let nprop_table = Globals.NProp.create 251

  type proof_t = Globals.HProof.t
  let proof_table = Globals.HProof.create 251

  type value_t = Globals.PValue.t
  let value_table = Globals.PValue.create 251

  type stack_t = Globals.NStack.t
  let stack_table = Globals.NStack.create 251

  type sym_t = (int,string * int) Hashtbl.t
  let sym_table = (Hashtbl.create ~size:251 (module Int) : sym_t)

  let rev_table : (int, string) Hashtbl.t = Hashtbl.create ~size:251 (module Int)

  let gen_sym s =
    let h = Hashtbl.hash s in
    begin match Hashtbl.find sym_table h with
    | Some (_, t) -> t
    | None -> let t = Hashcons.gentag () in
      ignore (Hashtbl.add sym_table ~key:h ~data:(s, t));
      ignore (Hashtbl.add rev_table ~key:t ~data:s);
      t
    end

  let lookup_sym t =
    match Hashtbl.find rev_table t with
    | Some x -> x
    | None -> "S" ^ string_of_int t

  let gen_tag = Hashcons.gentag   (* ensures that proposition symbols and term Top.tags can be used together in unification *)
end

module TMS = Tm.Make(G);;
module PROPS = Prop.Make(G)(TMS);;
module PROOFS = Proof.Make(G)(TMS)(PROPS);;
module TRANS = Translate.Make(G)(TMS)(PROPS);;
module RULES = Rule.Make(G)(TMS);;
module SYNTH = Synthetics.Make(G)(TMS)(PROPS)(RULES)(PROOFS);;
module SEARCH = Search.Make(RULES)
module PROVER = Prover.Make(G)(TMS)(PROPS)(RULES)(SYNTH)(SEARCH);;
module STRATEGY = Mcts.RuleStrategy(RULES)(SYNTH)(PROVER);;
module MCTS = Mcts.Make(STRATEGY);;