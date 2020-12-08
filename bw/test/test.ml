open Util
open OUnit2


module G : Globals.T = struct
  type tm_t = Globals.HTm.t
  let tm_table = Globals.HTm.create 251    (* or, load from a file based on flags *)

  type pprop_t = Globals.PProp.t
  let pprop_table = Globals.PProp.create 251

  type nprop_t = Globals.NProp.t
  let nprop_table = Globals.NProp.create 251

  type ppat_t = Globals.PPat.t
  let ppat_table = Globals.PPat.create 251

  type npat_t = Globals.NPat.t
  let npat_table = Globals.NPat.create 251

  type proof_t = Globals.HProof.t
  let proof_table = Globals.HProof.create 251

  type stack_t = Globals.NStack.t
  let stack_table = Globals.NStack.create 251

  type value_t = Globals.PValue.t
  let value_table = Globals.PValue.create 251

  type sym_t = (int,string * int) Hashtbl.t
  let sym_table = (Hashtbl.create 251 : sym_t)

  let rev_table : (int, string) Hashtbl.t = Hashtbl.create 251

  let gen_sym s =
    let h = Hashtbl.hash s in
    try let _,t = Hashtbl.find sym_table h in t
    with Not_found -> let t = Hashcons.gentag() in Hashtbl.add sym_table h (s, t); Hashtbl.add rev_table t s; t

  let lookup_sym t =
    try Hashtbl.find rev_table t with Not_found -> ("S" ^ string_of_int t)

  let gen_tag = Hashcons.gentag   (* ensures that proposition symbols and term Top.tags can be used together in unification *)
end

module PROCESS = Processor.Make(G)


(* Unit tests *)
let dir = "tests/"
let hasSuffix suffix s =
  let s_len = String.length s in
  let suffix_len = String.length suffix in
  String.sub s (s_len - suffix_len) suffix_len = suffix

let files = List.filter (hasSuffix ".p") (Array.to_list (Sys.readdir dir))

let tests =  "Tests directory" >:::
               (List.map (fun fn -> fn >::
                                    (fun _ -> assert_bool "Proof search failed." (PROCESS.do_file (dir ^ fn))))
                  files)

(* let _ = run_test_tt_main tests *)


open PROCESS.PROPS
open PROCESS.PROOFS
open Proof_rep

let n_not pprop = n_imp pprop (n_shift (p_zero ()))
let prop1 = n_prop (G.gen_tag ()) []

let case_tt = pr_p_rfoc pr_value_unit

let case_double_neg = pr_n_match (fun {node = Pat_n_app ({node = Pat_p_bvar _; _},
                                                         {node = Pat_n_app ({ node = Pat_p_bvar _; _}, _); _}); _} ->
    pr_n_lfoc (Bound 1) (pr_stack_app (pr_value_shift (pr_bvar 0)) (pr_stack_shift pr_ex_falso)))
let type_double_neg = n_imp (p_shift prop1) (n_not (p_shift (n_not (p_shift prop1))))

let assert_checks msg proof nprop = assert_bool msg (check [] [] proof nprop)

let checker_tests = "Proof checker" >::: [
    "true" >:: (fun _ -> assert_checks "true" case_tt (n_shift (p_one ())));
    "double negation" >:: (fun _ ->
      Pp.verbose := true;
      assert_checks "double negation" case_double_neg type_double_neg)
]


let _ = run_test_tt_main checker_tests
