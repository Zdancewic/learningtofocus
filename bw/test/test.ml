open Core
open Util
open OUnit2
open Prop
open Proof
open Proof_rep

module G = Globals.G

(* Unit tests *)
let dir = "tests/"

let files = List.filter ~f:(String.is_suffix ~suffix:".p") (Array.to_list (Sys.readdir dir))



let n_not pprop = n_imp pprop (n_shift (p_zero ()))

let props = [
  ("↓1", n_shift (p_one ()));
  ("↓1 & ↓1", n_shift (p_one ()));
  ("not 0", n_not (p_zero ()));
  ("not (not ⊤)", n_not (p_shift (n_not (p_shift (n_top ())))));
]

let manual = "Prover Only" >::: List.map ~f:(fun (name, nprop) ->
    name >:: (fun _ -> assert_bool "Proof search failed." (Option.is_some (Processor.prove [] nprop)))) props

let tests =  "Combined Parsing & Prover" >:::
               (List.map ~f:(fun fn -> fn >::
                                    (fun _ -> assert_bool "Proof search failed." (Processor.do_file (dir ^ fn))))
                  files);;

run_test_tt_main manual;;
run_test_tt_main tests;;



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
