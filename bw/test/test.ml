open Util
open OUnit2


module G : Globals.T = struct
  type tm_t = Globals.HTm.t
  let tm_table = Globals.HTm.create 251    (* or, load from a file based on flags *)

  type pprop_t = Globals.PProp.t
  let pprop_table = Globals.PProp.create 251

  type nprop_t = Globals.NProp.t
  let nprop_table = Globals.NProp.create 251

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
let files = Sys.readdir dir

let tests =  "Tests directory" >::: Array.to_list
               (Array.map (fun fn -> fn >::
                                     (fun _ -> assert_bool "Proof search failed." (PROCESS.do_file (dir ^ fn))))
                  files)

let _ = run_test_tt_main tests


