module G : Globals.T = struct
  type tm_t = Globals.HTm.t
  let tm_table = Globals.HTm.create 251    (* or, load from a file based on flags *)

  type pprop_t = Globals.PProp.t
  let pprop_table = Globals.PProp.create 251

  type nprop_t = Globals.NProp.t
  let nprop_table = Globals.NProp.create 251

  type proof_t = Globals.HProof.t
  let proof_table = Globals.HProof.create 251

  type sym_t = (int,string * int) Hashtbl.t
  let sym_table = (Hashtbl.create 251 : sym_t)

  let lookup_sym t =
    try
      let (s,_) = Hashtbl.find sym_table t in
      s
    with Not_found -> "NOT FOUND"

  let gen_tag =
    let c = ref 0 in
    fun () -> let x = !c in incr c; x

  let gen_sym (s:string) =
    let h = Hashtbl.hash s in
    try ignore (Hashtbl.find sym_table h); h
    with Not_found -> Hashtbl.add sym_table h (s,gen_tag()); h

end

module TMS = Tm.Make(G);;
module PROPS = Prop.Make(G)(TMS);;
module TRANS = Translate.Make(G)(TMS)(PROPS);;

open TMS
open PROPS

let x = tm_uvar 0
let y = tm_uvar 1
let z = tm_uvar 0
let p = p_one ()
let q = p_zero ()
let r = p_or p q
let p' = p_one ()
let q' = p_zero ()
let r' = p_or p' q'

;; Pp.showhash := true
;; Pp.verbose := true

;; print_string (Pp.string_of_pprop G.lookup_sym r)
