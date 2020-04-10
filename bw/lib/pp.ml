(** Pretty printing for terms and formulas*)
open Util
open Common
open Tm_rep
open Prop_rep
open Format

let verbose  = ref false
let showhash = ref false

(* Auxilliary printing functions*)

let rec pp_list_aux fmt sep fn = function
  | [] -> ()
  | [x] -> fn x
  | x :: tl -> (
      pp_open_hovbox fmt 0;
      fn x;
      pp_print_string fmt sep;
      pp_close_box fmt ();
      pp_print_space fmt ();
      pp_list_aux fmt sep fn tl
    )


let pp_hash_consed_aux fmt lvl fn h =
  let pps = pp_print_string fmt in
  if !showhash then
    (pp_open_hovbox fmt 0;
     pps "{hkey = "; pps (string_of_int h.Hashcons.hkey); pps ";"; pp_print_break fmt 1 1;
     pps "Top.tag = "; pps (string_of_int h.Hashcons.tag); pps ";"; pp_print_break fmt 1 1;
     pps "node = "; fn fmt lvl (h.Hashcons.node); pps "}";
     pp_close_box fmt ())
  else fn fmt lvl (h.Hashcons.node)

let rec pp_tm_aux st fmt lvl =
  pp_hash_consed_aux fmt lvl (pp_tm_t_aux st)
and pp_tm_t_aux (st : int -> string) fmt _ t =
  let pps = pp_print_string fmt in
  match t with
  | Tm_uvar i ->  pps ("u_" ^ (string_of_int i))
  | Tm_param x -> pps ("x_" ^ (string_of_int x))
  | Tm_fun (f, l) ->
    pps (st f);
    if l = [] then () else begin
      pps "(";
      (pp_list_aux fmt "," (pp_tm_aux st fmt 0) l);
      pps ")"
    end

let prec_of_pprop p =
  match p with
  | P_one     -> 1000
  | P_zero    -> 1000
  | P_or _    -> 20
  | P_ex _    -> 900
  | P_shift _ -> 1000


let prec_of_nprop n =
  match n with
  | N_prop _  -> 1000
  | N_top     -> 1000
  | N_and _   -> 30
  | N_imp _   -> 10
  | N_all _   -> 900
  | N_shift _ -> 1000

let rec pp_pprop_aux st fmt lvl p =
  let this_level = prec_of_pprop p in
  let pps = pp_print_string fmt in
  let pph lvl = pp_hash_consed_aux fmt lvl (pp_pprop_aux st) in
  let pp_bin_pprop p1 p2 s l1 l2 =
    pp_open_box fmt 0;
    pph l1 p1;
    pps s;
    pph l2 p2;
    pp_close_box fmt ()
  in
  (* Hash-consing interferes with name hints, so we print only the de Bruijn indices
     let pp_binding_prop h p s =
     let x = gensym_var_hint h in
     pp_open_box fmt 0;
     pps s; pps " ";
     pp_tm_aux fmt 0 (Tm_fv x);
     pps "."; pp_print_space fmt ();
     pp_prop_aux fmt this_level (open_pt (Tm_fv x) p);
     pp_close_box fmt ()
     in
  *)
  (if this_level < lvl then fprintf fmt "(" else ());
  begin
    match p with
    | P_one -> pps "ONE"
    | P_zero -> pps "ZERO"
    | P_or (p1, p2) -> pp_bin_pprop p1 p2 " + " this_level this_level
    | P_ex p1 -> pps "EX."; pph this_level p1
    | P_shift n -> pps "↑"; pp_hash_consed_aux fmt lvl (pp_nprop_aux st) n
  end;
  (if (this_level < lvl) then fprintf fmt ")" else ())

and pp_nprop_aux st fmt lvl n =
  let this_level = prec_of_nprop n in
  let pps = pp_print_string fmt in
  let pph lvl = pp_hash_consed_aux fmt lvl (pp_nprop_aux st) in
  let pp_bin_nprop n1 n2 s l1 l2 =
    pp_open_box fmt 0;
    pph l1 n1;
    pps s;
    pph l2 n2;
    pp_close_box fmt ()
  in
  let pp_imp p1 n2 l1 l2 =
    pp_open_box fmt 0;
    pp_hash_consed_aux fmt l1 (pp_pprop_aux st) p1;
    pps " -> ";
    pph l2 n2;
    pp_close_box fmt ()
  in
  (if this_level < lvl then fprintf fmt "(" else ());
  begin match n with
    | N_prop (f, ts) -> begin
	pps (st f);
	if List.length ts = 0 then () else (
	  pps "(";
	  (pp_list_aux fmt "," (pp_tm_aux st fmt 0) ts);
	  pps ")")
      end
    | N_top -> pps "TOP"
    | N_and (n1, n2) -> pp_bin_nprop n1 n2 " & " this_level this_level
    | N_imp (p1, n2) -> pp_imp p1 n2 1000 this_level
    | N_all n1 -> pps "ALL."; pph this_level n1
    | N_shift p -> pps "↓"; pp_hash_consed_aux fmt lvl (pp_pprop_aux st) p
  end;
  (if (this_level < lvl) then fprintf fmt ")" else ())


(*
let prec_of_pf m =
match m with
| Pf_flab _   -> 1000
| Pf_blab _   -> 1000
| Pf_pair _   -> 1000
| Pf_fst  _   -> 900
| Pf_snd  _   -> 900
| Pf_abs  _   -> 50
| Pf_app  _   -> 100
| Pf_inl  _   -> 900
| Pf_inr  _   -> 900
| Pf_case _   -> 50
| Pf_not  _   -> 50
| Pf_contra _ -> 90
| Pf_unit     -> 1000
| Pf_abort _  -> 80
| Pf_all _    -> 50
| Pf_inst _   -> 100
| Pf_pack _   -> 1000
| Pf_unpack _ -> 40
| Pf_let    _ -> 40

let pp_lab fmt (h,k) =
pp_print_string fmt (h ^ "_" ^ (string_of_int k))

let rec pp_pf_aux fmt lvl m =
let this_level = prec_of_pf m in
let pps = pp_print_string fmt in
let pp_binder p m s =
let l = gensym_lab () in
pps s; pp_lab fmt l;
pps ":"; pp_prop_aux fmt 0 p;
pps "."; pp_print_space fmt ();
pp_pf_aux fmt 0 (open_mm (Pf_flab l) m)
in
pp_open_box fmt 0;
  (if this_level < lvl then fprintf fmt "(" else ());
 begin
match m with
| Pf_flab l -> pp_lab fmt l
| Pf_blab i -> pps "!BLAB_"; pps (string_of_int i)
| Pf_pair (m1, m2) ->
pps "<"; pp_pf_aux fmt 0 m1;
pps ","; pp_print_space fmt ();
pp_pf_aux fmt 0 m2;
pps ">"
| Pf_fst m1 -> pps "fst "; pp_pf_aux fmt this_level m1
| Pf_snd m1 -> pps "snd "; pp_pf_aux fmt this_level m1
| Pf_abs (p, m1) -> pp_binder p m1 "\\"
| Pf_app (m1, m2) ->
pp_pf_aux fmt this_level m1;
pp_print_space fmt ();
pp_pf_aux fmt 1000 m2
| Pf_inl (p, m1) -> pps "inl["; pp_prop_aux fmt 0 p; pps "] "; pp_pf_aux fmt this_level m1
| Pf_inr (p, m1) -> pps "inr["; pp_prop_aux fmt 0 p; pps "] "; pp_pf_aux fmt this_level m1
| Pf_case (m1, m2, m3) ->
let l1 = gensym_lab_hint "m" in
let l2 = gensym_lab_hint "n" in
pps "case ";
pp_pf_aux fmt 0 m1;
pps " of"; pp_force_newline fmt ();
pps "| inl "; pp_lab fmt l1; pps " -> "; pp_pf_aux fmt 0 (open_mm (Pf_flab l1) m2);
pp_force_newline fmt ();
pps "| inr "; pp_lab fmt l2; pps " -> "; pp_pf_aux fmt 0 (open_mm (Pf_flab l2) m3)
| Pf_not (p, m1) -> pp_binder p m1 "~"
| Pf_contra (m1, p, m2) ->
pp_pf_aux fmt this_level m1;
pp_print_space fmt ();
pps ".[";
pp_prop_aux fmt 0 p;
pps "]"; pp_print_space fmt ();
pp_pf_aux fmt 1000 m2
| Pf_unit -> pps "<>"
| Pf_abort (p, m1) ->
pps "abort[";
pp_prop_aux fmt 0 p;
pps "]";
pp_print_space fmt ();
pp_pf_aux fmt this_level m1
| Pf_all (h, m1) ->
let x = gensym_var_hint h in
pps "/\\\\";
pps x; pps ".";
pp_print_space fmt ();
pp_pf_aux fmt this_level m1
| Pf_inst (m1, t) ->
pp_pf_aux fmt this_level m1;
pp_print_space fmt ();
pps "["; pp_tm_aux fmt 0 t;
pps "]";
| Pf_pack (t, m1) ->
pps "pack[";
pp_tm_aux fmt 0 t;
pps ","; pp_print_space fmt ();
pp_pf_aux fmt 0 m1;
pps "]"
| Pf_unpack (h, m1, m2) ->
let x = gensym_var_hint h in
let l = gensym_lab_hint "lx" in
pps "let ["; pps x; pps ", "; pp_lab fmt l; pps "] =";
pp_print_space fmt ();
pp_pf_aux fmt 0 m1;
pps " in";
pp_print_space fmt ();
pp_pf_aux fmt 0 (open_mt (Tm_fv x) (open_mm (Pf_flab l) m2))
| Pf_let (m1, m2) ->
let l = gensym_lab_hint "l" in
pps "let "; pp_lab fmt l; pps " =";
pp_print_space fmt ();
pp_pf_aux fmt 0 m1;
pps " in";
pp_print_space fmt ();
pp_pf_aux fmt 0 (open_mm (Pf_flab l) m2)
end;
(if this_level < lvl then fprintf fmt ")" else ());
pp_close_box fmt ()

let pp_binding fmt (l,p) =
pp_lab fmt l;
pp_print_string fmt " : ";
pp_prop_aux fmt 0 p

let pp_ctxt fmt = pp_list_aux fmt "," (pp_binding fmt)
*)

let string_of_x f x =
  pp_open_hvbox str_formatter 0;
  f str_formatter x;
  pp_close_box str_formatter ();
  flush_str_formatter ()


let string_of_tm st = string_of_x (fun fmt -> pp_tm_aux st fmt 0)
let string_of_pprop st p = if !verbose then string_of_x (fun fmt -> pp_hash_consed_aux fmt 0 (pp_pprop_aux st)) p else "[PPROP]"
let string_of_nprop st n = if !verbose then
    string_of_x (fun fmt -> pp_hash_consed_aux fmt 0 (pp_nprop_aux st)) n
  else "[NPROP]"
(*
let string_of_pf = string_of_x (fun fmt -> pp_pf_aux fmt 0)
let string_of_lab = string_of_x pp_lab

let string_of_ctxt = string_of_x pp_ctxt
*)

let pp_input i =
  match i with
  | Ast.Include (s, _) -> (
      print_string "input: ";
      print_string s;
      print_newline ()
    )
  | Ast.Fof (s, _, _) -> (
      print_string "fof: ";
      print_string s;
      print_newline ()
    )

let pp_file = List.iter pp_input
