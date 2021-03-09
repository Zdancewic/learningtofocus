open Common
open Tm
open Prop
open Ast
module G = Globals.G

  type lab = int  (* move to Pf_rep *)

  type translation =
    | Binding of lab * prop
    | Goal of prop

  let rec tm_to_tm m (t : Ast.tm) : Tm_rep.tm =
    match t with
    | Var x -> tm_fvar (List.assoc x m)
    | Fun (s, tms) -> tm_fun (G.gen_sym s) (List.map (tm_to_tm m) tms)


  let rec prop_to_pprop (m : (Ast.var * Top.tag) list) (p : Ast.prop) : Prop_rep.pprop =
    match p with
    | BinOp (p1, bop, p2) ->
      (match bop with
       | Or -> p_or (prop_to_pprop m p1) (prop_to_pprop m p2)
       | _  -> p_shift (prop_to_nprop m p))
    | Prop _ -> p_shift (prop_to_nprop m p)
    | All  _ -> p_shift (prop_to_nprop m p)
    | Exists (vs, p1) ->
      let xs = List.map (fun x -> (x, G.gen_tag ())) vs in
      List.fold_right (fun (_, v) -> fun q -> p_ex (close_pt v q)) xs (prop_to_pprop (xs @ m) p1)
    | Not _ -> p_shift (prop_to_nprop m p)
    | Eq _  -> failwith "Term EQ primitive '=' not supported"
    | True  -> p_one ()
    | False -> p_zero ()
  and prop_to_nprop (m : (Ast.var * Top.tag) list) (p : Ast.prop) : Prop_rep.nprop =
    let prop_not m p = n_imp (prop_to_pprop m p) (n_shift (p_zero ())) in
    match p with
    | Prop (s, tms) -> n_prop (G.gen_sym s) (List.map (tm_to_tm m) tms)
    | BinOp (p1, bop, p2) ->
      (match bop with
       | Iff -> prop_to_nprop m (BinOp (BinOp (p1, Imp, p2), And, BinOp (p2, Imp, p1)))
       | Imp -> n_imp (prop_to_pprop m p1) (prop_to_nprop m p2)
       | RevImp -> n_imp (prop_to_pprop m p2) (prop_to_nprop m p1)
       | NotIff -> prop_not m (BinOp (p1, Iff, p2))
       | NotOr  -> prop_not m (BinOp (p1, Or, p2))
       | NotAnd -> prop_not m (BinOp (p1, And, p2))
       | And    -> n_and (prop_to_nprop m p1) (prop_to_nprop m p2)
       | Or     -> n_shift (prop_to_pprop m p))
    | All (vs, p1) ->
      let xs = List.map (fun x -> (x, G.gen_tag ())) vs in
      List.fold_right (fun (_, v) -> fun q -> n_all (close_nt v q)) xs (prop_to_nprop (xs @ m) p1)
    | Exists _   -> n_shift (prop_to_pprop m p)
    | Not p -> prop_not m p
    | Eq _  -> failwith "Term EQ primitive '=' not supported"
    | True -> n_top ()
    | False -> n_shift (p_zero ())
