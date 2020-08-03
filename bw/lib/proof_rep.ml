open Util
open Prop_rep
open Tm_rep

type prop = Pos of pprop | Neg of nprop

type proof = t Hashcons.hash_consed

and t =
  | Pr_var of int
  | Pr_p_one
  | Pr_p_inL of proof * pprop
  | Pr_p_inR of pprop * proof
  | Pr_p_case of proof * proof * proof
  | Pr_p_sigpair of pprop * tm * proof
  | Pr_p_sigmatch of proof * proof
  | Pr_p_shift of proof
  | Pr_n_top
  | Pr_n_pair of proof * proof
  | Pr_n_projL of proof * proof
  | Pr_n_projR of proof * proof
  | Pr_n_abs of pprop * proof
  | Pr_n_app of proof * proof * proof
  | Pr_n_piabs of proof
  | Pr_n_piapp of proof * tm * proof
  | Pr_n_shift of proof

let equal (proof1 : t) (proof2 : t) : bool =
  match (proof1, proof2) with
  | Pr_var i, Pr_var j -> i == j
  | Pr_p_one, Pr_p_one -> true
  | Pr_p_inL (p1, prop1), Pr_p_inL (p2, prop2) -> p1 == p2 && prop1 == prop2
  | Pr_p_inR (prop1, p1), Pr_p_inR (prop2, p2) -> p1 == p2 && prop1 == prop2
  | Pr_p_case (pa1, pb1, pc1), Pr_p_case (pa2, pb2, pc2) ->
      pa1 == pa2 && pb1 == pb2 && pc1 == pc2
  | Pr_p_sigpair (prop1, tm1, p1), Pr_p_sigpair (prop2, tm2, p2) ->
      prop1 == prop2 && tm1 == tm2 && p1 == p2
  | Pr_p_sigmatch (pa1, pb1), Pr_p_sigmatch (pa2, pb2) ->
      pa1 == pa2 && pb1 == pb2
  | Pr_p_shift p1, Pr_p_shift p2 -> p1 == p2
  | Pr_n_top, Pr_n_top -> true
  | Pr_n_pair (pa1, pb1), Pr_n_pair (pa2, pb2) -> pa1 == pa2 && pb1 == pb2
  | Pr_n_projL (pa1, pb1), Pr_n_projL (pa2, pb2) -> pa1 == pa2 && pb1 == pb2
  | Pr_n_projR (pa1, pb1), Pr_n_projR (pa2, pb2) -> pa1 == pa2 && pb1 == pb2
  | Pr_n_abs (prop1, p1), Pr_n_abs (prop2, p2) -> prop1 == prop2 && p1 == p2
  | Pr_n_app (pa1, pb1, pc1), Pr_n_app (pa2, pb2, pc2) ->
      pa1 == pa2 && pb1 == pb2 && pc1 == pc2
  | Pr_n_piabs p1, Pr_n_piabs p2 -> p1 == p2
  | Pr_n_piapp (pa1, t1, pb1), Pr_n_piapp (pa2, t2, pb2) ->
      pa1 == pa2 && t1 == t2 && pb1 == pb2
  | Pr_n_shift p1, Pr_n_shift p2 -> p1 == p2
  | _ -> false

let hash (proof1 : t) : int =
  match proof1 with
  | Pr_var i -> abs ((19 * i) + 1)
  | Pr_p_one -> 0
  | Pr_p_inL (p1, prop1) ->
      abs ((19 * ((19 * p1.Hashcons.hkey) + prop1.Hashcons.hkey)) + 2)
  | Pr_p_inR (prop1, p1) ->
      abs ((19 * ((19 * prop1.Hashcons.hkey) + p1.Hashcons.hkey)) + 3)
  | Pr_p_case (pa1, pb1, pc1) ->
      abs
        ( 19
          * ( (19 * ((19 * pa1.Hashcons.hkey) + pb1.Hashcons.hkey))
            + pc1.Hashcons.hkey )
        + 4 )
  | Pr_p_sigpair (prop1, tm1, p1) ->
      abs
        ( 19
          * ( (19 * ((19 * prop1.Hashcons.hkey) + tm1.Hashcons.hkey))
            + p1.Hashcons.hkey )
        + 5 )
  | Pr_p_sigmatch (pa1, pb1) ->
      abs ((19 * ((19 * pa1.Hashcons.hkey) + pb1.Hashcons.hkey)) + 6)
  | Pr_p_shift p1 -> abs ((19 * p1.Hashcons.hkey) + 7)
  | Pr_n_top -> 8
  | Pr_n_pair (pa1, pb1) ->
      abs ((19 * ((19 * pa1.Hashcons.hkey) + pb1.Hashcons.hkey)) + 9)
  | Pr_n_projL (pa1, pb1) ->
      abs ((19 * ((19 * pa1.Hashcons.hkey) + pb1.Hashcons.hkey)) + 10)
  | Pr_n_projR (pa1, pb1) ->
      abs ((19 * ((19 * pa1.Hashcons.hkey) + pb1.Hashcons.hkey)) + 11)
  | Pr_n_abs (prop1, p1) ->
      abs ((19 * ((19 * prop1.Hashcons.hkey) + p1.Hashcons.hkey)) + 12)
  | Pr_n_app (pa1, pb1, pc1) ->
      abs
        ( 19
          * ( (19 * ((19 * pa1.Hashcons.hkey) + pb1.Hashcons.hkey))
            + pc1.Hashcons.hkey )
        + 13 )
  | Pr_n_piabs p1 -> abs ((19 * p1.Hashcons.hkey) + 14)
  | Pr_n_piapp (pa1, t1, pb1) ->
      abs
        ( 19
          * ( (19 * ((19 * pa1.Hashcons.hkey) + t1.Hashcons.hkey))
            + pb1.Hashcons.hkey )
        + 15 )
  | Pr_n_shift p1 -> abs ((19 * p1.Hashcons.hkey) + 16)
