open Util

(* Hash-consed representation of polarized first-order logic formulas *)
type pprop = pprop_t Hashcons.hash_consed 
and pprop_t =
  | P_one 
  | P_zero
  | P_or    of pprop * pprop
  | P_ex    of pprop
  | P_shift of nprop

and nprop = nprop_t Hashcons.hash_consed
and nprop_t =
  | N_prop of Top.tag * (Tm_rep.tm list)  (* the Top.tag is stored in a symbol table *)
  | N_top
  | N_and of nprop * nprop
  | N_imp of pprop * nprop 
  | N_all of nprop
  | N_shift of pprop

module PPropRep = struct
  type t = pprop_t

  let equal p1 p2 =
    match (p1, p2) with
    | (P_one, P_one) -> true
    | (P_zero, P_zero) -> true
    | (P_or (q11, q12), P_or (q21, q22)) -> q11 == q21 && q12 == q22
    | (P_ex q1, P_ex q2) -> q1 == q2
    | (P_shift n1, P_shift n2) -> n1 == n2
    | _ -> false

  let hash p =
    match p with
    | P_one -> 1
    | P_zero -> 0
    | P_or (q1, q2) -> abs (19 * (19 * q1.Hashcons.hkey + q2.Hashcons.hkey) + 2)
    | P_ex q -> abs (19 * q.Hashcons.hkey + 3)
    | P_shift n -> abs (19 * n.Hashcons.hkey + 4)
end

module NPropRep = struct
  type t = nprop_t

  let equal n1 n2 =
    match (n1, n2) with
    | (N_prop (x, l1), N_prop (y, l2)) -> x == y && List.fold_left2 (fun t x y -> t && x == y) true l1 l2
    | (N_top, N_top) -> true
    | (N_and (n11, n12), N_and (n21, n22)) -> n11 == n21 && n12 == n22
    | (N_imp (p11, n12), N_imp (p21, n22)) -> p11 == p21 && n12 == n22
    | (N_all n1, N_all n2) -> n1 == n2
    | (N_shift p1, N_shift p2) -> p1 == p2
    | _ -> false

  let hash n =
    match n with
    | N_prop (x, l1) -> abs ((19 * x + Hashutil.hash_list l1) + 1)
    | N_top -> 0
    | N_and (n1, n2) -> abs (19 * (19 * n1.Hashcons.hkey + n2.Hashcons.hkey) + 2)
    | N_imp (p1, n2) -> abs (19 * (19 * p1.Hashcons.hkey + n2.Hashcons.hkey) + 3)
    | N_all n1 -> abs (19 * n1.Hashcons.hkey + 4)
    | N_shift p -> abs (19 * p.Hashcons.hkey + 5)  

end  


