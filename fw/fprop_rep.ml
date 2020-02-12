open Hashcons
(*open Fol*)
open List
open Ftop

type sign = 
  | Pos
  | Neg

let flip (s: sign) : sign = 
  match s with
  | Pos -> Neg
  | Neg -> Pos

type s_prop = s_prop_t hash_consed
and s_prop_t =
  (*| SProp_param of var * sign *)
  | SProp_pred of (Ftop.tag * (Ftm_rep.tm list)) * sign
  | SProp_and of (s_prop * s_prop) * sign
  | SProp_imp of (s_prop * s_prop) * sign
  | SProp_or  of (s_prop * s_prop) * sign
  | SProp_not of (s_prop) * sign
  | SProp_top of sign
  | SProp_bot of sign
  | SProp_Emp of sign

module SPropRep = struct
  type t = s_prop_t

  let equal t1 t2 = 
    match (t1, t2) with
    | (SProp_pred ((x, l1), sn1), SProp_pred ((y, l2), sn2)) -> x == y && sn1 == sn2 && List.fold_left2 (fun t x y -> t && x == y) true l1 l2
    | (SProp_and ((t11, t12), sn1), SProp_and ((t21, t22), sn2)) -> t11 == t21 && t12 == t22 && sn1 == sn2
    | (SProp_imp ((t11, t12), sn1), SProp_imp ((t21, t22), sn2)) -> t11 == t21 && t12 == t22 && sn1 == sn2
    | (SProp_or ((t11, t12), sn1), SProp_or ((t21, t22), sn2)) -> t11 == t21 && t12 == t22 && sn1 == sn2
    | (SProp_not (t11, sn1), SProp_not (t21, sn2)) -> t11 == t21 && sn1 == sn2
    | (SProp_top sn1, SProp_top sn2) -> sn1 == sn2
    | (SProp_bot sn1, SProp_top sn2) -> sn1 == sn2
    | (SProp_Emp sn1, SProp_Emp sn2) -> sn1 == sn2
    | _ -> false
  
  let hash sp =
    match sp with 
    | SProp_pred ((x, l1), sn) -> if (sn = Pos) then abs ((19 * x + Hashutil.hash_list l1) + 1) else  ((19 * x + Hashutil.hash_list l1) + 2)
    | SProp_and ((sp1, sp2), sn) -> abs (19 * (19 * sp1.Hashcons.hkey + sp2.Hashcons.hkey) + 3)
    | SProp_imp ((sp1, sp2), sn) -> abs (19 * (19 * sp1.Hashcons.hkey + sp2.Hashcons.hkey) + 4)
    | SProp_or  ((sp1, sp2), sn) -> abs (19 * (19 * sp1.Hashcons.hkey + sp2.Hashcons.hkey) + 5)
    | SProp_not (sp1, sn) -> abs (19 * sp1.Hashcons.hkey + 6)  
    | SProp_top sn -> 1
    | SProp_bot sn -> 0
    | SProp_Emp	sn -> 0
end
