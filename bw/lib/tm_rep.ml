open Util

type tm = t Hashcons.hash_consed
and t =
  | Tm_bvar of int          (* bound variable -- dB index *)
  | Tm_fvar of Top.tag      (* free variable (parameter or unification variable) *)
  | Tm_fun of Top.tag * tm list  (* arity is implicit *)

let equal t1 t2 =
  match (t1, t2) with
  | (Tm_fvar a, Tm_fvar b)   -> a == b
  | (Tm_fun (f, l1), Tm_fun (g, l2)) -> f == g && List.fold_left2 (fun t x y -> t && x == y) true l1 l2
  | _ -> false

let hash t =
  match t with
  | Tm_bvar t -> abs (19 * t)
  | Tm_fvar t -> abs (19 * t + 1)
  | Tm_fun (f, l1) -> abs (19 * f + Hashutil.hash_list l1 + 2)
