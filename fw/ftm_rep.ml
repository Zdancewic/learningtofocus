
type tm = t Hashcons.hash_consed 
and t = 
	| Tm_uvar of int      (* bound variable *) 
	| Tm_param of Ftop.tag     (* free (e.g. unification) variable / parameter *)
	| Tm_fun of Ftop.tag * tm list  (* arity is implicit *)

let equal t1 t2 =
	match (t1, t2) with
		| (Tm_uvar i, Tm_uvar j)     -> i == j
		| (Tm_param a, Tm_param b)   -> a == b
		| (Tm_fun (f, l1), Tm_fun (g, l2)) -> f == g && List.fold_left2 (fun t x y -> t && x == y) true l1 l2
		| _ -> false

let hash t =
	match t with
		| Tm_uvar i -> i
		| Tm_param t -> abs (19 * t + 1)
		| Tm_fun (f, l1) -> abs (19 * f + Hashutil.hash_list l1 + 2)
