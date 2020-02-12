let hash_list (l : ('a Hashcons.hash_consed) list) =
	List.fold_left (fun h -> fun x -> abs (19 * x.Hashcons.hkey + h)) 1 l
	