(* Top level declarations *)

type tag = int          (* unique Top.tags generated during hash consing *)
module OrderedInt = struct
	type t = int
	let compare i j = i - j
end

module TagSet = Set.Make(OrderedInt)


