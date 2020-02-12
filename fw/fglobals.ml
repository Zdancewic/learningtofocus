
module HTm = Hashcons.Make(Ftm_rep)
module FProp = Hashcons.Make(Fprop_rep.SPropRep)

module type T =
  sig
    type tm_t = HTm.t
    val tm_table : tm_t
		
    type fprop_t = FProp.t
    val fprop_table : fprop_t
	
    type sym_t = (int, (string * int)) Hashtbl.t
    val sym_table : sym_t
    val gen_sym : string -> int     (* creates a new symbol or returns and existing one *)
    val lookup_sym : int -> string 	(* maps a tag generated by gen_sym to the string *)
					
    val gen_tag : unit -> Ftop.tag    (* creates a globally unique identifier *) 
  end
	
