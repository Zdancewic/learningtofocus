(* Ranges and utilities on ranges. *)

(* compact representation of a filename *)
type file_index

(* get or create a filename's compact representation *)
val file_index_of_file : string -> file_index

(* get the file this index was created from *)
val file_of_file_index : file_index -> string

(* a position in the source file *)
type pos

(* line of position *)
val line_of_pos : pos -> int

(* column of position *)
val col_of_pos : pos -> int

(* new position with given line and col *)
val mk_pos : int -> int -> pos

(* a range of positions in a particular file *)
type t

(* the file a range is in *)
val file_index_of_range : t -> file_index

(* the beginning of the range *)
val start_of_range : t -> pos

(* the end of the range *)
val end_of_range : t -> pos

(* create a new range from the given file and start, end positions *)
val mk_range : file_index -> pos -> pos -> t

(* merge two ranges together *)
val merge_range : t -> t -> t

(* pretty-print a range, leaving out the file *)
val string_of_range : t -> string

(* use to tag generated AST nodes where range does not apply *)
val norange : t
