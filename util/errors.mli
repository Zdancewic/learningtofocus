(* Error reporting and related utilities. *)

exception Error of Range.t * string
val handle_errors : 'a -> (unit -> 'a) -> 'a
val errorf : Range.t -> ('b, unit, string, 'a) format4 -> 'b
val string_of_error_line : Range.t -> string -> (Range.t -> string) -> string
val string_of_error : Range.t -> string -> string
