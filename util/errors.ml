open Printf

exception Error of Range.t * string

let errorf range fmt = ksprintf (fun s -> raise (Error (range,s))) fmt

let string_of_error_line range msg getline =
  let linestr = getline range in
  sprintf "%s: %s%s" (Range.string_of_range range) msg linestr

let string_of_error range msg =
  string_of_error_line range msg (fun _ -> "")

let handle_errors default f =
  try f ()
  with Error (r,s) -> (
    print_endline (string_of_error r s);
    default
  )
