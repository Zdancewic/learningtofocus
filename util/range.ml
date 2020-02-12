type file_index = int
type pos = int * int
type t = file_index * pos * pos

let string_to_file = Hashtbl.create 32
and file_to_string = ref (Array.make 0 "")

let file_index_of_file filename =
  if Hashtbl.mem string_to_file filename then
    Hashtbl.find string_to_file filename
  else (
    let next_idx = Array.length !file_to_string in
    let old_arr = !file_to_string in
    file_to_string := Array.make (next_idx + 1) filename;
    Array.blit old_arr 0 !file_to_string 0 next_idx;
    Hashtbl.add string_to_file filename next_idx;
    next_idx
  )

let file_of_file_index index =
  try Array.get !file_to_string index
  with Invalid_argument _ -> raise (Invalid_argument "bad file index")

let line_of_pos (l,_) = l
let col_of_pos (_,c) = c
let mk_pos line col = (line, col)

let file_index_of_range (i,_,_) = i
let start_of_range (_,s,_) = s
let end_of_range (_,_,e) = e
let mk_range i s e = (i,s,e)
let valid_pos (l,_) = l <> 0
let merge_range ((f,s1,e1) as r1) ((f',s2,e2) as r2)=
  if (not (valid_pos s1)) then r2 else
  if (not (valid_pos s2)) then r1 else
  mk_range f (min s1 s2) (max e1 e2)
let string_of_range ((_,(sl,sc),(el,ec))) =
  Printf.sprintf "[%d.%d-%d.%d]" sl sc el ec

let norange = (file_index_of_file "internal", (0,0), (0,0))
