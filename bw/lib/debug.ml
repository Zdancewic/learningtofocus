let enabled = ref false
let level = ref 0
let mute = ref 0

let debugk k format =
  if !enabled && !mute == 0 then
    Printf.ksprintf (fun s ->
        let indent = String.make (2 * !level) ' ' in
        print_endline (indent ^ s);
        k ()
    ) format
  else
    Printf.ksprintf (fun _ -> k ()) format

let debug format = debugk (fun _ -> ()) format

let debug_start format =
  debugk (fun () ->
      level := !level + 1
      (* Printf.printf "new level: %d \n%!" !level *)
    ) format

let debug_end () =
  (* Printf.printf "end level: %d \n%!" !level; *)
  level := !level - 1

let mute_start () =
  mute := !mute + 1

let mute_end () =
  mute := !mute - 1
