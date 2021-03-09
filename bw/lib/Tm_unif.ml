open Tm_rep
open Format


  type t = (Top.tag * tm) list

  let empty : t = []
  let single (t : Top.tag) (e : tm) : t =
   [(t, e)]
  let combine (old_unif : t) (new_unif : t) : t option =
    List.fold_right
      (fun (tag, tm) ->
         function
         | None -> None
         | Some u ->
           if List.mem_assoc tag u then begin
             Debug.debug "tm_unif collision: %s" (string_of_int tag);
             None
           end else
             Some ((tag, Tm.msubst_tt new_unif tm) :: u))
      old_unif (Some new_unif)

  let rec apply (uni : t) (t : tm) : tm =
    match t.node with
    | Tm_fvar tag ->
      if List.mem_assoc tag uni then
        List.assoc tag uni
      else t
    | Tm_fun (tag, args) ->
      (* TODO could tag be in domain of uni??? *)
      Tm.tm_fun tag (List.map (apply uni) args)
    | _ -> t


  let domain (u : t) : Top.TagSet.t = Top.TagSet.of_list (List.map fst u)

  let pp_tm_unif st fmt (tm_unif : t) =
    let pp_tm_unif_entry st fmt (tag, tm) =
    pp_print_string fmt "(";
    pp_print_string fmt (st tag);
    pp_print_string fmt ": ";
    Pp.pp_tm_aux st fmt 0 tm;
    pp_print_string fmt ")"
  in
  pp_print_string fmt "[";
  Pp.pp_list_aux fmt ", " (pp_tm_unif_entry st fmt) tm_unif;
  pp_print_string fmt "]";
  ()

  let string_of_tm_unif st = Pp.string_of_x (fun fmt -> pp_tm_unif st fmt)
