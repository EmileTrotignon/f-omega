(** Helper library functions *)

let map_snd f l = List.map (fun (x, y) -> (x, f y)) l

let iter_snd f l = List.iter (fun (_, y) -> f y) l

let rec fold_left_map_unify f init li1 li2 =
  match (li1, li2) with
  | [], [] ->
      (init, [])
  | e1 :: li1, e2 :: li2 ->
      let acc, e = f init e1 e2 in
      let acc, li = fold_left_map_unify f acc li1 li2 in
      (acc, e :: li)
  | _ ->
      raise (Invalid_argument "fold_left_map_unify : different lengths")

(** Helper for command line options *)

let spec_list = ref []

let spec_add name spec doc = spec_list := (name, spec, doc) :: !spec_list

let spec_bool r name doc =
  spec_add name (if !r then Arg.Clear r else Arg.Set r) ("\t" ^ doc)

let spec_flip r name doc = spec_add name (Arg.Unit (fun () -> r := not !r)) doc

let spec_bool_new b name doc =
  let r = ref b in
  spec_bool r name doc ; r

let spec_false = spec_bool_new false

let spec_true = spec_bool_new true

let spec_alias new_name old_name =
  let _, spec, _ = List.find (fun (n, _, _) -> n = old_name) !spec_list in
  spec_add new_name spec ("Alias for " ^ old_name)

let verbose = ref 0

let () =
  let increase () = incr verbose in
  spec_add "--verbose" (Arg.Unit increase) "Increase verbosity" ;
  spec_alias "-v" "--verbose"

let verbose_level n = !verbose > n
