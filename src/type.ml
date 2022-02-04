(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-37-39-60"]

open Util
open Syntax
open Mlog

let compare_cvar u v =
  let uv = Int.compare u.id v.id in
  if uv = 0 then String.compare u.name v.name else uv

module Tenv = struct
  include Map.Make (struct
    type t = cvar

    let compare = compare_cvar
  end)

  let of_list li =
    List.fold_left (fun acc (key, data) -> add key data acc) empty li

  let map_key f m =
    m |> bindings |> List.map (fun (key, data) -> (f key, data)) |> of_list

  let add key data map = map |> remove key |> add key data
end

(** Renaming tvars *)

(** Computations may introduce, auxiliary fresh that have disapeared after
   normalization. When done, we may rename types to minimize the numeric
   suffixes of type variables.  *)

(** We mainting for each name, the highest suffix appearing in scope *)
module Senv = Map.Make (struct
  type t = svar

  let compare v1 v2 = String.compare (string_of_svar v1) (string_of_svar v2)
end)

module Eenv = Map.Make (struct
  type t = evar

  let compare v1 v2 = String.compare (string_of_evar v1) (string_of_evar v2)
end)

let apply_with_default t su a = try Tenv.find a su with Not_found -> t

let apply su a = apply_with_default a su a

(** Kind equality *)
let rec eq_kind k1 k2 = k1 = k2

(** Type substitution as opposed to renaming *)
let rec subst su (t : ctyp) : ctyp =
  if Tenv.is_empty su then t
  else
    match t with
    | Tvar ident -> (
      match Tenv.find_opt ident su with
      | Some typ ->
          typ
      | None -> (
        match ident.def with Some {typ; _} -> subst su typ | None -> t ) )
    | Tprim prim_typ ->
        Tprim prim_typ
    | Tapp (tfunc, targ) ->
        Tapp (subst su tfunc, subst su targ)
    | Tprod t_li ->
        Tprod (t_li |> List.map (subst su))
    | Trcd rdc ->
        Trcd (rdc |> List.map (fun (field, typ) -> (field, subst su typ)))
    | Tarr (t1, t2) ->
        Tarr (subst su t1, subst su t2)
    | Tbind (binder, ident, kind, typ) ->
        let su = Tenv.remove ident su in
        Tbind (binder, ident (* todo check correctness *), kind, subst su typ)

let subst su t =
  let t' = subst su t in
  Print.(
    meprintf "substitution : %s became %s\n"
      (string (typ cvar t))
      (string (typ cvar t'))) ;
  t'

let subst_typ a ta t =
  let su = Tenv.singleton a ta in
  subst su t

(** Type normalization *)
let eager = spec_false "--eager" "Eager full reduction and definition expansion"

(** We still provide the --lazy option, even though this is the default *)
let _lazy =
  spec_add "--lazy" (Arg.Clear eager)
    "Lazy definition expansion and reduction to head normal forms"

type rec_env = C of (rec_env * cvar Tenv.t * ctyp) Tenv.t

let fresh_cvar env svar =
  let rec pick_id id =
    let candidate = cvar ~id svar in
    if not @@ Tenv.mem candidate env then candidate else pick_id (id + 1)
  in
  pick_id 0

let refresh_cvar env cvar = fresh_cvar env (svar cvar.name)

let refresh_cvar_rec_env env cvar =
  let (C env) = env in
  fresh_cvar env (svar cvar.name)

let rec norm_lazy t =
  match t with
  | Tapp (tfunc, targ) -> (
      let tfunc = norm_lazy tfunc in
      match tfunc with
      | Tbind (Tlam, ident, kind, typ) ->
          let typ = subst_typ ident targ typ in
          norm_lazy typ
      | _ ->
          Tapp (tfunc, targ) )
  | _ ->
      t

let rec norm ?(expand_defs = false) t1 =
  (* meprintf "internal normalizing : %s\n" Print.(string @@ typ cvar t1) ; *)
  match t1 with
  | Tvar ident ->
      if expand_defs then
        match ident.def with Some {typ; _} -> norm typ | None -> t1
      else t1
  | Tprim _ ->
      t1
  | Tapp (tfunc, targ) -> (
      let tfunc = norm tfunc in
      match tfunc with
      | Tbind (Tlam, ident, kind, typ) ->
          norm (subst_typ ident (norm targ) typ)
      | _ ->
          Tapp (tfunc, norm targ) )
  | Tprod t_li ->
      Tprod (t_li |> List.map (norm ~expand_defs))
  | Trcd rcd ->
      Trcd (rcd |> map_snd (norm ~expand_defs))
  | Tbind (binder, ident, kind, typ) ->
      Tbind (binder, ident, kind, norm typ)
  | Tarr (targ, tbody) ->
      Tarr (norm targ, norm tbody)

let norm t1 =
  let t1' = norm t1 in
  (* Print.(
     meprintf "normalizing :\n%s\ninto :\n%s\n"
       (string @@ typ cvar t1)
       (string @@ typ cvar t1')) ; *)
  t1'

let bind_none ~f o = match o with None -> f () | v -> v

let rec diff_typ t1 t2 =
  let bind_diff_typ t1 t1' ~f = bind_none ~f (diff_typ t1 t1') in
  let diff_typ_pair t1 t1' t2 t2' =
    bind_none ~f:(fun () -> diff_typ t2 t2') (diff_typ t1 t1')
  in
  match (t1, t2) with
  | Tvar ident, Tvar ident' ->
      if ident = ident' then None else Some (t1, t2)
  | Tprim prim_typ, Tprim prim_typ' ->
      if prim_typ = prim_typ' then None else Some (t1, t2)
  | Tapp (tfunc, targ), Tapp (tfunc', targ') ->
      diff_typ_pair tfunc tfunc' targ targ'
  | Tprod t_li, Tprod t_li' ->
      let rec aux t_li t_li' =
        match (t_li, t_li') with
        | [], [] ->
            None
        | t :: t_li, t' :: t_li' ->
            bind_diff_typ t t' ~f:(fun () -> aux t_li t_li')
        | _ ->
            assert false
      in
      aux t_li t_li'
  | Trcd rcd, Trcd rcd' ->
      let rec aux t_li t_li' =
        match (t_li, t_li') with
        | [], [] ->
            None
        | (field, _) :: t_li, (field', _) :: t_li' when field <> field' ->
            Some (t1, t2)
        | (_, t) :: t_li, (_, t') :: t_li' -> (
          match diff_typ t t' with None -> aux t_li t_li' | v -> v )
        | _ ->
            assert false
      in
      aux rcd rcd'
  | Tarr (targ, tbody), Tarr (targ', tbody') ->
      diff_typ_pair targ targ' tbody tbody'
  | Tbind (binder, ident, kind, typ), Tbind (binder', ident', kind', typ')
    when binder = binder' && eq_kind kind kind' ->
      diff_typ typ (subst_typ ident' (Tvar ident) typ')
  | t1, t2 ->
      Some (t1, t2)

let eq_typ t1 t2 = diff_typ t1 t2 <> None
