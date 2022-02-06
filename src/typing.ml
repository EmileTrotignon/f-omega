open Util
open Syntax
open Type
open Error

(** 1. Environments *)

(** We represent the environment using maps.  (For short programs, we could
   use lists, but large programs with modules, may have quite large
   contexts.)  We separate the name spaces of expression variables [evar]
   from type variables, hence using a separate map.

   For type variables, we actually need two maps: [svar] maps source type
   variables (which may be shadowed) to internal type variables while [cvar]
   maps internal type variables (which are never shadowed) to their kind or
   definition. <- probably not the definitons

   You may need to add another map in type [env] for Task 4.  *)

open Printf

let string_of_ctyp t = Print.(string (typ cvar t))

let string_of_cvar c = Print.(string (cvar c))

let string_of_kind k = Print.(string (kind k))

let string_of_exp e = Print.(string (exp e))

type reason =
  [ `NotARecord
  | `NotBinder of shape
  | `OutOfBoundsProj of int
  | `RecordLabel of lab
  | `Shape of ctyp
  | `ShapeWithin of ctyp * ctyp * ctyp ]

(* [failure_typing r t] raises an in type [t], because of reason [r]. *)
let failure_typing reason t =
  Error.(
    raise
      (error_unloc
         ( match reason with
         | `NotBinder shape ->
             error_unloc (Expected (t, Matching shape))
         | `NotARecord ->
             Expected (t, Matching (Srcd None))
         | `OutOfBoundsProj n ->
             error_unloc (Expected (t, Matching (Sprod (Some n))))
         | `RecordLabel lab ->
             Expected (t, Matching (Srcd (Some lab)))
         | `Shape t' ->
             Expected (t, Nonequal t')
         | `ShapeWithin (t1, t2, t3) ->
             Expected (t, Showdiff (t1, t2, t3)) ) ))

(** [failure_kinding styp k r] raises a kinding error that occured in type
  [styp]in kind [k], because of reason [r]. *)
let failure_kinding styp k reason =
  match reason with
  | `Shape k2 ->
      raise Error.(error_unloc (Kinding (styp, k, Nonequal k2)))
  | `NeedArrow ->
      raise Error.(error_unloc (Kinding (styp, k, Matching Sarr)))

(** [unify_kinds k1 k2] is a kind that is equal to [k1] and [k2]. If no such
    kind exists, calls [failure_kinding]. *)
let unify_kinds styp k1 k2 =
  if eq_kind k1 k2 then k1 else failure_kinding styp k1 (`Shape k2)

(** Let for within_loc *)
let ( let+ ) x f = Error.within_loc f x

(** Let that discards a location *)
let ( let+/ ) x f = f x.obj

type env = {evar: ctyp Eenv.t; svar: cvar Senv.t; cvar: kind Tenv.t}

let empty_env = {evar= Eenv.empty; svar= Senv.empty; cvar= Tenv.empty}

(** Functions to query the environment accordingly. Same semantics as maps,
   except for the order of arguments. All `find_` functions raise the
   exception [Not_found] when their argument is not in the environment. *)
let find_cvar env a =
  try Tenv.find a env.cvar
  with Not_found ->
    failwith
      (Printf.sprintf "Could not find %s_%i in env.cvar. Should never happen."
         a.name a.id )

(** [string_of_cvars] converts a [kind Tenv.t] to a string, for debugging
  purposes.  *)
let string_of_cvars un =
  let buffer = Buffer.create 256 in
  Tenv.iter
    (fun cvar kind ->
      Buffer.add_string buffer
        (sprintf " (%s :: %s)" (string_of_cvar cvar) (string_of_kind kind)) )
    un ;
  Buffer.contents buffer

(** Representation of a cvar. *)
let cvar_repr {name; id; _} = if id = 0 then name else name ^ string_of_int id

(** [exists_cvar_with_repr env repr] is true if [env.cvar] contains a cvar whose
  representation is [repr]. *)
let exists_cvar_with_repr env repr =
  Tenv.exists (fun cvar _ -> String.equal (cvar_repr cvar) repr) env.cvar

let find_evar env x = Eenv.find x env.evar

let find_svar env s = Senv.find s env.svar

(** Functions to modify the environment accordingly. Same semantics as maps,
   except for the order of arguments. *)
let add_evar env ~key ~data = {env with evar= Eenv.add key data env.evar}

let add_cvar env ~key ~data = {env with cvar= Tenv.add key data env.cvar}

(** [add_svar] must also deal with shallow bindings *)
let add_svar env ~key ~data = {env with svar= Senv.add key data env.svar}

(** [get_svar env a] is a wrapper around [find_evar env a] that turns a
   [Not_found] exception into a non-localized [Unbound] typing-error
   exception.  These will have to be localized by their calling context,
   using [within_loc]. *)
let get_svar env (key : svar) =
  try find_svar env key
  with Not_found -> error_unloc (Unbound (Typ (None, key)))

(** May raise non-localized [Unbound] error *)
let get_evar exp env x =
  try find_evar env x with Not_found -> error exp (Unbound (Exp x))

(** [norm_if_eager ()] is [norm] is [eager] is set to true, and [Fun.id]
  otherwise. *)
let norm_if_eager () = if !eager then norm else Fun.id

(** 2. Type minimization *)

(** Type checking must perform computation on types when checking for
   convertibilty.  This requires appropriate renamaing to avoid capture,
   hence generating many fresh variables, which may then disappear during
   reduction.  The resulting type may thefore use large integer suffixes,
   which are unpleasant for the user to read.

   For this reason, we minimize variable names after typechecking each
   declaration, and before printing error messages.  We take advantage of
   this to allow chose possibly large integers when renaming local
   variables during computation on types, given that this will be minimized
   after computation.

   (We could use this to further optimize maps, using just some additional
   [uid] integer field for identificatiion instead of the pair [name] nad [id].)
*)

(** [minimize_typ env t] returns a renaming of [t] that minimizes the
   variables suffixes but still avoids shallowing internally and with
   respect to env [env] *)
let minimize_typ _env t = t

(** [do_minimize] tells whether types should be minimized. It defaults to
   [true] and may be changed with the `--rawtypes` command line option, *)
let do_minimize = spec_true "--rawtypes" "Do not minimize types"

let minimize_typ env t =
  if !do_minimize then minimize_typ (env, Tenv.empty) t else t

let def_map f {typ; scope} = {typ= f typ; scope}

(** [fresh_cvar env ?def ?unifiable svar] returns a [cvar] to be used as
  internal representation of [svar]. Guarantees no conflict with cvars already
  registered in [env]. If [def] or [unifiable] are provided, the resulting
  [cvar] will have those fields set to their values. *)
let fresh_cvar env ?def ?unifiable svar =
  let def = def |> Option.map (def_map (norm_if_eager ())) in
  let rec pick_id id =
    let candidate = cvar ~id ?def ?unifiable svar in
    let repr = cvar_repr candidate in
    if exists_cvar_with_repr env repr then pick_id (id + 1) else candidate
  in
  pick_id 0

(** [fresh_unifiable_cvar ()] returns a never used cvar [a] such that
  [a.unifiable] is true.  *)
let fresh_unifiable_cvar =
  let id = ref (-1) in
  let svar = svar "unif" in
  fun () ->
    incr id ;
    cvar ~id:!id ~unifiable:true svar

(** [refresh_cvar env c] is the cvar [c'] such that [c'] is unbound in [env] and
  [c.name = c'.name]. *)
let refresh_cvar env ?def ?unifiable cvar =
  fresh_cvar env ?def ?unifiable (svar cvar.name)

(* auxilliray function for [refresh_binders] bellow. *)
let rec refresh_binders env su typ =
  match typ with
  | Tvar a ->
      Tvar
        ( match Tenv.find_opt a su with
        | Some a ->
            a
        | None -> (
          match a.def with
          | Some {typ; scope} ->
              {a with def= Some {typ= refresh_binders env su typ; scope}}
          | None ->
              a ) )
  | Tprim prim_typ ->
      Tprim prim_typ
  | Tapp (tfunc, targ) ->
      Tapp (refresh_binders env su tfunc, refresh_binders env su targ)
  | Tprod t_li ->
      Tprod (t_li |> List.map (refresh_binders env su))
  | Trcd rdc ->
      Trcd (rdc |> map_snd (refresh_binders env su))
  | Tarr (t1, t2) ->
      Tarr (refresh_binders env su t1, refresh_binders env su t2)
  | Tbind (binder, ident, kind, typ) ->
      let ident' = refresh_cvar env ident in
      let su = Tenv.add ident ident' su in
      let env = add_cvar env ~key:ident' ~data:kind in
      Tbind (binder, ident', kind, refresh_binders env su typ)

(** [refresh_cvars env typ] is the type [typ'] such that [typ = typ'] and every
  [cvar] introduced by a [Tbind] is [typ'] is unbound in [env]. *)
let refresh_binders env typ =
  let typ' = refresh_binders env Tenv.empty typ in
  typ'

(* -------------------------------------------------------------------------- *)
(* typing types *)

(** [type_typ env t] typechecks source type [t] returning its kind [k] and
   an internal representation of [t].  This may raise non-localized (Unbound and
   Kinding) typing error exceptions. *)
let rec type_typ env (t : styp) : kind * ctyp =
  match t with
  | Tprim c ->
      (Ktyp, Tprim c)
  | Tvar svar ->
      let cvar = get_svar env svar in
      let kind = find_cvar env cvar in
      (kind, Tvar cvar)
  | Tapp (tfunc, targ) -> (
      let kfunc, tfunc = type_typ env tfunc in
      let karg, targ = type_typ env targ in
      match kfunc with
      | Karr (karg', kbody) ->
          let _karg = unify_kinds t karg karg' in
          (kbody, Tapp (tfunc, targ))
      | Ktyp ->
          failure_kinding t kfunc `NeedArrow )
  | Tprod typs ->
      ( Ktyp
      , Tprod
          ( typs
          |> List.map (fun typ ->
                 let _kind, ctyp = type_typ env typ in
                 ctyp ) ) )
  | Trcd rcd ->
      ( Ktyp
      , Trcd
          ( rcd
          |> List.map (fun (field, typ) ->
                 let _kind, ctyp = type_typ env typ in
                 (field, ctyp) ) ) )
  | Tarr (t1, t2) ->
      let _kind, t1 = type_typ env t1 in
      let _kind, t2 = type_typ env t2 in
      (Ktyp, Tarr (t1, t2))
  | Tbind (Tlam, ident, kind_input, typ) ->
      let cident = fresh_cvar env ident in
      let env =
        env
        |> add_svar ~key:ident ~data:cident
        |> add_cvar ~key:cident ~data:kind_input
      in
      let kind2, typ = type_typ env typ in
      (Karr (kind_input, kind2), Tbind (Tlam, cident, kind_input, typ))
  | Tbind (binder, ident, kind_input, typ) ->
      let cident = fresh_cvar env ident in
      let env =
        env
        |> add_svar ~key:ident ~data:cident
        |> add_cvar ~key:cident ~data:kind_input
      in
      let kind_output, typ = type_typ env typ in
      (kind_output, Tbind (binder, cident, kind_input, typ))

let type_typ env t =
  let k, t = type_typ env t in
  (k, refresh_binders env t)

(** Checking that local variable do not escape. Typechecking of
   existential types requires that locally abstract variables do not escape
   from their scope.  This amounts to verifying that the returned type is
   well-formed.  It suffices to check that all variables are bound in the
   given environment.

   One must be careful of non linear redexes and delayed definitions.
   Therefore, we must not only check for well-formedness, but return an
   equivalent type that is well-formed.  This should just perform the
   necessary unfoldings and reductions.  *)
exception Escape of cvar

let rec wf_ctyp env t : ctyp =
  match t with
  | Tvar a -> (
      let a =
        Option.value ~default:a
          (Option.map fst @@ Tenv.find_first_opt (eq_cvar a) env.cvar)
      in
      if Tenv.mem a env.cvar then t
      else match a.def with Some _ -> t | None -> raise (Escape a) )
  | Tprim prim_typ ->
      Tprim prim_typ
  | Tapp (tfunc, targ) ->
      if not !eager then
        let m, t' = norm_lazy t in
        if m then wf_ctyp env t' else Tapp (wf_ctyp env tfunc, wf_ctyp env targ)
      else Tapp (wf_ctyp env tfunc, wf_ctyp env targ)
  | Tprod t_li ->
      Tprod (t_li |> List.map (wf_ctyp env))
  | Trcd rdc ->
      Trcd (rdc |> List.map (fun (field, typ) -> (field, wf_ctyp env typ)))
  | Tarr (t1, t2) ->
      Tarr (wf_ctyp env t1, wf_ctyp env t2)
  | Tbind (binder, ident, kind, typ) ->
      let env = add_cvar env ~key:ident ~data:kind in
      Tbind (binder, ident, kind, wf_ctyp env typ)

let wf_ctyp env t : ctyp =
  let t = norm_if_eager () t in
  wf_ctyp env t

(* -------------------------------------------------------------------------- *)
(* unification section *)

(** Type [unifications] represent equalities between types and unifiable
  variables. *)
type unifications = ctyp Tenv.t

(** [sort_rcd rcd] is the record list [rcd], but sorted by field names. *)
let sort_rcd rcd =
  List.sort (fun (field, _) (field', _) -> String.compare field field') rcd

(** [mentions_cvar a t] is true if [t] mentions [a].  *)
let rec mentions_cvar cvar typ =
  match typ with
  | Tvar cvar' ->
      if eq_cvar cvar cvar' then true
      else
        Option.value ~default:false
        @@ Option.map (fun {typ; _} -> mentions_cvar cvar typ) cvar'.def
  | Tprim _prim_typ ->
      false
  | Tapp (tfunc, targ) ->
      mentions_cvar cvar tfunc || mentions_cvar cvar targ
  | Tprod t_li ->
      t_li |> List.exists (mentions_cvar cvar)
  | Trcd rdc ->
      rdc |> List.exists (fun (_field, typ) -> mentions_cvar cvar typ)
  | Tarr (t1, t2) ->
      mentions_cvar cvar t1 || mentions_cvar cvar t2
  | Tbind (_binder, ident, _kind, typ) ->
      if eq_cvar ident cvar then false else mentions_cvar cvar typ

exception UnifFailure of reason * ctyp

(* auxiliary function for unify_types bellow. *)
let rec unify_types unifications t1 t2 : ctyp Tenv.t * ctyp =
  let fail reason t = raise (UnifFailure (reason, t)) in
  if t1 == t2 then (unifications, t1)
  else
    let unifications, typ =
      match (t1, t2) with
      | Tvar ident, Tvar ident' when eq_cvar ident ident' ->
          (unifications, Tvar ident)
      | Tvar ident, typ when ident.unifiable ->
          unify_idents unifications ident typ
      | typ, Tvar ident when ident.unifiable ->
          unify_idents unifications ident typ
      | Tvar {def= Some {typ= t1'; _}; _}, t2 ->
          (* The two below cases are the same, they are just separated to be
             able to maintain the invariant that [t1] is the authoritative type,
             that is the one that is "expected" in type error and the one that is
             kept if no unifications are performed. *)
          (* We unify with the definition of the variable. If no equality is
             added then we keep the unexpanded version. *)
          let n_unif = Tenv.cardinal unifications in
          let unifications, t =
            unify_types unifications (norm_if_eager () t1')
              (norm_if_eager () t2)
          in
          let new_n_unif = Tenv.cardinal unifications in
          (unifications, if n_unif = new_n_unif then t1 else t)
      | t1, Tvar {def= Some {typ= t2; _}; _} ->
          let n_unif = Tenv.cardinal unifications in
          let unifications, t =
            unify_types unifications (norm_if_eager () t1) (norm_if_eager () t2)
          in
          let new_n_unif = Tenv.cardinal unifications in
          (unifications, if n_unif = new_n_unif then t1 else t)
      | Tapp (tfunc, targ), Tapp (tfunc', targ') ->
          if not !eager then
            (* In lazy mode, this application pair may need to be reduced in
               order to prove unifiability. *)
            try
              (* We first try not to reduce. *)
              let unifications, tfunc = unify_types unifications tfunc tfunc' in
              let unifications, targ = unify_types unifications targ targ' in
              (unifications, Tapp (tfunc, targ))
            with UnifFailure _ as failure ->
              (* If this fails, then we try to reduce. *)
              let eliminated_app1, t1' = norm_lazy t1 in
              let eliminated_app2, t2' = norm_lazy t2 in
              (* If [norm_lazy] is unable to reduce them, we fail. *)
              if not (eliminated_app1 || eliminated_app2) then raise failure
              else
                (* If it did reduce at least one of the types, we try to unify
                   them again, and try to keep the unreduced type if possible. *)
                let n_unif = Tenv.cardinal unifications in
                let unifications, t = unify_types unifications t1' t2' in
                ( unifications
                , if n_unif = Tenv.cardinal unifications then t1 else t )
          else
            (* In eager mode, we already know that the reduction cannot be done,
               so we just unify the functions and the arguments. *)
            let unifications, tfunc = unify_types unifications tfunc tfunc' in
            let unifications, targ = unify_types unifications targ targ' in
            (unifications, Tapp (tfunc, targ))
      | (Tapp (_, _) as t1), t2 when not !eager ->
          (* The two below cases are the same, they are just separated to be
             able to maintain the invariant that [t1] is the authoritative type,
             that is the one that is "expected" in type error and the one that is
             kept if no unifications are performed. *)
          let eliminated_app1, t1' = norm_lazy t1 in
          if eliminated_app1 then
            let n_unif = Tenv.cardinal unifications in
            let unifications, t = unify_types unifications t1' t2 in
            ( unifications
            , (* if no unifications are performed, we can keep the unreduced
                 version of the type. *)
              if n_unif = Tenv.cardinal unifications then t1 else t )
          else fail (`Shape t1) t2
      | t1, (Tapp (_, _) as t2) when not !eager ->
          let eliminated_app2, t2' = norm_lazy t2 in
          if eliminated_app2 then
            let n_unif = Tenv.cardinal unifications in
            let unifications, t = unify_types unifications t1 t2' in
            ( unifications
            , (* if no unifications are performed, we can keep the unreduced
                 version of the type. *)
              if n_unif = Tenv.cardinal unifications then t1 else t )
          else fail (`Shape t1) t2
      | Tprim prim_typ, Tprim prim_typ' ->
          if prim_typ = prim_typ' then (unifications, Tprim prim_typ)
          else fail (`Shape t1) t2
      | Tprod t_li, Tprod t_li' ->
          let unifications, t_li =
            fold_left_map_unify unify_types unifications t_li t_li'
          in
          (unifications, Tprod t_li)
      | Trcd rcd, Trcd rcd' ->
          if List.length rcd <> List.length rcd' then fail (`Shape t1) t2
          else
            let s_rcd = sort_rcd rcd in
            let s_rcd' = sort_rcd rcd' in
            let n_unif = Tenv.cardinal unifications in
            let unifications, nrcd =
              fold_left_map_unify
                (fun unifications (field, t) (field', t') ->
                  if field <> field' then fail (`Shape t1) t2 ;
                  let unifications, t = unify_types unifications t t' in
                  (unifications, (field, t)) )
                unifications s_rcd s_rcd'
            in
            ( unifications
            , (* We check that the unifications have grown in order to be able
                 to keep the unsorted fields if not. *)
              Trcd (if n_unif = Tenv.cardinal unifications then rcd else nrcd)
            )
      | Tarr (targ, tbody), Tarr (targ', tbody') ->
          let unifications, targ = unify_types unifications targ targ' in
          let unifications, tbody = unify_types unifications tbody tbody' in
          (unifications, Tarr (targ, tbody))
      | Tbind (binder, ident, kind, typ), Tbind (binder', ident', kind', typ')
        when binder = binder' && eq_kind kind kind' ->
          let ntyp' = subst_typ ident' (Tvar ident) typ' in
          let typ' = ntyp' in
          let unifications, typ =
            unify_types (Tenv.remove ident unifications) typ typ'
          in
          (unifications, Tbind (binder, ident, kind, typ))
      | t1, t2 ->
          fail (`Shape t1) t2
    in
    (unifications, typ)

and unify_idents unifications ident t =
  match Tenv.find_opt ident unifications with
  | Some typ ->
      unify_types unifications typ t
  | None when ident.unifiable ->
      if mentions_cvar ident t then failure_typing (`Shape t) (Tvar ident)
      else
        let unifications = Tenv.add ident t unifications in
        (unifications, t)
  | None -> (
    match ident.def with
    | Some {typ; _} ->
        unify_types unifications typ t
    | None ->
        failure_typing (`Shape t) (Tvar ident) )

(** [unify_types unifs t1 t2] is the pair [(unifs', t)] such that :
  - [unifs] is included in [unifs']
  - [t] is convertible to [t1] and [t2].
  - [unifs'] also contains the equalities needed to make the above true.
  An error is raised if there is no such pair. *)
let unify_types unifications t1 t2 =
  try
    (* if we have physical equality, no need to do anything. *)
    if t1 == t2 then (unifications, norm_if_eager () t1)
    else
      (* We normalize the ingoing types if they we are eager, and we apply the
         current equalities to them. *)
      let t1' = t1 |> norm_if_eager () |> subst unifications in
      let t2' = t2 |> norm_if_eager () |> subst unifications in
      (* We only use the result of the unification if at least one equality
         was added to [unifications]. *)
      let n_unif = Tenv.cardinal unifications in
      let unifications, typ = unify_types unifications t1' t2' in
      let typ_subst = subst unifications typ in
      ( unifications
      , if n_unif = Tenv.cardinal unifications then t1'
        else subst unifications typ_subst )
  with UnifFailure (reason, t) -> (
    match reason with
    | `Shape te ->
        failure_typing (`ShapeWithin (te, t2, t1)) t
    | _ ->
        failure_typing reason t )

(** [apply_unification_env env unifs] is [env'] such that every occurence of a
  variable from the left-hand side of [unifs] is replaced by its corresponding
  right-hand side. *)
let apply_unification_env {evar; cvar; svar} unifications =
  let unif_cvar cvar =
    match Tenv.find_opt cvar unifications with
    | Some typ ->
        {cvar with unifiable= false; def= Some {typ; scope= -1}}
    | None ->
        { cvar with
          def=
            Option.map
              (fun ({typ; _} as def) ->
                {def with typ= typ |> subst unifications} )
              cvar.def }
  in
  { evar= Eenv.map (subst unifications) evar
  ; svar
  ; cvar= Tenv.map_key unif_cvar cvar }

(* -------------------------------------------------------------------------- *)
(* typing proper section *)

let ( !@ ) = Locations.with_loc

let ( !@- ) = Locations.dummy_located

let type_prim_val = function
  | Int _ ->
      Tprim Tint
  | String _ ->
      Tprim Tstring
  | Bool _ ->
      Tprim Tbool

(** [type_pattern is_rec (env, unifications) pat] is the tuple
  [((env', unifs'), t)] such that :
  - if [is_rec] is true, [env'] is [env] with every variable from the pattern
    bound to its type. Else [env' = env]
  - [t] is a type that has the same shape as [pat], and that satisifyes the
    annotation found. Unannotated leaves are typed with a fresh unifiable
    variable, and if an upstream node is annotated, unified with that
    annotation.
  - [unifs'] contains all the equalities from [unifs], plus thoses needed to
    unify the pattern and its annotations. *)
let rec type_pattern is_rec (env, unifications) pat =
  let type_pattern = type_pattern is_rec in
  let+ pat in
  match pat with
  | Ptyp (pat, typ_annot) ->
      let+ typ_annot in
      let _kind, typ_annot = type_typ env typ_annot in
      let (env, unifications), typ_pat = type_pattern (env, unifications) pat in
      (* [typ_annot] needs to be the first argument passed to [unify_types], so
         that it is the one kept as-is if possible. *)
      let unifications, typ = unify_types unifications typ_annot typ_pat in
      ((env, unifications), typ)
  | Pvar ident ->
      let uident = fresh_unifiable_cvar () in
      let typ = Tvar uident in
      let env = if is_rec then add_evar env ~key:ident ~data:typ else env in
      ((env, unifications), typ)
  | Pprod li ->
      let (env, unifications), li =
        List.fold_left_map type_pattern (env, unifications) li
      in
      ((env, unifications), Tprod li)
  | Pprim prim_val ->
      ((env, unifications), type_prim_val prim_val)

(** [add_pattern_evar env pat typ] add the type of variables from [pat] to [env]
    assuming that pattern has type [typ]. Fails unceremonously if that is not
    the case. *)
let rec add_pattern_evar env pat typ =
  let+ pat in
  match (pat, typ) with
  | Pvar evar, typ ->
      add_evar env ~key:evar ~data:typ
  | Ptyp (pat, _), typ ->
      add_pattern_evar env pat typ
  | Pprod pats, Tprod typs ->
      List.fold_left2 add_pattern_evar env pats typs
  | _ ->
      assert false

(** [type_shape_exp env e] is the "shape" of the type of [e]. What that means is
  that give an approximate type, with unifiable variables in places where we are
  not able to be accurate. This is used to be able to type unannotated recursive
  functions. It is mutually  *)
let rec type_shape_exp env exp =
  let+ exp in
  match exp with
  | Efun (bindings, body) ->
      let rec aux env bindings =
        match bindings with
        | [] ->
            type_shape_exp env body
        | binding :: bindings -> (
          match binding with
          | Exp pattern ->
              let (_env, _unif), typ_pattern =
                type_pattern true (env, Tenv.empty) pattern
              in
              Tarr (typ_pattern, aux env bindings)
          | Typ (svar, kind) ->
              let cvar = fresh_cvar env svar in
              let env =
                env
                |> add_svar ~key:svar ~data:cvar
                |> add_cvar ~key:cvar ~data:kind
              in
              Tbind (Tall, cvar, kind, aux env bindings) )
      in
      aux env bindings
  | Elet (_is_rec, _pat, _e1, e2) ->
      type_shape_exp env e2
  | Eprod eli ->
      Tprod (eli |> List.map (type_shape_exp env))
  | _ ->
      Tvar (fresh_unifiable_cvar ())

(** [type_exp env unifs exp] is the pair [unifs', t] such that [t] is the type
  of [exp] and [unifs'] are the equalities from [unifs] plus the ones needed to
  type [exp]. *)
let rec type_exp env unifications exp : unifications * ctyp =
  let+ exp_ = exp in
  let unifications, t =
    match exp_ with
    | Evar x ->
        (unifications, get_evar exp env x)
    | Eprim prim_val ->
        (unifications, type_prim_val prim_val)
    | Eannot (e, typ) ->
        let unifications, t_expr = type_exp env unifications e in
        let+ typ_ = typ in
        let _kind, typ = type_typ env typ_ in
        unify_types unifications typ t_expr
    | Efun (bindings, body) ->
        type_bindings env unifications bindings body
    | Eappl (func, args) ->
        type_appl env unifications func args
    | Elet (is_rec, pattern, e1, e2) ->
        type_let env unifications is_rec pattern e1 e2
    | Eprod li ->
        let unifications, li =
          li |> List.fold_left_map (type_exp env) unifications
        in
        (unifications, Tprod li)
    | Ercd rcd ->
        let unifications, rcd =
          rcd
          |> List.fold_left_map
               (fun unifications (field, exp) ->
                 let unifications, typ = type_exp env unifications exp in
                 (unifications, (field, typ)) )
               unifications
        in
        (unifications, Trcd rcd)
    | Elab (exp, label) -> (
        let unifications, typ_exp = type_exp env unifications exp in
        let typ_exp = typ_exp |> norm_lazy |> snd in
        match typ_exp with
        | Trcd rcd -> (
          match List.assoc_opt label rcd with
          | Some typ ->
              (unifications, typ)
          | None ->
              failure_typing (`RecordLabel label) typ_exp )
        | _ ->
            failure_typing (`RecordLabel label) typ_exp )
    | Eproj (tuple, index) -> (
        let unifications, typ_tuple = type_exp env unifications tuple in
        match typ_tuple with
        | Tprod tli ->
            let n = List.length tli in
            let index = index - 1 in
            if 0 <= index && index < n then (unifications, List.nth tli index)
            else failure_typing (`OutOfBoundsProj index) typ_tuple
        | _ ->
            failure_typing (`OutOfBoundsProj index) typ_tuple )
    | Epack (styp_wit, exp, typ') -> (
        let+ styp_wit in
        let kind_wit, typ_wit = type_typ env styp_wit in
        let+ typ' in
        let _kind', typ' = type_typ env typ' in
        let unifications, typ_exp = type_exp env unifications exp in
        let typ' = typ' |> norm_lazy |> snd |> expand_def in
        match typ' with
        | Tbind (Texi, ident, kind, typ_exi) ->
            let _kind = unify_kinds styp_wit kind kind_wit in
            let typ_exi = subst_typ ident typ_wit typ_exi in
            let unifications, _typ_exp =
              unify_types unifications typ_exp typ_exi
            in
            (unifications, typ')
        | _ ->
            failure_typing (`NotBinder Sexi) typ' )
    | Eopen (svar, evar, e1, e2) -> (
        let unifications, typ_e1 = type_exp env unifications e1 in
        let typ_e1 = typ_e1 |> norm_lazy |> snd in
        match typ_e1 with
        | Tbind (Texi, ident_exi, kind, typ_exi) -> (
            let cvar = fresh_cvar env svar in
            let env' =
              env
              |> add_svar ~key:svar ~data:cvar
              |> add_cvar ~key:cvar ~data:kind
            in
            let typ_exi = subst_typ ident_exi (Tvar cvar) typ_exi in
            let env' = add_evar env' ~key:evar ~data:typ_exi in
            let unifications, typ_e2 = type_exp env' unifications e2 in
            ( unifications
            , try wf_ctyp env typ_e2
              with Escape cvar ->
                raise Error.(error_unloc (Escaping (typ_e2, cvar))) ) )
        | _ ->
            failure_typing (`NotBinder Sexi) typ_e1 )
  in
  (unifications, t)

(** types [let pattern = e1 in e2] *)
and type_let env unifications is_rec pattern e1 e2 : unifications * ctyp =
  let (env, unifications), typ_pattern =
    type_pattern is_rec (env, unifications) pattern
  in
  let unifications, typ_pattern =
    unify_types unifications typ_pattern (type_shape_exp env e1)
  in
  let env = apply_unification_env env unifications in
  let unifications, typ_exp = type_exp env unifications e1 in
  let unifications, typ_exp = unify_types unifications typ_pattern typ_exp in
  let env = add_pattern_evar env pattern typ_exp in
  let env = apply_unification_env env unifications in
  type_exp env unifications e2

and type_appl env unifications func args : unifications * ctyp =
  let unifications, typ_func = type_exp env unifications func in
  let typ_func = typ_func |> norm_lazy |> snd in
  let rec aux (env, unifications) (typ_func : ctyp)
      (args : (styp_loc, exp) typorexp list) =
    match args with
    | [] ->
        (unifications, typ_func)
    | arg :: args -> (
      match arg with
      | Exp arg -> (
          let unifications, typ_arg = type_exp env unifications arg in
          let uident = fresh_unifiable_cvar () in
          let expected_typ = Tarr (typ_arg, Tvar uident) in
          let unifications, typ_func =
            unify_types unifications typ_func expected_typ
          in
          match typ_func with
          | Tarr (_typ_arg, typ_body) ->
              aux (env, unifications) typ_body args
          | _ ->
              assert false )
      | Typ typ_arg -> (
          let+ typ_arg in
          let _kind_arg, typ_arg = type_typ env typ_arg in
          let typ_func = typ_func |> norm_lazy |> snd |> expand_def in
          match typ_func with
          | Tbind (Tall, ident, _kind, typ_body) ->
              let typ_body =
                typ_body |> refresh_binders env |> subst_typ ident typ_arg
              in
              aux (env, unifications) typ_body args
          | _ ->
              failure_typing (`NotBinder Sall) typ_func ) )
  in
  aux (env, unifications) typ_func args

and type_bindings env unifications bindings body =
  let ftyp, env, unifications =
    List.fold_left
      (fun (ftyp_outer, env, unifications) binding ->
        let ftyp_inner, env = type_binding env unifications binding in
        ((fun typ -> ftyp_outer (ftyp_inner typ)), env, unifications) )
      (Fun.id, env, unifications)
      bindings
  in
  let unifications, typ_body = type_exp env unifications body in
  (unifications, ftyp typ_body)

and type_binding env unifications binding =
  match binding with
  | Typ (ident, kind) ->
      let cvar = fresh_cvar env ident in
      let env =
        env |> add_svar ~key:ident ~data:cvar |> add_cvar ~key:cvar ~data:kind
      in
      ((fun typ_body -> Tbind (Tall, cvar, kind, typ_body)), env)
  | Exp pattern ->
      let (env, unifications), typ_pat =
        type_pattern false (env, unifications) pattern
      in
      let env = apply_unification_env env unifications in
      ( (fun typ_body -> Tarr (typ_pat, typ_body))
      , add_pattern_evar env pattern typ_pat )

let norm_when_eager =
  spec_true "--loose" "Do not force toplevel normalization in eager mode"

let rec typed_decl_of_pattern pat typ =
  let+ patobj = pat in
  match (patobj, typ) with
  | Pvar evar, typ ->
      [Glet (evar, typ)]
  | Ptyp (pat, _), typ ->
      typed_decl_of_pattern pat typ
  | Pprod pats, Tprod typs ->
      List.concat (List.map2 typed_decl_of_pattern pats typs)
  | _ ->
      let m, typ = norm_lazy typ in
      if m then typed_decl_of_pattern pat typ else assert false

let type_dlet env unifications is_rec pattern exp =
  let (env, unifications), typ_pattern =
    type_pattern is_rec (env, unifications) pattern
  in
  let unifications, typ_pattern =
    unify_types unifications typ_pattern (type_shape_exp env exp)
  in
  let env = apply_unification_env env unifications in
  let unifications, typ_exp = type_exp env unifications exp in
  let unifications, typ_exp = unify_types unifications typ_pattern typ_exp in
  let env = add_pattern_evar env pattern typ_exp in
  let env = apply_unification_env env unifications in
  let typ_exp =
    if !norm_when_eager then typ_exp |> norm_if_eager () else typ_exp
  in
  ((env, unifications), typed_decl_of_pattern pattern typ_exp)

let type_decl (env, unifications) decl : (env * unifications) * typed_decl list
    =
  let+ decl in
  match decl with
  | Dlet (is_rec, pattern, exp) ->
      type_dlet env unifications is_rec pattern exp
  | Dtyp (ident, Typ kind) ->
      let cvar = fresh_cvar env ident in
      let env =
        env |> add_svar ~key:ident ~data:cvar |> add_cvar ~key:cvar ~data:kind
      in
      let decl = Gtyp (cvar, Typ kind) in
      ((env, unifications), [decl])
  | Dtyp (svar, Exp typ) ->
      let+ typ in
      let kind, typ = typ |> type_typ env in
      let cvar = fresh_cvar env ~def:{scope= -1; typ} svar in
      let env =
        env |> add_svar ~key:svar ~data:cvar |> add_cvar ~key:cvar ~data:kind
      in
      let typ = if !norm_when_eager then typ |> norm_if_eager () else typ in
      let decl = Gtyp (cvar, Exp (kind, typ)) in
      ((env, unifications), [decl])
  | Dopen (svar, evar, e1) -> (
      let unifications, typ_e1 = type_exp env unifications e1 in
      let typ_e1 = typ_e1 |> norm_lazy |> snd in
      match typ_e1 with
      | Tbind (Texi, ident_exi, kind, typ_exi) ->
          let cvar = fresh_cvar env svar in
          let env' =
            env
            |> add_svar ~key:svar ~data:cvar
            |> add_cvar ~key:cvar ~data:kind
          in
          let typ_exi = subst_typ ident_exi (Tvar cvar) typ_exi in
          let env' = add_evar env' ~key:evar ~data:typ_exi in
          ((env', unifications), [Gopen (cvar, evar, typ_exi)])
      | _ ->
          failure_typing (`NotBinder Sexi) typ_e1 )

let type_program env p : env * typed_decl list =
  let (env, _), li = List.fold_left_map type_decl (env, Tenv.empty) p in
  let li = List.concat li in
  (env, li)

let type_decl env decl =
  let (env, _), decl = type_decl (env, Tenv.empty) decl in
  (env, decl)

(** Initial environment *)

let unit, int, bool, string, bot =
  let unit = Tprod [] in
  let int = Tprim Tint in
  let bool = Tprim Tbool in
  let string = Tprim Tstring in
  let bot =
    let a = svar "#" in
    Tbind (Tall, a, Ktyp, Tvar a)
  in
  (unit, int, bool, string, bot)

let primitive_types =
  [ ("unit", unit)
  ; ("bool", bool)
  ; ("int", int)
  ; ("string", string)
  ; ("bot", bot) ]

let initial_env, initial_program =
  let magic = evar "magic" in
  let p : program =
    let pair (s, t) : decl = !@-(Dtyp (svar s, Exp !@-t)) in
    List.map pair primitive_types
    @ [!@-(Dlet (true, !@-(Ptyp (!@-(Pvar magic), !@-bot)), !@-(Evar magic)))]
  in
  type_program empty_env p
