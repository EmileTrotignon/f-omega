[@@@warning "-27-32-33-37-39-60"]

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
open Mlog

let string_of_ctyp t = Print.(string (typ cvar t))

let string_of_cvar c = Print.(string (cvar c))

let string_of_kind k = Print.(string (kind k))

let string_of_exp e = Print.(string (exp e))

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
             Expected (t, Nonequal t') ) ))

let failure_kinding styp k1 reason =
  match reason with
  | `Shape k2 ->
      meprintf "Could not unify kinds :%s\nwith kind :%s\n" (string_of_kind k1)
        (string_of_kind k2) ;
      raise Error.(error_unloc (Kinding (styp, k1, Nonequal k2)))
  | `NeedArrow ->
      raise Error.(error_unloc (Kinding (styp, k1, Matching Sarr)))

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

let find_evar env x = Eenv.find x env.evar

let find_svar env s = Senv.find s env.svar

(** Functions to modify the environment accordingly. Same semantics as maps,
   except for the order of arguments. *)
let add_evar env x t =
  meprintf "Adding %s : %s in env.evar.\n" (string_of_evar x) (string_of_ctyp t) ;
  {env with evar= Eenv.add x t env.evar}

let add_cvar env a k =
  (* meprintf "Adding %s in env.cvar.\n" (string_of_cvar a) ; *)
  {env with cvar= Tenv.add a k env.cvar}

(** [add_svar] must also deal with shallow bindings *)
let add_svar env s a = {env with svar= Senv.add s a env.svar}

(** [fresh_id_for env a] returns the smallest possible id for variable name
   [a] given the already allocated variables in [env]. Depending on the
   implementation, it may need to store information in env, hence it returns
   a possibly modified version of [env] *)

(** Assuming source type variables never end with an integer, a simple correct
    implementation of [fresh_id_for] *)
let fresh_id_for_T1 env _a = (env, fresh_id ())

let fresh_id_for = fresh_id_for_T1

(** [get_svar env a] is a wrapper around [find_evar env a] that turns a
   [Not_found] exception into a non-localized [Unbound] typing-error
   exception.  These will have to be localized by their calling context,
   using [within_loc]. *)
let get_svar env (a : svar) =
  try find_svar env a with Not_found -> error_unloc (Unbound (Typ (None, a)))

(** May raise non-localized [Unbound] error *)
let get_evar exp env x =
  try find_evar env x with Not_found -> error exp (Unbound (Exp x))

(** 2. Type minimization *)

(** Type checking must perform computation on types when checking for
   convertibilty.  This requires appropriate renamaing to avaid capture,
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
let rec minimize_typ env t = t
(* fix me *)

(** [do_minimize] tells whether types should be minimized. It defaults to
   [true] and may be changed with the `--rawtypes` command line option, *)
let do_minimize = spec_true "--rawtypes" "Do not minimize types"

let minimize_typ env t =
  if !do_minimize then minimize_typ (env, Tenv.empty) t else t

let norm_def {typ; scope} = {typ= norm typ; scope}

let fresh_cvar env ?def ?unifiable svar =
  let def = Option.map norm_def def in
  let rec pick_id id =
    let candidate = cvar ~id ?def ?unifiable svar in
    if not @@ Tenv.mem candidate env.cvar then candidate else pick_id (id + 1)
  in
  pick_id 0

let fresh_unifiable_cvar =
  let id = ref (-1) in
  let svar = svar "unif" in
  fun () ->
    incr id ;
    cvar ~id:!id ~unifiable:true svar

let refresh_cvar env ?def ?unifiable cvar =
  fresh_cvar env ?def ?unifiable (svar cvar.name)

let rec refresh_cvars env su typ =
  match typ with
  | Tvar a ->
      Tvar (match Tenv.find_opt a su with Some a -> a | None -> a)
  | Tprim prim_typ ->
      Tprim prim_typ
  | Tapp (tfunc, targ) ->
      Tapp (refresh_cvars env su tfunc, refresh_cvars env su targ)
  | Tprod t_li ->
      Tprod (t_li |> List.map (refresh_cvars env su))
  | Trcd rdc ->
      Trcd (rdc |> map_snd (refresh_cvars env su))
  | Tarr (t1, t2) ->
      Tarr (refresh_cvars env su t1, refresh_cvars env su t2)
  | Tbind (binder, ident, kind, typ) ->
      let ident' = refresh_cvar env ident in
      let su = Tenv.add ident ident' su in
      let env = add_cvar env ident' kind in
      (* todo check correctness *)
      Tbind (binder, ident', kind, refresh_cvars env su typ)

let refresh_cvars env typ =
  let typ' = refresh_cvars env Tenv.empty typ in
  meprintf "refreshed %s is %s\n" (string_of_ctyp typ) (string_of_ctyp typ') ;
  typ'

(** [type_typ env t] typechecks source type [t] returning its kind [k] and
   an internal representation of [t].  This may non-localized (Unbound and
   Kinding) typing error exceptions. *)
let rec type_typ env (t : styp) : kind * ctyp =
  (* meprintf "typing %s\n" Print.(string (typ svar t)) ; *)
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
                 let kind, ctyp = type_typ env typ in
                 ctyp ) ) )
  | Trcd rcd ->
      ( Ktyp
      , Trcd
          ( rcd
          |> List.map (fun (field, typ) ->
                 let kind, ctyp = type_typ env typ in
                 (field, ctyp) ) ) )
  | Tarr (t1, t2) ->
      let kind, t1 = type_typ env t1 in
      let kind, t2 = type_typ env t2 in
      (Ktyp, Tarr (t1, t2))
  | Tbind (Tlam, ident, kind_input, typ) ->
      let cident = fresh_cvar env ident in
      let env = add_svar env ident cident in
      let env = add_cvar env cident kind_input in
      let kind2, typ = type_typ env typ in
      (Karr (kind_input, kind2), Tbind (Tlam, cident, kind_input, typ))
  | Tbind (binder, ident, kind_input, typ) ->
      let cident = fresh_cvar env ident in
      let env = add_svar env ident cident in
      let env = add_cvar env cident kind_input in
      let kind_output, typ = type_typ env typ in
      (kind_output, Tbind (binder, cident, kind_input, typ))

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

let eq_cvar c1 c2 = c1.name = c2.name && c1.id = c2.id

let rec wf_ctyp env t : ctyp =
  match t with
  | Tvar a -> (
      let a =
        Option.value ~default:a
          (Option.map fst @@ Tenv.find_first_opt (eq_cvar a) env.cvar)
      in
      if (* fix me *)
         Tenv.mem a env.cvar then t
      else match a.def with Some _ -> t | None -> raise (Escape a) )
  | Tprim prim_typ ->
      Tprim prim_typ
  | Tapp (tfunc, targ) ->
      Tapp (wf_ctyp env tfunc, wf_ctyp env targ)
  | Tprod t_li ->
      Tprod (t_li |> List.map (wf_ctyp env))
  | Trcd rdc ->
      Trcd (rdc |> List.map (fun (field, typ) -> (field, wf_ctyp env typ)))
  | Tarr (t1, t2) ->
      Tarr (wf_ctyp env t1, wf_ctyp env t2)
  | Tbind (binder, ident, kind, typ) ->
      let env = add_cvar env ident kind in
      (* todo check correctness *)
      Tbind (binder, ident, kind, wf_ctyp env typ)

let wf_ctyp env t : ctyp =
  let t = norm t in
  meprintf "Well formedness of type %s\n" (string_of_ctyp t) ;
  wf_ctyp env t

type unifications = ctyp Tenv.t

let string_of_unifications un =
  let buffer = Buffer.create 256 in
  Tenv.iter
    (fun cvar typ ->
      Buffer.add_string buffer
        (sprintf " (%s <== %s)" (string_of_cvar cvar) (string_of_ctyp typ)) )
    un ;
  Buffer.contents buffer

let get_unified unifications ident = Tenv.find_opt ident unifications

let sort_rcd rcd =
  List.sort (fun (field, _) (field', _) -> String.compare field field') rcd

let norm_eager = norm

let norm () = if !eager then norm else fun t -> snd (norm_lazy t)

let rec unify_types unifications t1 t2 : ctyp Tenv.t * ctyp =
  (* (meprintf "Intermediate : Trying to unify type : \n%s\n and \n%s\n"
      (string_of_ctyp t1) )
     (string_of_ctyp t2) ; *)
  if t1 == t2 then (unifications, t1)
  else
    let unifications, typ =
      match (t1, t2) with
      | Tvar ident, Tvar ident' when eq_cvar ident ident' ->
          meprintf "branch Tvar ident, Tvar ident' when eq_cvar ident ident'\n" ;
          (unifications, Tvar ident)
      | Tvar ident, typ when ident.unifiable ->
          meprintf "branch 3\n" ;
          unify_idents unifications ident typ
      | typ, Tvar ident when ident.unifiable ->
          meprintf "branch 4\n" ;
          unify_idents unifications ident typ
      | (Tvar {def= Some {typ= t1; _}; _} as keep_var), t2
      | t2, (Tvar {def= Some {typ= t1; _}; _} as keep_var) ->
          meprintf
            "branch (Tvar {def= Some {typ; _}; _}), _ | _, (Tvar {def= Some \
             {typ; _}; _})\n" ;
          let n_unif = Tenv.cardinal unifications in
          let unifications, t =
            unify_types unifications (norm () t1) (norm () t2)
          in
          let new_n_unif = Tenv.cardinal unifications in
          (unifications, if n_unif = new_n_unif then keep_var else t)
      | Tapp (tfunc, targ), Tapp (tfunc', targ') ->
          (* meprintf "branch Tapp (_, _), Tapp (_, _)\n" ; *)
          if not !eager then
            let eliminated_app1, t1' = norm_lazy t1 in
            let eliminated_app2, t2' = norm_lazy t2 in
            if eliminated_app1 || eliminated_app2 then
              unify_types unifications t1' t2'
            else
              let unifications, tfunc = unify_types unifications tfunc tfunc' in
              let unifications, targ = unify_types unifications targ targ' in
              (unifications, Tapp (tfunc, targ))
          else
            let unifications, tfunc = unify_types unifications tfunc tfunc' in
            let unifications, targ = unify_types unifications targ targ' in
            (unifications, Tapp (tfunc, targ))
      | ((Tapp (_, _) as t1), t2 | t2, (Tapp (_, _) as t1)) when not !eager ->
          meprintf "branch (Tapp (_, _), _ | _, Tapp (_, _)) when not !eager\n" ;
          meprintf "lazy extra normalisation\n" ;
          let eliminated_app1, t1' = norm_lazy t1 in
          if eliminated_app1 then unify_types unifications t1' t2
          else failure_typing (`Shape t2) t1
      | Tprim prim_typ, Tprim prim_typ' ->
          meprintf "branch 8\n" ;
          if prim_typ = prim_typ' then (unifications, Tprim prim_typ)
          else (* todo better reason *) failure_typing (`Shape t2) t1
      | Tprod t_li, Tprod t_li' ->
          meprintf "branch 9\n" ;
          let unifications, t_li =
            fold_left_map_unify unify_types unifications t_li t_li'
          in
          (unifications, Tprod t_li)
      | Trcd rcd, Trcd rcd' ->
          meprintf "branch 10\n" ;
          if List.length rcd <> List.length rcd' then
            failure_typing (`Shape t2) t1
          else
            let rcd = sort_rcd rcd in
            let rcd' = sort_rcd rcd' in
            let unifications, rcd =
              fold_left_map_unify
                (fun unifications (field, t) (field', t') ->
                  if field <> field' then failure_typing (`Shape t2) t1 ;
                  let unifications, t = unify_types unifications t t' in
                  (unifications, (field, t)) )
                unifications rcd rcd'
            in
            (unifications, Trcd rcd)
      | Tarr (targ, tbody), Tarr (targ', tbody') ->
          meprintf "branch 11\n" ;
          let unifications, targ = unify_types unifications targ targ' in
          let unifications, tbody = unify_types unifications tbody tbody' in
          (unifications, Tarr (targ, tbody))
      | Tbind (binder, ident, kind, typ), Tbind (binder', ident', kind', typ')
        when binder = binder' && eq_kind kind kind' ->
          meprintf "branch 12\n" ;
          let typ, ident, typ', ident' =
            if ident'.unifiable then (typ, ident, typ', ident')
            else (typ', ident', typ, ident)
          in
          let ntyp' = subst_typ ident' (Tvar ident) typ' in
          meprintf "Subst : %s became %s\n" (string_of_ctyp typ')
            (string_of_ctyp ntyp') ;
          let typ' = ntyp' in
          let unifications, typ =
            unify_types (Tenv.remove ident unifications) typ typ'
          in
          (unifications, Tbind (binder, ident, kind, typ))
      | t1, t2 ->
          meprintf "failing unification because of shape\n" ;
          failure_typing (`Shape t2) t1
    in
    (* meprintf "Successfully unified %s and %s\ninto : %s.\n" (string_of_ctyp t1)
       (string_of_ctyp t2) (string_of_ctyp typ) ; *)
    (unifications, typ)

and unify_idents unifications ident t =
  match get_unified unifications ident with
  | Some typ ->
      unify_types unifications typ t
  | None when ident.unifiable ->
      meprintf "add unification : %s <- %s\n" (string_of_cvar ident)
        (string_of_ctyp t) ;
      let unifications = Tenv.add ident t unifications in
      meprintf "unifications = %s\n" (string_of_unifications unifications) ;
      (unifications, t)
  | None -> (
    match ident.def with
    | Some {typ; _} ->
        unify_types unifications typ t
    | None ->
        failure_typing (`Shape t) (Tvar ident) )

let unify_types env unifications t1 t2 =
  if t1 == t2 then (unifications, norm () t1)
  else
    let t1 = norm () t1 in
    let t2 = norm () t2 in
    meprintf "Trying to unify \n%s\nand\n%s\n" (string_of_ctyp t1)
      (string_of_ctyp t2) ;
    let unifications, typ = unify_types unifications t1 t2 in
    let typ_subst = subst unifications typ in
    meprintf
      "Successfully unified \n%s\nand\n%s\ninto :\n%s\nsubsts into :%s.\n"
      (string_of_ctyp t1) (string_of_ctyp t2) (string_of_ctyp typ)
      (string_of_ctyp typ_subst) ;
    (unifications, subst unifications typ_subst)

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

let ( !@ ) = Locations.with_loc

let ( !@- ) = Locations.dummy_located

let type_prim_val = function
  | Int _ ->
      Tprim Tint
  | String _ ->
      Tprim Tstring
  | Bool _ ->
      Tprim Tbool

let rec type_pattern is_rec (env, unifications) (pat : pat) =
  let type_pattern = type_pattern is_rec in
  let+ pat in
  match pat with
  | Ptyp (pat, typ_annot) ->
      let+ typ_annot in
      let _kind, typ_annot = type_typ env typ_annot in
      let (env, unifications), typ_pat = type_pattern (env, unifications) pat in
      meprintf "unification for pattern annotation\n" ;
      let unifications, typ = unify_types env unifications typ_pat typ_annot in
      ((env, unifications), typ)
  | Pvar ident ->
      let uident = fresh_unifiable_cvar () in
      let typ = Tvar uident in
      let env =
        if is_rec then (
          meprintf "adding evar for pattern type\n" ;
          add_evar env ident typ )
        else env
      in
      ((env, unifications), typ)
  | Pprod li ->
      let (env, unifications), li =
        List.fold_left_map type_pattern (env, unifications) li
      in
      ((env, unifications), Tprod li)
  | Pprim prim_val ->
      ((env, unifications), type_prim_val prim_val)

let type_pattern is_rec (env, unifications) pattern =
  let (env, unifications), t =
    type_pattern is_rec (env, unifications) pattern
  in
  meprintf "typing pattern : %s has type %s\n"
    Print.(string (pat pattern))
    (string_of_ctyp t) ;
  ((env, unifications), t)

(** add the type of variables from pat assuming that pattern has type typ. *)
let rec add_pattern_evar env pat typ =
  let+ pat in
  match (pat, typ) with
  | Pvar evar, typ ->
      meprintf "adding evar for add_pattern_evar : %s : %s\n"
        (string_of_evar evar) (string_of_ctyp typ) ;
      add_evar env evar typ
  | Ptyp (pat, _), typ ->
      add_pattern_evar env pat typ
  | Pprod pats, Tprod typs ->
      List.fold_left2 add_pattern_evar env pats typs
  | _ ->
      assert false

let rec type_exp env unifications exp : unifications * ctyp =
  meprintf "exp typing : %s\n" (string_of_exp exp) ;
  let+ exp_ = exp in
  let unifications, t =
    match exp_ with
    | Evar x ->
        (unifications, get_evar exp env x)
    | Eprim prim_val ->
        (unifications, type_prim_val prim_val)
    | Eannot (e, typ) ->
        let unifications, t_expr = type_exp env unifications e in
        let t_expr = norm () t_expr in
        let+ typ_ = typ in
        let kind, typ = type_typ env typ_ in
        let typ = norm () typ in
        unify_types env unifications t_expr typ
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
        let typ_exp = norm () typ_exp in
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
        let kind', typ' = type_typ env typ' in
        let unification, typ_exp = type_exp env unifications exp in
        let typ' = norm () typ' in
        match typ' with
        | Tbind (Texi, ident, kind, typ_exi) ->
            let _kind = unify_kinds styp_wit kind kind_wit in
            let typ_exi = subst_typ ident typ_wit typ_exi in
            let unifications, _typ_exp =
              unify_types env unifications typ_exp typ_exi
            in
            (unifications, typ')
        | _ ->
            failure_typing (`NotBinder Sexi) typ' )
    | Eopen (svar, evar, e1, e2) -> (
        let unifications, typ_e1 = type_exp env unifications e1 in
        let typ_e1 = norm () typ_e1 in
        meprintf "Typing open :\nsvar=%s\nevar=%s\ne1=%s\ne1:%s\ne2=%s"
          (string_of_svar svar) (string_of_evar evar) (string_of_exp e1)
          (string_of_ctyp typ_e1) (string_of_exp e2) ;
        match typ_e1 with
        | Tbind (Texi, ident_exi, kind, typ_exi) -> (
            let cvar = fresh_cvar env svar in
            let env' = add_svar env svar cvar in
            let env' = add_cvar env' cvar kind in
            let typ_exi = subst_typ ident_exi (Tvar cvar) typ_exi in
            let env' = add_evar env' evar typ_exi in
            meprintf "Typ exi = %s\n" (string_of_ctyp typ_exi) ;
            let unifications, typ_e2 = type_exp env' unifications e2 in
            ( unifications
            , try wf_ctyp env typ_e2
              with Escape cvar ->
                raise Error.(error_unloc (Escaping (typ_e2, cvar))) ) )
        | _ ->
            failure_typing (`NotBinder Sexi) typ_e1 )
  in
  meprintf "- exp :\n%s\n- has type :\n%s\n" (string_of_exp exp)
    (string_of_ctyp t) ;
  (unifications, t)

and type_let env unifications is_rec pattern e1 e2 : unifications * ctyp =
  let (env, unifications), typ_pattern =
    type_pattern is_rec (env, unifications) pattern
  in
  let unifications, typ_e1 = type_exp env unifications e1 in
  let unifications, typ_e1 = unify_types env unifications typ_pattern typ_e1 in
  let env = apply_unification_env env unifications in
  let env = add_pattern_evar env pattern typ_e1 in
  type_exp env unifications e2

and type_appl env unifications func args : unifications * ctyp =
  let unifications, typ_func = type_exp env unifications func in
  let typ_func = norm () typ_func in
  let rec aux (env, unifications) (typ_func : ctyp)
      (args : (styp_loc, exp) typorexp list) =
    match args with
    | [] ->
        (unifications, norm () typ_func)
    | arg :: args -> (
        (meprintf "applying %s to %s\n" (string_of_ctyp typ_func))
          ( match arg with
          | Typ typ_arg ->
              Print.(string @@ typ svar typ_arg.obj)
          | Exp arg ->
              string_of_exp arg ) ;
        match arg with
        | Exp arg -> (
            let unifications, typ_arg = type_exp env unifications arg in
            let uident = fresh_unifiable_cvar () in
            let expected_typ = Tarr (typ_arg, Tvar uident) in
            meprintf
              "unification for exp func appl. function is : %s, arg is %s\n\
               type of function is :\n\
               %s\n\
               and type of argument is :\n\
               %s\n"
              (string_of_exp func) (string_of_exp arg) (string_of_ctyp typ_func)
              (string_of_ctyp typ_arg) ;
            let unifications, typ_func =
              unify_types env unifications typ_func expected_typ
            in
            match typ_func with
            | Tarr (typ_arg, typ_body) ->
                aux (env, unifications) typ_body args
            | _ ->
                assert false )
        | Typ typ_arg -> (
            let+ typ_arg in
            let kind_arg, typ_arg = type_typ env typ_arg in
            let typ_func = norm () typ_func in
            match typ_func with
            | Tbind (Tall, ident, kind, typ_body) ->
                let new_cvar =
                  fresh_cvar env ~def:{scope= -1; typ= typ_arg}
                    (svar ident.name)
                in
                let env = add_cvar env new_cvar kind in
                let typ_body = refresh_cvars env typ_body in
                let typ_body = subst_typ ident (Tvar new_cvar) typ_body in
                aux (env, unifications) typ_body args
            | _ ->
                failure_typing (`NotBinder Sall) typ_func ) )
  in
  aux (env, unifications) typ_func args

and type_bindings env unifications bindings body =
  let ftyp, env, unifications =
    List.fold_left
      (fun (ftyp_inner, env, unifications) binding ->
        let ftyp_outer, env = type_binding env unifications binding in
        ((fun typ -> ftyp_inner (ftyp_outer typ)), env, unifications) )
      (Fun.id, env, unifications)
      bindings
  in
  let unifications, typ_body = type_exp env unifications body in
  (unifications, ftyp typ_body)

and type_binding env unifications binding =
  match binding with
  | Typ (ident, kind) ->
      let cvar = fresh_cvar env ident in
      let env = add_svar env ident cvar in
      let env = add_cvar env cvar kind in
      ((fun typ_body -> Tbind (Tall, cvar, kind, typ_body)), env)
  | Exp pattern ->
      let (env, unifications), typ_pat =
        type_pattern false (env, unifications) pattern
      in
      meprintf "Hey there 2, %s\n" (string_of_ctyp typ_pat) ;
      let env = apply_unification_env env unifications in
      ( (fun typ_body -> Tarr (typ_pat, typ_body))
      , add_pattern_evar env pattern typ_pat )

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
              (* let (_env, _unif), typ_pattern =
                   type_pattern true (env, Tenv.empty) pattern
                 in *)
              Tarr (Tvar (fresh_unifiable_cvar ()), aux env bindings)
          | Typ (svar, kind) ->
              let cvar = fresh_cvar env svar in
              Tbind (Tall, cvar, kind, aux env bindings) )
      in
      aux env bindings
  | Elet (is_rec, pat, e1, e2) ->
      type_shape_exp env e2
  | Eprod eli ->
      Tprod (eli |> List.map (type_shape_exp env))
  | _ ->
      Tvar (fresh_unifiable_cvar ())

let type_shape_exp env exp =
  let t = type_shape_exp env exp in
  meprintf "type_exp_func : %s type to %s\n" (string_of_exp exp)
    (string_of_ctyp t) ;
  t

let norm_when_eager =
  spec_true "--loose" "Do not force toplevel normalization in eager mode"

let type_dlet env unifications is_rec pattern exp =
  meprintf "location %s%s\n\n"
    (Locations.string_loc pattern.loc)
    (Locations.string_of_loc pattern.loc) ;
  let (env, unifications), typ_pattern =
    type_pattern is_rec (env, unifications) pattern
  in
  let unifications, type_pattern =
    unify_types env unifications typ_pattern (type_shape_exp env exp)
  in
  let env = apply_unification_env env unifications in
  let unifications, typ_exp = type_exp env unifications exp in
  let unifications, typ_exp =
    unify_types env unifications typ_exp typ_pattern
  in
  meprintf "Hey there, %s\n" (string_of_ctyp typ_exp) ;
  let env = add_pattern_evar env pattern typ_exp in
  let env = apply_unification_env env unifications in
  meprintf "adding %s : %s\n"
    Print.(string (pat pattern))
    (string_of_ctyp typ_exp) ;
  ((env, unifications), Glet (pattern, typ_exp))

let type_decl (env, unifications) decl : (env * unifications) * typed_decl =
  let+ decl in
  match decl with
  | Dlet (is_rec, pattern, exp) ->
      type_dlet env unifications is_rec pattern exp
  | Dtyp (ident, Typ kind) ->
      let cvar = fresh_cvar env ident in
      let env = add_svar env ident cvar in
      let env = add_cvar env cvar kind in
      let decl = Gtyp (cvar, Typ kind) in
      ((env, unifications), decl)
  | Dtyp (svar, Exp typ) ->
      let+ typ in
      let kind, typ = type_typ env typ in
      let typ = norm () typ in
      let cvar = fresh_cvar env ~def:{scope= -1; typ} svar in
      let env = add_svar env svar cvar in
      let env = add_cvar env cvar kind in
      let decl = Gtyp (cvar, Exp (kind, typ)) in
      ((env, unifications), decl)
  | Dopen (svar, evar, e1) -> (
      let unifications, typ_e1 = type_exp env unifications e1 in
      let typ_e1 = norm () typ_e1 in
      meprintf "Typing Dopen :\nsvar=%s\nevar=%s\ne1=%s\ne1:%s\n"
        (string_of_svar svar) (string_of_evar evar) (string_of_exp e1)
        (string_of_ctyp typ_e1) ;
      match typ_e1 with
      | Tbind (Texi, ident_exi, kind, typ_exi) ->
          let cvar = fresh_cvar env svar in
          let env' = add_svar env svar cvar in
          let env' = add_cvar env' cvar kind in
          let typ_exi = subst_typ ident_exi (Tvar cvar) typ_exi in
          let env' = add_evar env' evar typ_exi in
          meprintf "Typ exi = %s\n" (string_of_ctyp typ_exi) ;
          ((env', unifications), Gopen (cvar, evar, typ_exi))
      | _ ->
          failwith
            (sprintf "unpacking something that is not existantial = %s : %s"
               (string_of_exp e1) (string_of_ctyp typ_e1) ) )

let type_program env p : env * typed_decl list =
  let (env, _), li = List.fold_left_map type_decl (env, Tenv.empty) p in
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
