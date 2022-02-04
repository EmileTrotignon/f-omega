open Syntax

(** Module [Tenv] implements map from (internal) type variables, hence, take
   both id and name for comparisson (the def field is ignored).  Internal
   variiables do not shadow one another. This map is used for several
   purposes: checking well-formedness, renamings, substitutions. *)
module Tenv : sig
  include Map.S

  val map_key : (key -> key) -> 'a t -> 'a t

end
with type key = cvar

val eq_kind : kind -> kind -> bool
(** Implements kind equality, whose definition is trivial. *)

val subst : ctyp Tenv.t -> ctyp -> ctyp
(** [subst su t] returns the result of applying the substitution [su]
   encoding as a maping of type [ctyp Tenv.t]. *)

val subst_typ : Tenv.key -> ctyp -> ctyp -> ctyp
(** [subst su t] returns the result of applying the substitution [su]
   encoding as a maping of type [ctyp Tenv.t]. *)

val eager : bool ref
(** This opton tells whether to compute full normal forms and expand type
   definitions eagerly (when [true]), or lazily (when [false]), i.e. just
   compute head normal forms and expand type definitions on demand.  This
   option defaults to [false]. It can be changed using the `--eager` command
   line option.  Until lazy evaluation is implemented, this option may be
   ignored, defaulting to eager computation.  *)

val norm : ctyp -> ctyp
(** [norm t] returns a type equivalent to [t] but in normal form. *)


val norm_lazy : ctyp -> ctyp
(** [norm_lazy t] returns a type equivalent to [t] but in normal form. *)

val eq_typ : ctyp -> ctyp -> bool
(** [eq_typ t1 t2] just checks where [t1] and [t2] are equal. It has no
   visible side effect. *)

val diff_typ : ctyp -> ctyp -> (ctyp * ctyp) option
(** [diff_typ t1 t2] returns None when both [t1] and [t2] are equal;
   othewise, it returns [Some (s1, s2)] where [s1] and [s2] are subterms of
   [t1] and [t2] that witness a difference between them . *)

(** Module [Senv] implement a map from svar. *)
module Senv : Map.S with type key = svar

(** Module [Eenv] implement a map from evar. *)
module Eenv : Map.S with type key = evar
