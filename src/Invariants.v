(** Invariants.
  States some invariants of R’s heap. **)

(* Copyright © 2018 Martin Bodin

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301 USA *)

Set Implicit Arguments.
Require Import TLC.LibBag Paco.paco.
Require Export Path MonadTactics.

Open Scope list_scope. (* FIXME: How to disable some notations of LibBag? *)


(** * Predicates about the memory **)

(** ** Valid pointers **)

(** A pointer is valid if it is bound to an object.
  The predicate [bound_such_that] allows us to state some
  properties of the pointed object. **)

Definition bound_such_that (S : state) P p :=
  exists p_, read_SExp S p = Some p_ /\ P p_.

Definition bound S := bound_such_that S (fun _ => True).


(** ** Typed pointers **)

(** The predicate [may_have_types S l p] states that
  the pointer [p] may only be associated with an object
  whose type is in the list [l] in the heap [S]. **)

Definition may_have_types S l :=
  bound_such_that S (fun p_ => type p_ \in l).


(** ** List pointers **)

(** Along the structures that frequently appear in R’s source code,
  lists are one of the most used.
  We this provide special predicates to manipulate them. **)

Definition list_type_head_such_that P Pheader Pcar Ptag S l_t l_car l_tag (p_ : SExpRec) :=
  exists header car cdr tag,
    p_ = make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag)
    /\ type p_ \in l_t /\ Pheader header
    /\ may_have_types S l_car car /\ Pcar car
    /\ P S l_t l_car l_tag cdr
    /\ may_have_types S l_tag tag /\ Ptag tag.

Definition list_type_step_such_that P Pheader Pcar Ptag (S : state) l_t l_car l_tag :=
  bound_such_that S (list_type_head_such_that P Pheader Pcar Ptag S l_t l_car l_tag).

Inductive list_type_such_that Pheader Pcar Ptag (S : state) : list SExpType -> list SExpType -> list SExpType -> SEXP -> Prop :=
  | list_type_nil : forall p l_t l_car l_tag,
    may_have_types S ([NilSxp]) p ->
    list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag p
  | list_type_cons : forall p l_t l_car l_tag,
    list_type_step_such_that (list_type_such_that Pheader Pcar Ptag) Pheader Pcar Ptag S l_t l_car l_tag p ->
    list_type_such_that Pheader Pcar Ptag S l_t l_car l_tag p
  .

Definition list_head_such_that Pheader Pcar Ptag :=
  list_type_head_such_that (list_type_such_that Pheader Pcar Ptag) Pheader Pcar Ptag.

(** The predicate [list_type S l_t l_car l_tag p] states that in the heap [S],
  the pointer [p] points to a list.
  Furthermore, each element of this list has its type in [l_t], with the expection
  of the last element, which is of type [NilSxp] (and is unique in R’s memory).
  The ypical value for [l_t] is [[ListSxp]], but R sometimes manipulates lists
  whose types are either [LangSxp] and [ListSxp] (typically the first element is
  [LangSxp] and the next ones are [ListSxp]).
  Furthermore, the “car” elements of the list [p] must be of type in [l_car],
  and the “tag” elements of type in [l_tag].
  The predicate [list_head S l_t l_car l_tag p_] applies to an object [p_]
  instead of a pointer [p], but states a very similar statement. **)

Definition list_type := list_type_such_that (fun _ => True) (fun _ => True) (fun _ => True).
Definition list_head := list_head_such_that (fun _ => True) (fun _ => True) (fun _ => True).


(** * Invariants about the state **)

(** ** NULL pointer exceptions **)

(** R very rarely uses C’s NULL pointer. It instead uses a single object
  of type [NilSxp].
  But there are exceptions to this. The following predicates lists where
  such NULL pointer can appear.  Such NULL pointer are of course invalid
  and can not be read.
  It is however possible that these exceptions still store a non-NULL
  pointer.  In such cases, the pointer has to be valid. **)

Inductive null_pointer_exceptions_entry_point : entry_point -> Prop :=
  | null_pointer_exceptions_context_promargs :
    null_pointer_exceptions_entry_point
      (Econtext (context_path_entry Pstate_context) Scontext_promargs)
  | null_pointer_exceptions_context_callfun :
    null_pointer_exceptions_entry_point
      (Econtext (context_path_entry Pstate_context) Scontext_callfun)
  | null_pointer_exceptions_context_sysparent :
    null_pointer_exceptions_entry_point
      (Econtext (context_path_entry Pstate_context) Scontext_sysparent)
  | null_pointer_exceptions_context_call :
    null_pointer_exceptions_entry_point
      (Econtext (context_path_entry Pstate_context) Scontext_call)
  | null_pointer_exceptions_context_cloenv :
    null_pointer_exceptions_entry_point
      (Econtext (context_path_entry Pstate_context) Scontext_cloenv)
  | null_pointer_exceptions_context_conexit :
    null_pointer_exceptions_entry_point
      (Econtext (context_path_entry Pstate_context) Scontext_conexit)
  | null_pointer_exceptions_context_returnValue : forall cp,
    null_pointer_exceptions_entry_point (Econtext cp Scontext_returnValue)
  .

Inductive null_pointer_exceptions_suffix : path_step -> Prop :=
  | null_pointer_symbol_value :
    null_pointer_exceptions_suffix (SNonVectorSym Ssym_value)
  (* FIXME: BindData_ans_ptr *)
  (* FIXME: BindData_ans_names *)
  .

Inductive null_pointer_exceptions_path : path -> Prop :=
  | null_pointer_exceptions_path_entry_point : forall e,
    null_pointer_exceptions_entry_point e ->
    null_pointer_exceptions_path (Pentry e)
  | null_pointer_exceptions_path_suffix : forall s p,
    null_pointer_exceptions_suffix s ->
    Path.last p s ->
    null_pointer_exceptions_path p
  .

Inductive null_pointer_exceptions_globals : GlobalVariable -> Prop := .


(** ** Invariants **)

(** A safe offset is defined as one linked with a function in the
  [R_FunTab] array. **)
Definition safe_offset n := forall max_step globals S,
  result_prop (fun _ _ => True) (fun _ => True) (fun _ _ _ => True)
    (read_R_FunTab (runs max_step globals) S n).

(** The invariants defined in this file are about types.
  We here states for each R’s type how its field should be typed.
  For instance, the “cdr” field of a list is either of type
  [ListSxp] or [NilSxp]. **)

Inductive safe_SExpRec_type S : SExpType -> SExpRec -> Prop :=
  | SExpType_corresponds_to_data_NilSxp : forall header car cdr tag,
      may_have_types S ([NilSxp]) car ->
      may_have_types S ([NilSxp]) cdr ->
      may_have_types S ([NilSxp]) tag ->
      safe_SExpRec_type S NilSxp (make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag))
  | SExpType_corresponds_to_data_SymSxp : forall header pname value internal,
      may_have_types S ([CharSxp]) pname ->
      may_have_types S ([NilSxp ; BuiltinSxp ; SpecialSxp]) internal ->
      safe_SExpRec_type S SymSxp (make_NonVector_SExpRec header (make_SymSxp_struct pname value internal))
  | SExpType_corresponds_to_data_ListSxp : forall header car cdr tag,
      (* FIXME: As-is, there is no hypothesis stating that the list is finite. Do we want it? *)
      may_have_types S all_storable_SExpTypes car ->
      may_have_types S ([NilSxp ; ListSxp]) cdr ->
      may_have_types S ([NilSxp ; CharSxp]) tag ->
      safe_SExpRec_type S ListSxp (make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag))
  | SExpType_corresponds_to_data_CloSxp : forall header formals body env,
      list_type S ([ListSxp]) ([SymSxp]) ([NilSxp ; CharSxp]) formals ->
      may_have_types S ([NilSxp ; SymSxp ; ListSxp ; EnvSxp ; PromSxp ; LangSxp ; CharSxp ; LglSxp ; IntSxp ; RealSxp ; CplxSxp ; StrSxp ; VecSxp ; BcodeSxp ; ExtptrSxp ; WeakrefSxp ; RawSxp ; S4Sxp ]) body ->
      may_have_types S ([EnvSxp]) env ->
      safe_SExpRec_type S CloSxp (make_NonVector_SExpRec header (make_CloSxp_struct formals body env))
  | SExpType_corresponds_to_data_EnvSxp : forall header frame enclos,
      may_have_types S ([NilSxp; ListSxp]) frame ->
      may_have_types S ([NilSxp ; EnvSxp]) enclos ->
      safe_SExpRec_type S EnvSxp (make_NonVector_SExpRec header (make_EnvSxp_struct frame enclos))
  | SExpType_corresponds_to_data_PromSxp : forall header value expr env,
      may_have_types S all_storable_SExpTypes value ->
      may_have_types S all_storable_SExpTypes expr ->
      may_have_types S ([EnvSxp]) env ->
      safe_SExpRec_type S PromSxp (make_NonVector_SExpRec header (make_PromSxp_struct value expr env))
  | SExpType_corresponds_to_data_LangSxp : forall header car cdr tag,
      may_have_types S all_storable_SExpTypes car ->
      may_have_types S ([NilSxp ; ListSxp]) cdr ->
      may_have_types S ([NilSxp ; CharSxp]) tag ->
      safe_SExpRec_type S LangSxp (make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag))
  | SExpType_corresponds_to_data_SpecialSxp : forall header offset,
      safe_offset offset ->
      safe_SExpRec_type S SpecialSxp (make_NonVector_SExpRec header (make_PrimSxp_struct offset))
  | SExpType_corresponds_to_data_BuiltinSxp : forall header offset,
      safe_offset offset ->
      safe_SExpRec_type S BuiltinSxp (make_NonVector_SExpRec header (make_PrimSxp_struct offset))
  | SExpType_corresponds_to_data_CharSxp : forall header array,
      safe_SExpRec_type S CharSxp
        (SExpRec_VectorChar (make_Vector_SExpRec header
          (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array)))
  | SExpType_corresponds_to_data_LglSxp : forall header array,
      safe_SExpRec_type S LglSxp
        (SExpRec_VectorLogical (make_Vector_SExpRec header
          (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array)))
  | SExpType_corresponds_to_data_IntSxp : forall header array,
      safe_SExpRec_type S IntSxp
        (SExpRec_VectorInteger (make_Vector_SExpRec header
          (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array)))
  | SExpType_corresponds_to_data_RealSxp : forall header array,
      safe_SExpRec_type S RealSxp
        (SExpRec_VectorReal (make_Vector_SExpRec header
          (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array)))
  | SExpType_corresponds_to_data_CplxSxp : forall header array,
      safe_SExpRec_type S CplxSxp
        (SExpRec_VectorComplex (make_Vector_SExpRec header
           (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array)))
  | SExpType_corresponds_to_data_StrSxp : forall header array,
      (forall a,
        Mem a (ArrayList.to_list array) ->
        may_have_types S ([CharSxp]) a) ->
      safe_SExpRec_type S StrSxp
        (SExpRec_VectorPointer (make_Vector_SExpRec header
          (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array)))
  | SExpType_corresponds_to_data_DotSxp : forall header car cdr tag,
      may_have_types S all_storable_SExpTypes car ->
      may_have_types S ([NilSxp ; ListSxp ; DotSxp]) cdr ->
      may_have_types S ([NilSxp ; CharSxp]) tag ->
      safe_SExpRec_type S DotSxp (make_NonVector_SExpRec header (make_ListSxp_struct car cdr tag))
  (** The type [AnySxp] does not appear as the type of a C object,
    Thus no constructor is associated to this type. **)
  | SExpType_corresponds_to_data_VecSxp : forall header array,
      (forall a,
        Mem a (ArrayList.to_list array) ->
        may_have_types S ([LglSxp ; IntSxp ; RealSxp ; CplxSxp ; StrSxp ; RawSxp]) a) ->
      safe_SExpRec_type S VecSxp
        (SExpRec_VectorPointer (make_Vector_SExpRec header
          (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array)))
  | SExpType_corresponds_to_data_ExprSxp : forall header array,
      (forall a,
        Mem a (ArrayList.to_list array) ->
        may_have_types S all_storable_SExpTypes a) ->
      safe_SExpRec_type S ExprSxp
        (SExpRec_VectorPointer (make_Vector_SExpRec header
          (make_VecSxp_struct (ArrayList.length array) (ArrayList.length array) array)))
  (** The following four types have not been implemented. **)
  | SExpType_corresponds_to_data_BcodeSxp : forall e_,
      safe_SExpRec_type S BcodeSxp e_
  | SExpType_corresponds_to_data_ExtptrSxp : forall e_,
      safe_SExpRec_type S ExtptrSxp e_
  | SExpType_corresponds_to_data_RawSxp : forall e_,
      (** We don’t know much about [RawSxp], but we know that it must be a vector. **)
      (forall e_NonVector, e_ <> SExpRec_NonVector e_NonVector) ->
      safe_SExpRec_type S RawSxp e_
  | SExpType_corresponds_to_data_S4Sxp : forall e_,
      safe_SExpRec_type S S4Sxp e_
  (** The two types [NewSxp] and [FreeSxp] are only used in the
    garbage collector, which has not been formalised.  They thus never
    appear in our memory, and no constructor is associated to
    these types. **)
  (** The type [FunSxp] is not possible as the type of a C object,
    as it would need more bytes than actually present.  It is
    rewriten in practise into CloSxp if someone tries to put it into
    an object. Again, no constructor is associated to this type. **)
  .

(** Header are considered safe if their [attrib] field is safe.
  It must also be a finite list. **)
Record safe_header_gen (safe_pointer : state -> _ -> Prop) S (h : SExpRecHeader) : Prop := make_safe_header {
    safe_attrib : safe_pointer S (attrib h) ;
    attrib_list : list_type S ([ListSxp]) all_storable_SExpTypes ([CharSxp]) (attrib h)
  }.

(** An object is considered safe if its fields are of the expected type. **)
Record safe_SExpRec_gen (safe_pointer : state -> _ -> Prop) S (e_ : SExpRec) : Prop := make_safe_SExpRec {
    SExpType_corresponds_to_datatype : safe_SExpRec_type S (type e_) e_ ;
    SExpRec_header : safe_header_gen safe_pointer S e_
  }.

(** We can now define [safe_pointer], which stands for several properties:
  subpointers should be valid, and subobjects should be safe.
  This property is circular: for instance, the [NilSxp] object points to
  itself through its “cdr”.  We could have used Coq’s coinduction, but we
  choose to use Paco’s instead.
  Note that the [move_along_path_step] applies for any subpointers,
  including the one stored in the attribute, or the elements of arrays. **)

Record safe_pointer_gen (safe_pointer : _ -> _ -> Prop) S p : Prop := make_safe_pointer {
    pointer_bound : bound S p ;
    no_null_pointer_along_path_step : forall s p',
      ~ null_pointer_exceptions_suffix s ->
      move_along_path_step s S p = Some p' ->
      p' <> NULL ;
    safe_pointer_along_path_step : forall s e,
      move_along_path_step s S p = Some e ->
      e <> NULL ->
      safe_pointer S e ;
    safe_SExpRec_read : forall p_,
      read_SExp S p = Some p_ ->
      safe_SExpRec_gen safe_pointer S p_
  }.
Definition safe_pointer S p := paco2 safe_pointer_gen bot2 S p.
Hint Unfold safe_pointer.

Lemma safe_pointer_gen_mon : monotone2 safe_pointer_gen.
Proof.
  pmonauto. (* This is very frustating: I have found no documentation on when this tactic may fail… *)
  repeat intro. destruct IN as [B OKf OKs R]. constructors*.
  introv E. forwards (T&OKh): R E. constructors*. inverts OKh. constructors*.
Qed.
Hint Resolve safe_pointer_gen_mon : paco.

Lemma safe_pointer_rewrite : safe_pointer = safe_pointer_gen safe_pointer.
Proof.
  extens. intros S p. iff I.
  - punfold I. applys_eq I 3. extens. clear. intros S p. iff I.
    + left~.
    + inverts I as I; [ autos* | inverts I ].
  - pfold. applys_eq I 3. extens. clear. intros S p. iff I.
    + inverts I as I; [ autos* | inverts I ].
    + left~.
Qed.

Lemma safe_pointer_rewrite_paco2 : paco2 safe_pointer_gen bot2 = safe_pointer.
Proof. reflexivity. Qed.

Lemma safe_pointer_rewrite_upaco2 : upaco2 safe_pointer_gen bot2 = safe_pointer.
Proof. extens. intros S p. iff~ I. inverts I as I; autos~. inverts I. Qed.

Definition safe_SExpRec := safe_SExpRec_gen safe_pointer.
Definition safe_header := safe_header_gen safe_pointer.

Definition list_type_safe S := list_type_such_that (safe_header S) (safe_pointer S) (safe_pointer S) S.
Definition list_head_safe S := list_head_such_that (safe_header S) (safe_pointer S) (safe_pointer S) S.

(** A state is safe if all the pointers reachable from any entry point are safe.
  We also require that only one object of type [NilSxp] can be declared. **)
Record safe_state S : Prop := make_safe_state {
    no_null_pointer_entry_point : forall e p,
      ~ null_pointer_exceptions_entry_point e ->
      move_along_entry_point e S = Some p ->
      p <> NULL ;
    safe_entry_points : forall e p,
      move_along_entry_point e S = Some p ->
      p <> NULL ->
      safe_pointer S p ;
    only_one_nil : forall p1 p2,
      may_have_types S ([NilSxp]) p1 ->
      may_have_types S ([NilSxp]) p2 ->
      p1 = p2 ;
    safe_SymbolTable :
      list_type_safe S ([ListSxp]) ([SymSxp]) ([NilSxp]) (R_SymbolTable S)
  }.

(** Global variables must be safe.
  We also state the expected type of some pointers (and in particular [R_NilValue]). **)
Record safe_globals S globals : Prop := make_safe_globals {
    globals_not_NULL : forall g,
      ~ null_pointer_exceptions_globals g ->
      read_globals globals g <> NULL ;
    globals_not_NULL_safe : forall g,
      read_globals globals g <> NULL ->
      safe_pointer S (read_globals globals g) ;
    R_NilValue_may_have_types : may_have_types S ([NilSxp]) (read_globals globals R_NilValue)
  }.


(** ** Transitions between states **)

(** It is frequent that two states are nearly identical, differing only
  in values not reachable from entry points.
  This for instance occur after memory allocations.
  We can also use this predicate to garbage collect a heap.
  The tactic [transition_conserve] uses such a statement to update as much
  properties as can be from the old state to the new one. **)
Record conserve_old_bindings S S' : Prop := make_conserve_old_bindings {
    conserve_old_bindings_bindings : forall p,
      bound S p ->
      bound_such_that S (fun e_ =>
        bound_such_that S' (fun e'_ => e_ = e'_) p) p ;
    conserve_old_bindings_entry_point : forall e,
      move_along_entry_point e S = move_along_entry_point e S'
  }.

