(** Result.
  This file describes the [result] monad. **)

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
From CoqR Require Import Rinternals State InternalTypes Globals.
From ExtLib Require Structures.Monad.
From ITree Require Export ITree.
From ITree Require Import TranslateFacts.

Import ITree.Eq.Eqit.

Export Structures.Monad.
Export Monads.
Export MonadNotation.

Open Scope type_scope.


(** * Lemmas **)

(** A lemma to easily convert the events of [itree]s. **)
Instance Embeddable_itree_event : forall E F R,
  E -< F ->
  Embeddable (itree E R) (itree F R).
Proof. introv S T. refine (translate S T). Defined.

(** A lemma to unfold [embed]. **)
Lemma embed_unfold : forall A B (H : Embeddable A B),
  embed = H.
Proof. reflexivity. Qed.


(** * Event types **)

(** This development is based on [itree]s.
  In this framework, we have to define a set of events needed to define our semantics. **)

Universe r. (** We force each event kind to return in the same universe. **)

(** ** Globals **)

(** Events to manipulate global variables. **)

(** As most functions of the formalism only read global variables,
  and that knowing that global variables are generally constant is
  an important property to have, we separate the reading and writing
  events.
  Thus, only functions actually modifying global variables (typically
  the ones in [Rinit]) will carry the writing events, and it will be
  possible to formally prove that as soon as only reading events are
  used, global variables don’t change values. **)

Inductive RGlobal : Type -> Type@{r} :=
  | rglobal : GlobalVariable -> RGlobal SEXP
  | type2Table : SExpType -> RGlobal Type2Table_type
  .

Inductive WGlobal : Type -> Type@{r} :=
  | wglobal : GlobalVariable -> SEXP -> WGlobal SEXP
  | wtype2Table : ArrayList.array Type2Table_type -> WGlobal Type2Table_type
  .

(** ** Heap **)

(** Events for the state: allocation, reading, and writing. **)

Inductive EHeap : Type -> Type@{r} := (* TODO: Should probably be split *)
  | alloc_sexp : SExpRec -> EHeap unit
  | read_sexp : SEXP -> EHeap SExpRec
  | write_sexp : SEXP -> SExpRec -> EHeap unit
  .

(** ** Inputs and outputs **)

Inductive EIO : Type -> Type@{r} :=
  | run_stdout_print : Rconnection -> string -> EIO (option Rconnection)
  | run_stderr_print : Rconnection -> string -> EIO (option Rconnection)
  | run_stdout_flush : Rconnection -> EIO (option Rconnection)
  | run_stderr_flush : Rconnection -> EIO (option Rconnection)
  .

(** ** [FUNTAB] **)

(** The [FUNTAB] structure is used to store primitive and internal
  functions, as well as some constructs to evaluate it. Most of these
  constructs can be found in include/Defn.h. **)

(** Following GNU R, all such functions have the same type: they take
  four SEXP and return an SEXP.  The four SEXP respectively correspond
  to the [call], [op], [args], and [rho] parameters of each functions.
  The most important is [args], which is an R list of arguments. **)

Inductive Funtab : Type -> Type@{r} :=
  | call_funtab :
    SEXP -> (** call **)
    SEXP -> (** op **)
    SEXP -> (** args **)
    SEXP -> (** rho **)
    Funtab SEXP
  .

(** ** Control-flow **)

(** We distinguish between erroneous events and jumping events. **)

(** Erroneous events break the control-flow, halting the execution. **)

(** The program yielded an error described by the provided message.
  This error is not guaranteed not to happen. **)
Inductive Error : Type -> Type@{r} :=
  | error [T] : string -> Error T
  .

(** Similar to [error], but this error is not meant to happen.
  If such an error happens, it is either a bug in the CoqR interpreter, or an undefined
  behaviour of the (source code of the) reference interpreter GNU R. **)
Inductive Impossible : Type -> Type@{r} :=
  | impossible [T] : string -> Impossible T
  .

(** The difference between [error] and [impossible] is that [error] is
  thrown when the R interpreter throws an error (usally using the
  [error] C function), and [impossible] is thrown when R does not
  throw an error, but we know for sure that such a case can never
  happen, or such a case would lead an undefined behaviour in the
  original program. Typically because the C program accepts an
  impossible case to be missing, but that Coq does not recognise this
  case to be impossible. So if there is a possible case in which Coq
  must return something, but that the R interpreter in C does not
  cover this case (for instance if C features an expression [e->type]
  without checking whether [e] actually maps to a valid object), the
  Coq interpreter will return [impossible]. **)

Inductive LongJump : Type -> Type@{r} :=
  | longjump [T] : nat -> context_type -> LongJump T
  (** the program yielded a call to [LONGJMP] with the provided arguments. **)
  .

(** ** Development **)

(** Features for developping purposes. **)

(** The result relies on a feature not yet implemented. **)
Inductive NotImplemented : Type -> Type@{r} :=
  | not_implemented [T] : string -> NotImplemented T
  .

(** A precision about [not_implemented] and [error]: if the C source
  code of R throw a not-implemented error, we consider this as an
  error thrown in the original interpreter and use the constructor
  [error].  We only throw [not_implemented] when our Coq code has not
  implemented a behaviour of R.  The construct [error] thus models the
  errors thrown by the R program. **)

Inductive Debug : Type -> Type@{r} :=
  | add_stack : string -> Debug unit
  (** When entering a function, we mark it using this event.
    This can then help to trace function definitions when debugging. **)
  | debug_log : string -> Debug unit
  (** A debug log, only meant for development purposes. **)
  .


(** * Event Descriptors **)

Module EventDescriptor.

(** Given the events defined in the previous section, one could imagine
  joining all these events in a single type [RGlobal +' WGlobal +' …].
  This would however provide very few information about what each function
  actually do.  Instead, we would like to have some kind of minimal set of
  events associated to each function.  For instance, most function never
  update the value of any global variable: the event [WGlobal] should
  preferably not be present in the type of such functions.  Not having such
  an event in the signature of a function ensures by type that this
  function will never modify a global variable, thus helping proving
  properties for this function.

  Inferring this minimal set is not trivial in general without having to add
  a lot of annotations or using some kind of meta-programming (typically, Ltac).
  For instance, Coq doesn’t provide a mechanism to infer that an expression of
  the form [if _ then a else b] should have some kind of union type between the
  type of [a] and the type of [b] (and for good reasons: such common larger
  type may not exist or may not be unique).  We are however here in the presence
  of a lattice of types, and this can be wroked with by explicitely defining
  this lattice. **)

(** Event descriptor state for each kind of events whether it can be triggerred
  by the associated function. **)
Record event_descriptor := make_event_descriptor {
    dRGlobal : bool ;
    dWGlobal : bool ;
    dEHeap : bool ;
    dEIO : bool ;
    dFuntab : bool ;
    dError : bool ;
    dImpossible : bool ;
    dLongJump : bool ;
    dNotImplemented : bool ;
    dDebug : bool ;
  }.

(** The correspondences between the fields of [event_descriptor] and events,
  mainly for automation purposes. **)
Definition event_descriptor_correspondence := [
    (dRGlobal, RGlobal) ;
    (dWGlobal, WGlobal) ;
    (dEHeap, EHeap) ;
    (dEIO, EIO) ;
    (dFuntab, Funtab) ;
    (dError, Error) ;
    (dImpossible, Impossible) ;
    (dLongJump, LongJump) ;
    (dNotImplemented, NotImplemented) ;
    (dDebug, Debug)
  ].

(** Adding the definitions expected by [OrderedType]. **)
Definition t := event_descriptor.

Definition eq (d1 d2 : t) :=
  Forall (fun '(dE, _) => dE d1 = dE d2) event_descriptor_correspondence.

Global Instance Decidable_eq : forall d1 d2, Decidable (eq d1 d2).
Proof.
  intros d1 d2. unfolds eq.
  (* This is frustrating: I can’t apply [Forall_Decidable] because of universe constraints here. *)
  induction event_descriptor_correspondence as [|[dE ?] l].
  - applys decidable_make true. rew_bool_eq. apply~ Forall_nil.
  - applys Decidable_equiv (dE d1 = dE d2 /\ Forall (fun '(dE, _) => dE d1 = dE d2) l).
    + iff F; inverts~ F. constructors~.
    + typeclass.
Defined.

Lemma eq_eq : forall d1 d2, eq d1 d2 <-> d1 = d2.
Proof.
  intros d1 d2. destruct d1, d2. unfolds eq, event_descriptor_correspondence. iff F.
  - repeat (let E := fresh "E" in inverts F as E F; simpl in E).
    fequals~.
  - inverts F. repeat constructors~.
Qed.

Global Instance Comparable_t : Comparable t.
Proof.
  constructors. intros d1 d2. applys Decidable_equiv.
  - apply eq_eq.
  - typeclass.
Defined.

Lemma eq_refl : forall d, eq d d.
Proof. intro d. apply~ eq_eq. Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. intros d1 d2 E. apply eq_eq in E. apply~ eq_eq. Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. intros d1 d2 d3 E1 E2. apply eq_eq in E1, E2. apply eq_eq. substs~. Qed.

Definition le (d1 d2 : t) :=
  Forall (fun '(dE, _) => decide ((dE d1 : bool) -> dE d2)) event_descriptor_correspondence.

Global Instance Decidable_le : forall d1 d2, Decidable (le d1 d2).
Proof.
  intros d1 d2. unfolds le.
  (* This is frustrating: I can’t apply [Forall_Decidable] because of universe constraints here. *)
  induction event_descriptor_correspondence as [|[dE ?] l].
  - applys decidable_make true. rew_bool_eq. apply~ Forall_nil.
  - applys Decidable_equiv ((dE d1 -> dE d2) /\ Forall (fun '(dE, _) => decide ((dE d1 : bool) -> dE d2)) l).
    + iff F; inverts F as I F.
      * constructors~. rewrite decide_spec. rew_bool_eq~.
      * rewrite decide_spec in I. rew_bool_eq~ in I.
    + typeclass.
Defined.

Definition lt (d1 d2 : t) :=
  le d1 d2 /\ d1 <> d2.

Global Instance Decidable_lt : forall d1 d2, Decidable (lt d1 d2).
Proof. typeclass. Defined.

Lemma le_trans : forall d1 d2 d3 : t, le d1 d2 -> le d2 d3 -> le d1 d3.
Proof.
  intros d1 d2 d3 F1 F2. destruct d1, d2, d3. unfolds eq, event_descriptor_correspondence.
  repeat (let E := fresh "E" in inverts F1 as E F1; simpl in E; rewrite decide_spec in E; rew_bool_eq in E).
  repeat (let E := fresh "E" in inverts F2 as E F2; simpl in E; rewrite decide_spec in E; rew_bool_eq in E).
  repeat constructors; simpl; rewrite decide_spec; rew_bool_eq~.
Qed.

Lemma le_antisym : forall d1 d2 : t, le d1 d2 -> le d2 d1 -> d1 = d2.
Proof.
  intros d1 d2 F1 F2. destruct d1, d2. unfolds eq, event_descriptor_correspondence.
  repeat (let E := fresh "E" in inverts F1 as E F1; simpl in E; rewrite decide_spec in E; rew_bool_eq in E).
  repeat (let E := fresh "E" in inverts F2 as E F2; simpl in E; rewrite decide_spec in E; rew_bool_eq in E).
  fequals; extens; splits~.
Qed.

Lemma lt_trans : forall d1 d2 d3 : t, lt d1 d2 -> lt d2 d3 -> lt d1 d3.
Proof.
  introv (L1&D1) (L2&D2). splits~.
  - applys le_trans L1 L2.
  - intro_subst. forwards: le_antisym L1 L2. substs~.
Qed.

Lemma lt_not_eq : forall d1 d2 : t, lt d1 d2 -> ~ eq d1 d2.
Proof. introv (L&D) E. apply eq_eq in E. substs~. Qed.

(** [event d] is the event type corresponding to the event descriptor [d]. **)
Definition event (d : t) : Type -> Type@{r} :=
  fold_left (fun '(dE, E) T => if (dE d : bool) then (E : Type -> Type@{r}) +' T else T) void1
    event_descriptor_correspondence.

(** Mapping each component of two event descriptors. **)
Definition map2 (f : bool -> bool -> bool) (d1 d2 : event_descriptor) : event_descriptor.
Proof.
  let rec g acc l :=
    lazymatch l with
    | [] => exact acc
    | (?dE, _) :: ?l => g (acc (f (dE d1) (dE d2))) l
    end in
  let l := eval compute in event_descriptor_correspondence in
  g make_event_descriptor l.
Defined.

Lemma map2_assoc : forall f,
  LibOperation.assoc f ->
  LibOperation.assoc (map2 f).
Proof. intros f Af d1 d2 d3. destruct d1, d2, d3; compute; fequals. Qed.

Lemma map2_comm : forall f,
  LibOperation.comm f ->
  LibOperation.comm (map2 f).
Proof. intros f Af d1 d2. destruct d1, d2; compute; fequals. Qed.

Lemma map2_same : forall f,
  LibOperation.idempotent2 f ->
  LibOperation.idempotent2 (map2 f).
Proof. intros f Af d. destruct d; compute; fequals. Qed.

(** The [join] and [meet] operations of the lattice. **)

Definition join : t -> t -> t :=
  map2 (fun b1 b2 => b1 || b2).

Definition meet : t -> t -> t :=
  map2 (fun b1 b2 => b1 && b2).

Lemma join_assoc : LibOperation.assoc join.
Proof. apply map2_assoc. apply or_assoc. Qed.

Lemma join_comm : LibOperation.comm join.
Proof. apply map2_comm. apply or_comm. Qed.

Lemma join_same : LibOperation.idempotent2 join.
Proof. apply map2_same. apply or_same. Qed.

Lemma le_join : forall d1 d2,
  le d1 d2 ->
  join d1 d2 = d2.
Proof.
  introv F. destruct d1, d2.
  repeat (let E := fresh "E" in inverts F as E F; simpl in E; rewrite decide_spec in E; rew_bool_eq in E).
  unfolds join, map2; fequals;
    lazymatch goal with |- ?b1 || ?b2 = _ => destruct b1, b2; (reflexivity || false*) end.
Qed.

Lemma join_le_l : forall d1 d2,
  le d1 (join d1 d2).
Proof.
  intros d1 d2. destruct d1, d2. unfolds le, event_descriptor_correspondence.
  repeat constructors; rewrite decide_spec; rew_bool_eq; simpl; rew_istrue; left~.
Qed.

Lemma join_le_r : forall d1 d2,
  le d2 (join d1 d2).
Proof.
  intros d1 d2. destruct d1, d2. unfolds le, event_descriptor_correspondence.
  repeat constructors; rewrite decide_spec; rew_bool_eq; simpl; rew_istrue; right~.
Qed.

Lemma meet_assoc : LibOperation.assoc meet.
Proof. apply map2_assoc. apply and_assoc. Qed.

Lemma meet_comm : LibOperation.comm meet.
Proof. apply map2_comm. apply and_comm. Qed.

Lemma meet_same : LibOperation.idempotent2 meet.
Proof. apply map2_same. apply and_same. Qed.

Lemma le_meet : forall d1 d2,
  le d1 d2 ->
  meet d1 d2 = d1.
Proof.
  introv F. destruct d1, d2.
  repeat (let E := fresh "E" in inverts F as E F; simpl in E; rewrite decide_spec in E; rew_bool_eq in E).
  unfolds meet, map2; fequals;
    lazymatch goal with |- ?b1 && ?b2 = _ => destruct b1, b2; (reflexivity || false*) end.
Qed.

Lemma meet_le_l : forall d1 d2,
  le (meet d1 d2) d1.
Proof.
  intros d1 d2. destruct d1, d2. unfolds le, event_descriptor_correspondence.
  repeat constructors; rewrite decide_spec; rew_bool_eq; simpl; rew_istrue; intros (?&?); autos~.
Qed.

Lemma meet_le_r : forall d1 d2,
  le (meet d1 d2) d2.
Proof.
  intros d1 d2. destruct d1, d2. unfolds le, event_descriptor_correspondence.
  repeat constructors; rewrite decide_spec; rew_bool_eq; simpl; rew_istrue; intros (?&?); autos~.
Qed.

(** The bottom of the lattice. **)
Definition empty : event_descriptor :=
  ltac:(constructor; exact false).

Definition bottom : t := empty.

Lemma bottom_is_bottom : forall d, le bottom d.
Proof.
  intro d. destruct d.
  repeat constructor; simpl; rewrite decide_spec; rew_bool_eq*.
Qed.

Lemma join_bottom_r : LibOperation.neutral_r join bottom.
Proof. intro d. destruct d. unfolds join, map2, bottom, empty; fequals; apply or_false_r. Qed.

Lemma join_bottom_l : LibOperation.neutral_l join bottom.
Proof. intro d. destruct d. unfolds join, map2, bottom, empty; fequals; apply or_false_l. Qed.

Lemma meet_bottom_r : LibOperation.absorb_r meet bottom.
Proof. intro d. destruct d. unfolds meet, map2, bottom, empty; fequals; try apply and_false_r. Qed.

Lemma meet_bottom_l : LibOperation.absorb_l meet bottom.
Proof. intro d. destruct d. unfolds meet, map2, bottom, empty; fequals; apply and_false_l. Qed.

(** The top of the lattice. **)
Definition full : event_descriptor :=
  ltac:(constructor; exact true).

Definition top : t := full.

Lemma top_is_top : forall d, le d top.
Proof.
  intro d. destruct d.
  repeat constructor; simpl; rewrite decide_spec; rew_bool_eq~.
Qed.

Lemma join_top_r : LibOperation.absorb_r join top.
Proof. intro d. destruct d. unfolds join, map2, top, full; fequals; apply or_true_r. Qed.

Lemma join_top_l : LibOperation.absorb_l join top.
Proof. intro d. destruct d. unfolds join, map2, top, full; fequals; apply or_true_l. Qed.

Lemma meet_top_r : LibOperation.neutral_r meet top.
Proof. intro d. destruct d. unfolds meet, map2, top, full; fequals; apply and_true_r. Qed.

Lemma meet_top_l : LibOperation.neutral_l meet top.
Proof. intro d. destruct d. unfolds meet, map2, top, full; fequals; apply and_true_l. Qed.

(** Basic projections with only one event. **)

Definition only_dRGlobal : event_descriptor :=
  ltac:(refine {| dRGlobal := true |}; exact false).

Global Instance event_only_dRGlobal : RGlobal -< event only_dRGlobal.
Proof.
  unfolds event, event_descriptor_correspondence, only_dRGlobal.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dWGlobal : event_descriptor :=
  ltac:(refine {| dWGlobal := true |}; exact false).

Global Instance event_only_dWGlobal : WGlobal -< event only_dWGlobal.
Proof.
  unfolds event, event_descriptor_correspondence, only_dWGlobal.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dEHeap : event_descriptor :=
  ltac:(refine {| dEHeap := true |}; exact false).

Global Instance event_only_dEHeap : EHeap -< event only_dEHeap.
Proof.
  unfolds event, event_descriptor_correspondence, only_dEHeap.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dEIO : event_descriptor :=
  ltac:(refine {| dEIO := true |}; exact false).

Global Instance event_only_dEIO : EIO -< event only_dEIO.
Proof.
  unfolds event, event_descriptor_correspondence, only_dEIO.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dFuntab : event_descriptor :=
  ltac:(refine {| dFuntab := true |}; exact false).

Global Instance event_only_dFuntab : Funtab -< event only_dFuntab.
Proof.
  unfolds event, event_descriptor_correspondence, only_dFuntab.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dError : event_descriptor :=
  ltac:(refine {| dError := true |}; exact false).

Global Instance event_only_dError : Error -< event only_dError.
Proof.
  unfolds event, event_descriptor_correspondence, only_dError.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dImpossible : event_descriptor :=
  ltac:(refine {| dImpossible := true |}; exact false).

Global Instance event_only_dImpossible : Impossible -< event only_dImpossible.
Proof.
  unfolds event, event_descriptor_correspondence, only_dImpossible.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dLongJump : event_descriptor :=
  ltac:(refine {| dLongJump := true |}; exact false).

Global Instance event_only_dLongJump : LongJump -< event only_dLongJump.
Proof.
  unfolds event, event_descriptor_correspondence, only_dLongJump.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dNotImplemented : event_descriptor :=
  ltac:(refine {| dNotImplemented := true |}; exact false).

Global Instance event_only_dNotImplemented : NotImplemented -< event only_dNotImplemented.
Proof.
  unfolds event, event_descriptor_correspondence, only_dNotImplemented.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.

Definition only_dDebug : event_descriptor :=
  ltac:(refine {| dDebug := true |}; exact false).

Global Instance event_only_dDebug : Debug -< event only_dDebug.
Proof.
  unfolds event, event_descriptor_correspondence, only_dDebug.
  repeat rewrite fold_left_cons. rewrite fold_left_nil. simpl. typeclass.
Defined.


(** The order [le] is directly linked with subtyping. **)
Global Instance event_le : forall d1 d2,
  le d1 d2 ->
  event d1 -< event d2.
Proof.
  introv L. unfolds event, le.
  asserts G: ((void1 : Type -> Type@{r}) -< (void1 : Type -> Type@{r})); [ typeclass |]. gen G.
  generalize (void1 : Type -> Type@{r}) at 1 3. generalize (void1 : Type -> Type@{r}).
  gen L. induction event_descriptor_correspondence as [|(dE&?) l]; introv F I.
  - typeclass.
  - repeat rewrite fold_left_cons. apply IHl.
    + inverts~ F.
    + asserts Id: (dE d1 -> dE d2).
      { inverts F as E ?. rewrite decide_spec in E. rew_bool_eq~ in E. }
      repeat cases_if; (typeclass || false~).
Defined.

End EventDescriptor.


(** How we assume events are organised. **)

Module Type FullEventLattice.

(** The main type of event descriptor. **)
Parameter t : Type.
Parameter event : t -> Type -> Type.

(** It is ordered. **)
Parameter eq : t -> t -> Prop.
Parameter eq_refl : forall d : t, eq d d.
Parameter eq_sym : forall x y : t, eq x y -> eq y x.
Parameter le : t -> t -> Prop.
Parameter lt : t -> t -> Prop.
Parameter le_trans : forall d1 d2 d3 : t, le d1 d2 -> le d2 d3 -> le d1 d3.
Parameter le_antisym : forall d1 d2 : t, le d1 d2 -> le d2 d1 -> d1 = d2.
Parameter lt_trans : forall d1 d2 d3 : t, lt d1 d2 -> lt d2 d3 -> lt d1 d3.
Parameter lt_not_eq : forall d1 d2 : t, lt d1 d2 -> ~ eq d1 d2.

(** The order is compatible with the event embedding. **)
Parameter event_le : forall d1 d2 : t, le d1 d2 -> event d1 -< event d2.

(** It is structured as a lattice. **)
Parameter join : t -> t -> t.
Parameter join_assoc : LibOperation.assoc join.
Parameter join_comm : LibOperation.comm join.
Parameter join_same : LibOperation.idempotent2 join.
Parameter le_join : forall d1 d2 : t, le d1 d2 -> join d1 d2 = d2.
Parameter join_le_l : forall d1 d2 : t, le d1 (join d1 d2).
Parameter join_le_r : forall d1 d2 : t, le d2 (join d1 d2).

Parameter meet : t -> t -> t.
Parameter meet_assoc : LibOperation.assoc meet.
Parameter meet_comm : LibOperation.comm meet.
Parameter meet_same : LibOperation.idempotent2 meet.
Parameter le_meet : forall d1 d2 : t, le d1 d2 -> meet d1 d2 = d1.
Parameter meet_le_l : forall d1 d2 : t, le (meet d1 d2) d1.
Parameter meet_le_r : forall d1 d2 : t, le (meet d1 d2) d2.

Parameter bottom : t.
Parameter bottom_is_bottom : forall d : t, le bottom d.
Parameter join_bottom_r : LibOperation.neutral_r join bottom.
Parameter join_bottom_l : LibOperation.neutral_l join bottom.
Parameter meet_bottom_r : LibOperation.absorb_r meet bottom.
Parameter meet_bottom_l : LibOperation.absorb_l meet bottom.

Parameter top : t.
Parameter top_is_top : forall d : t, le d top.
Parameter join_top_r : LibOperation.absorb_r join top.
Parameter join_top_l : LibOperation.absorb_l join top.
Parameter meet_top_r : LibOperation.neutral_r meet top.
Parameter meet_top_l : LibOperation.neutral_l meet top.

End FullEventLattice.


(** A subtype of [FullEventLattice] which is what is actually being used. **)
(* FIXME: Remove what can be removed. *)

Module Type EventLattice.

(** The main type of event descriptor. **)
Parameter t : Type.
Parameter event : t -> Type -> Type.

(** It is ordered. **)
Parameter eq : t -> t -> Prop.
Parameter eq_refl : forall d : t, eq d d.
Parameter eq_sym : forall x y : t, eq x y -> eq y x.
Parameter le : t -> t -> Prop.
Parameter lt : t -> t -> Prop.
Parameter le_trans : forall d1 d2 d3 : t, le d1 d2 -> le d2 d3 -> le d1 d3.
Parameter le_antisym : forall d1 d2 : t, le d1 d2 -> le d2 d1 -> d1 = d2.
Parameter lt_trans : forall d1 d2 d3 : t, lt d1 d2 -> lt d2 d3 -> lt d1 d3.
Parameter lt_not_eq : forall d1 d2 : t, lt d1 d2 -> ~ eq d1 d2.

(** The order is compatible with the event embedding. **)
Parameter event_le : forall d1 d2 : t, le d1 d2 -> event d1 -< event d2.

(** It is structured as a lattice. **)
Parameter join : t -> t -> t.
Parameter join_assoc : LibOperation.assoc join.
Parameter join_comm : LibOperation.comm join.
Parameter join_same : LibOperation.idempotent2 join.
Parameter le_join : forall d1 d2 : t, le d1 d2 -> join d1 d2 = d2.
Parameter join_le_l : forall d1 d2 : t, le d1 (join d1 d2).
Parameter join_le_r : forall d1 d2 : t, le d2 (join d1 d2).

Parameter meet : t -> t -> t.
Parameter meet_assoc : LibOperation.assoc meet.
Parameter meet_comm : LibOperation.comm meet.
Parameter meet_same : LibOperation.idempotent2 meet.
Parameter le_meet : forall d1 d2 : t, le d1 d2 -> meet d1 d2 = d1.
Parameter meet_le_l : forall d1 d2 : t, le (meet d1 d2) d1.
Parameter meet_le_r : forall d1 d2 : t, le (meet d1 d2) d2.

Parameter bottom : t.
Parameter bottom_is_bottom : forall d : t, le bottom d.
Parameter join_bottom_r : LibOperation.neutral_r join bottom.
Parameter join_bottom_l : LibOperation.neutral_l join bottom.
Parameter meet_bottom_r : LibOperation.absorb_r meet bottom.
Parameter meet_bottom_l : LibOperation.absorb_l meet bottom.

Parameter top : t.
Parameter top_is_top : forall d : t, le d top.
Parameter join_top_r : LibOperation.absorb_r join top.
Parameter join_top_l : LibOperation.absorb_l join top.
Parameter meet_top_r : LibOperation.neutral_r meet top.
Parameter meet_top_l : LibOperation.neutral_l meet top.

End EventLattice.

Module MonadFromEventLattice (E : EventLattice).

Include E.
Local Instance event_le' : forall d1 d2 : t, le d1 d2 -> event d1 -< event d2 := event_le.

(** Monadic structure **)

Definition ret R (r : R) : itree (event bottom) R :=
  Ret r.

Definition bind [d1 d2 T U] (x : itree (event d1) T) (k : T -> itree (event d2) U) :
  itree (event (join d1 d2)) U :=
  let L1 := join_le_l d1 d2 in
  let L2 := join_le_r d1 d2 in
  ITree.bind
    (@embed (itree (event d1) T) (itree (event (join d1 d2)) T) ltac:(typeclass) x)
    (fun t => @embed (itree (event d2) U) (itree (event (join d1 d2)) U) ltac:(typeclass) (k t)).

Definition if_then_else [d1 d2 d3 R] (b : itree (event d1) bool)
  (t : itree (event d2) R) (e : itree (event d3) R) : itree (event (join d1 (join d2 d3))) R :=
  bind b (fun b =>
    let L2 := join_le_l d2 d3 in
    let L3 := join_le_r d2 d3 in
    if b
    then (@embed (itree (event d2) R) (itree (event (join d2 d3)) R) ltac:(typeclass) t)
    else (@embed (itree (event d3) R) (itree (event (join d2 d3)) R) ltac:(typeclass) e)).

Definition lift [A B d] (f : A -> B) (a : itree (event d) A) : itree (event d) B.
Proof.
  lets r: (bind a (fun a => ret (f a))).
  rewrite join_bottom_r in r. exact r.
Defined.

Definition lift2 [A B C d1 d2] (f : A -> B -> C) (a : itree (event d1) A) (b : itree (event d2) B)
  : itree (event (join d1 d2)) C :=
  bind a (fun a => lift (f a) b).

Definition or [d1 d2] (a : itree (event d1) bool) (b : itree (event d2) bool) :=
  lift2 or a b.
Definition and [d1 d2] (a : itree (event d1) bool) (b : itree (event d2) bool) :=
  lift2 and a b.

(* Helper lemma for [easy_convert]. *)
Lemma assoc_inv : forall A (f : A -> A -> A),
  LibOperation.assoc f ->
  forall x y z, f (f x y) z = f x (f y z).
Proof. introv assoc. introv. rewrite~ assoc. Qed.

(** Given [t : itree (event _) _], tries to simplify the goal using [E]’s equations
  to seemlessly [t]. **)
Ltac easy_convert t :=
  let rec foreach l tac :=
    lazymatch l with
    | nil => idtac
    | boxer ?v :: ?l => tac v; foreach l tac
    end in
  let lemmas := constr:(>> (assoc_inv join_assoc) join_same (assoc_inv meet_assoc) meet_same
                           join_bottom_r join_bottom_l meet_bottom_r meet_bottom_l
                           join_top_r join_top_l meet_top_r meet_top_l) in
  repeat progress foreach lemmas ltac:(fun lemma => try rewrite lemma) ;
  exact t.

Lemma bind_of_return : forall A B d (a : A) (f : A -> itree (event d) B),
  bind (ret a) f ≅ ltac:(easy_convert (f a)).
Proof.
  introv. unfolds bind, ret, @embed, Embeddable_itree_event.
  rewrite translate_ret, bind_ret_l.
  (* FIXME: I need to prove that
     using the fact that [bottom] is less than [d] to get [event bottom -< event d]
     using [event_le], then using [translate] on [itree]
     is the same than
     rewriting the type of the [itree] using [join_bottom_l]. *)
Admitted. (* TODO *)

Lemma return_of_bind : forall A d (aM : itree (event d) A),
  bind aM (@ret _) ≅ ltac:(easy_convert aM).
Proof.
  introv. unfolds bind, ret, @embed, Embeddable_itree_event.
  lazymatch goal with |- ITree.bind _ ?f ≅ _ => asserts E: (forall a : A, f a ≅ Ret a) end.
  { intro a. rewrite translate_ret. reflexivity. }
  (* FIXME: I need a lemma similar to [eutt_eq_bind] but for ≅ -> eq_itree_clo_bind *)
Admitted. (* TODO *)

Lemma bind_associativity : forall A B C d1 d2 d3
    (aM : itree (event d1) A) (f : A -> itree (event d2) B) (g : B -> itree (event d3) C),
  bind (bind aM f) g ≅ ltac:(easy_convert (bind aM (fun a => bind (f a) g))).
Proof.
  introv. unfolds bind, ret, @embed, Embeddable_itree_event.
  rewrite translate_bind, bind_bind, <- translate_cmpE.
  (* TODO: An interesting property to prove about [event_le] here:
     it is compatible with the transitivity of [le]. *)
Admitted. (* TODO *)

End MonadFromEventLattice.

(** Instantiation. **)

Module EventMonad := MonadFromEventLattice (EventDescriptor).

Definition Rglobal : GlobalVariable -> itree (EventMonad.event EventDescriptor.only_dRGlobal) SEXP :=
  fun x => trigger (rglobal x).

(* TODO
Infix "'&&" := mR_and (at level 40, left associativity).

(** The lift of [&&] to ['&&] is just a lift in the contextual monad. **)
Lemma mR_and_bool : forall a b : bool,
  a '&& b ≅ (a && b : mR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Infix "'||" := mR_or (at level 50, left associativity).

Lemma mR_or_bool : forall a b : bool,
  a '|| b ≅ (a || b : mR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Notation "'! b" := (mR_neg b) (at level 35, right associativity).

Lemma mR_neg_bool : forall b : bool,
  '! b ≅ (negb b : mR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition mR_decide P `{Decidable P} : mR_bool := decide P.
Arguments mR_decide P {_}.

Notation "''decide' P" := (mR_decide P) (at level 70, no associativity).

Definition mR_eq_SEXP : mR_SEXP -> mR_SEXP -> mR_bool := @mR_eq _ _.

Infix "'==" := mR_eq (at level 70, no associativity).

Notation "a '!= b" := ('! (a '== b)) (at level 70, no associativity).

Notation "'ifc' b 'then' v1 'else' v2" :=
  (x <- (b : mR_bool) ;; if x then v1 else v2)
  (at level 200, right associativity) : type_scope.
*)

(** * [FUNTAB] **)

(*
(** We have defined above the [Funtab] effect.  This effects calls a
  function with the following type. **)
Definition funtab_function :=
  SEXP -> (** call **)
  SEXP -> (** op **)
  SEXP -> (** args **)
  SEXP -> (** rho **)
  mRHFJE SEXP.

(** The [FUNTAB] is then an array of such functions, with some
  additional meta-data, like the function name: **)
Record funtab_cell := make_funtab_cell {
    fun_name : string ;
    fun_cfun : funtab_function ;
    fun_code : int ; (** The number stored here can be quite large. We thus use [int] instead of [nat]. **)
    fun_eval : funtab_eval_arg ;
    fun_arity : int ;
    fun_gram : PPinfo
  }.

Instance funtab_cell_Inhab : Inhab funtab_cell.
Proof. apply Inhab_of_val. constructors; apply arbitrary. Defined.

Definition funtab := ArrayList.array funtab_cell.
*)

