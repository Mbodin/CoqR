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
Set Universe Polymorphism.
From CoqR Require Import Rinternals State InternalTypes Globals.
From ExtLib Require Structures.Monad.
From ITree Require Export ITree.
From ITree Require Import TranslateFacts.

Import ITree.Eq.Eq.

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

(** This developpment is based on [itree]s.
  In this framework, we have to define a set of events needed to define our semantics. **)

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

Inductive RGlobal : Type -> Type :=
  | rglobal : GlobalVariable -> RGlobal SEXP
  | type2Table : SExpType -> RGlobal Type2Table_type
  .

Inductive WGlobal : Type -> Type :=
  | wglobal : GlobalVariable -> SEXP -> WGlobal SEXP
  | wtype2Table : ArrayList.array Type2Table_type -> WGlobal Type2Table_type
  .

(** ** Heap **)

(** Events for the state: allocation, reading, and writing. **)

Inductive EHeap : Type -> Type :=
  | alloc_sexp : SExpRec -> EHeap unit
  | read_sexp : SEXP -> EHeap SExpRec
  | write_sexp : SEXP -> SExpRec -> EHeap unit
  .

(** ** [FUNTAB] **)

(** The [FUNTAB] structure is used to store primitive and internal
  functions, as well as some constructs to evaluate it. Most of these
  constructs can be found in include/Defn.h. **)

(** Following GNU R, all such functions have the same type: they take
  four SEXP and return an SEXP.  The four SEXP respectively correspond
  to the [call], [op], [args], and [rho] parameters of each functions.
  The most important is [args], which is an R list of arguments. **)

Inductive Funtab : Type -> Type :=
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

Inductive Error : Type -> Type :=
  | error [T] : string -> Error T
  (** The program yielded an error described by the provided message.
    This error is not guaranteed not to happen. **)
  | impossible [T] : string -> Error T
  (** Similar to [error], but this error is not meant to happens.
    If such an error happens, it is either a bug in the CoqR interpreter, or an undefined
    behaviour of the (source code of the) reference interpreter GNU R. **)
  | not_implemented [T] : string -> Error T
  (** the result relies on a feature not yet implemented. **)
  .

(** A precision about [not_implemented] and [error]: if the C source
  code of R throw a not-implemented error, we consider this as an
  error thrown in the original interpreter and use the constructor
  [error].  We only throw [not_implemented] when our Coq code has not
  implemented a behaviour of R.  The construct [error] thus models the
  errors thrown by the R program. **)

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

Inductive LongJump : Type -> Type :=
  | longjump [T] : nat -> context_type -> LongJump T
  (** the program yielded a call to [LONGJMP] with the provided arguments. **)
  .


(** * Contextual Types **)

Unset Universe Polymorphism.

(* FIXME: This looks like a bug: adding the following line solves the universe inconsistency! *)
Section FixingPolymorphism.
Constraint itreeF.u1 < ArrayList.array.u.
End FixingPolymorphism.

(** This project is based on the [itree] type.  This type is useful
  to define all the program’s effects, but in some context doesn’t
  behave well with coercions.
  In order to use Coq’s coercion mechanism, we identify the following
  usage cases, each being in a separate use-case of R functions:
  - R ([RGlobal]): the minimum level, only able to read global variables.
  - RE ([RGlobal +' Error]): as above, but are also allowed to fail.
  - RH ([RGlobal +' EHeap]): the level of most R functions that can’t fail:
    they read global variables as well as manipulate the C heap.
  - RHE ([RGlobal +' EHeap +' Error]): as above, but are also allowed to
    fail.
  - RHFE ([RGlobal +' EHeap +' Funtab +' Error]): the level of most R
    functions: they read global variables, manipulate the C heap, can call
    functions in the [FUNTAB] array, and fail.
  - RHFJE ([RGlobal +' EHeap +' Funtab +' LongJump +' Error]): the level
    of some rare functions based on long jump, as well as the level of the
    functions in the [FUNTAB] array.
  - RWH ([RGlobal +' WGlobal +' EHeap]): the level of some internal
    functions in [Rinit].
  - RWHFJE ([RGlobal +' WGlobal +' EHeap +' Funtab +' LongJump +' Error]):
    the maximum level in which all events are allowed to live in.
  These levels are designed such that the information about what the function
  is allowed to do is embedded in its type: a function in the RE level can’t
  change the value of global variables, for instance.
  For each of these levels, we define a type (for instance, [cRE] for the RE
  level), as well as coercions to other levels to manipulate them seemlessly.
  Unfortunately, Coq coercions don’t manipulate [forall] quantifiers, and we
  have to limit ourselves to the two most common results: [bool] and [SEXP].
  The fact that we can split all R functions into these separate levels was
  not obvious from the organisation of GNU R, but shows some intuition on
  how it is structured. **)

Definition cR T := itree RGlobal T.
Definition cRE T := itree (RGlobal +' Error) T.
Definition cRH T := itree (RGlobal +' EHeap) T.
Definition cRHE T := itree (RGlobal +' EHeap +' Error) T.
Definition cRHFE T := itree (RGlobal +' EHeap +' Funtab +' Error) T.
Definition cRHFJE T := itree (RGlobal +' EHeap +' Funtab +' LongJump +' Error) T.
Definition cRWH T := itree (RGlobal +' WGlobal +' EHeap) T.
Definition cRWHFJE T := itree (RGlobal +' WGlobal +' EHeap +' Funtab +' LongJump +' Error) T.

Instance Monad_cR : Monad cR := Monad_itree.
Instance Monad_cRE : Monad cRE := Monad_itree.
Instance Monad_cRH : Monad cRH := Monad_itree.
Instance Monad_cRHE : Monad cRHE := Monad_itree.
Instance Monad_cRHFE : Monad cRHE := Monad_itree.
Instance Monad_cRHFJE : Monad cRHFJE := Monad_itree.
Instance Monad_cRWH : Monad cRWH := Monad_itree.
Instance Monad_cRWHFJE : Monad cRWHFJE := Monad_itree.

Definition cR_bool := cR bool.
Definition cRE_bool := cRE bool.
Definition cRH_bool := cRH bool.
Definition cRHE_bool := cRHE bool.
Definition cRHFE_bool := cRHFE bool.
Definition cRHFJE_bool := cRHFJE bool.
Definition cRWH_bool := cRWH bool.
Definition cRWHFJE_bool := cRWHFJE bool.

Definition cR_SEXP := cR SEXP.
Definition cRE_SEXP := cRE SEXP.
Definition cRH_SEXP := cRH SEXP.
Definition cRHE_SEXP := cRHE SEXP.
Definition cRHFE_SEXP := cRHFE SEXP.
Definition cRHFJE_SEXP := cRHFJE SEXP.
Definition cRWH_SEXP := cRWH SEXP.
Definition cRWHFJE_SEXP := cRWHFJE SEXP.

Definition cR_cRE : forall T, cR T -> cRE T := fun _ => embed.
Coercion cR_cRE_bool := @cR_cRE bool : cR_bool -> cRE_bool.
Coercion cR_cRE_SEXP := @cR_cRE SEXP : cR_SEXP -> cRE_SEXP.

Definition cR_cRH : forall T, cR T -> cRH T := fun _ => embed.
Coercion cR_cRH_bool := @cR_cRH bool : cR_bool -> cRH_bool.
Coercion cR_cRH_SEXP := @cR_cRH SEXP : cR_SEXP -> cRH_SEXP.

Definition cRE_cRHE : forall T, cRE T -> cRHE T := fun _ => embed.
Coercion cRE_cRHE_bool := @cRE_cRHE bool : cRE_bool -> cRHE_bool.
Coercion cRE_cRHE_SEXP := @cRE_cRHE SEXP : cRE_SEXP -> cRHE_SEXP.

(** The following coercion technically introduce a warning, but it is
  a benign one, as shown by the lemmas [ambiguous_coercion_cR_cRHE*]
  below.  We thus temporary disable the notation warning there. **)
Local Set Warnings "-ambiguous-paths".
Definition cRH_cRHE : forall T, cRH T -> cRHE T := fun _ => embed.
Coercion cRH_cRHE_bool := @cRH_cRHE bool : cRH_bool -> cRHE_bool.
Coercion cRH_cRHE_SEXP := @cRH_cRHE SEXP : cRH_SEXP -> cRHE_SEXP.
Local Set Warnings "ambiguous-paths". (** Setting the warning again. **)

Definition cRHE_cRHFE : forall T, cRHE T -> cRHFE T := fun _ => embed.
Coercion cRHE_cRHFE_bool := @cRHE_cRHFE bool : cRHE_bool -> cRHFE_bool.
Coercion cRHE_cRHFE_SEXP := @cRHE_cRHFE SEXP : cRHE_SEXP -> cRHFE_SEXP.

Definition cRHFE_cRHFJE : forall T, cRHFE T -> cRHFJE T := fun _ => embed.
Coercion cRHFE_cRHFJE_bool := @cRHFE_cRHFJE bool : cRHFE_bool -> cRHFJE_bool.
Coercion cRHFE_cRHFJE_SEXP := @cRHFE_cRHFJE SEXP : cRHFE_SEXP -> cRHFJE_SEXP.

Definition cRH_cRWH : forall T, cRH T -> cRWH T := fun _ => embed.
Coercion cRH_cRWH_bool := @cRH_cRWH bool : cRH_bool -> cRWH_bool.
Coercion cRH_cRWH_SEXP := @cRH_cRWH SEXP : cRH_SEXP -> cRWH_SEXP.

Definition cRWH_cRWHFJE : forall T, cRWH T -> cRWHFJE T := fun _ => embed.
Coercion cRWH_cRWHFJE_bool := @cRWH_cRWHFJE bool : cRWH_bool -> cRWHFJE_bool.
Coercion cRWH_cRWHFJE_SEXP := @cRWH_cRWHFJE SEXP : cRWH_SEXP -> cRWHFJE_SEXP.

(** As above, an ambiguous path is created, but it is a benign one, as shown by the lemmas
  [ambiguous_coercion_cRH_cRWHFJE*] below. **)
Local Set Warnings "-ambiguous-paths".
Definition cRHFJE_cRWHFJE : forall T, cRHFJE T -> cRWHFJE T := fun _ => embed.
Coercion cRHFJE_cRWHFJE_bool := @cRHFJE_cRWHFJE bool : cRHFJE_bool -> cRWHFJE_bool.
Coercion cRHFJE_cRWHFJE_SEXP := @cRHFJE_cRWHFJE SEXP : cRHFJE_SEXP -> cRWHFJE_SEXP.
Local Set Warnings "ambiguous-paths". (** Setting the warning again. **)

(** Some coercions above introduced ambiguous pathes, which we prove
  to not change the result. **)

Lemma ambiguous_coercion_cR_CRHE : forall T (e : cR T),
  cRH_cRHE (cR_cRH e) ≅ cRE_cRHE (cR_cRE e).
Proof.
  intros. unfolds cRH_cRHE, cR_cRH, cRE_cRHE, cR_cRE.
  repeat rewrite embed_unfold. unfolds Embeddable_itree_event.
  do 2 rewrite <- translate_cmpE. reflexivity.
Qed.

Lemma ambiguous_coercion_cR_CRHE_SEXP : forall e,
  cRH_cRHE_SEXP (cR_cRH_SEXP e) ≅ cRE_cRHE_SEXP (cR_cRE_SEXP e).
Proof. apply ambiguous_coercion_cR_CRHE. Qed.

Lemma ambiguous_coercion_cR_CRHE_bool : forall b,
  cRH_cRHE_bool (cR_cRH_bool b) ≅ cRE_cRHE_bool (cR_cRE_bool b).
Proof. apply ambiguous_coercion_cR_CRHE. Qed.

Lemma ambiguous_coercion_cRH_cRWHJE : forall T (e : cRH T),
  cRHFJE_cRWHFJE (cRHFE_cRHFJE (cRHE_cRHFE (cRH_cRHE e))) ≅ cRWH_cRWHFJE (cRH_cRWH e).
Proof.
  intros. unfolds cRHFJE_cRWHFJE, cRHFE_cRHFJE, cRHE_cRHFE, cRH_cRHE, cRWH_cRWHFJE, cRH_cRWH.
  repeat rewrite embed_unfold. unfolds Embeddable_itree_event.
  repeat rewrite <- translate_cmpE.
  lazymatch goal with |- translate ?f _ ≅ translate ?g _ => asserts E: (f = g) end.
  { clear. extens. intros T e. destruct~ e. }
  rewrite E. reflexivity.
Qed.

Lemma ambiguous_coercion_cRH_cRWHJE_SEXP : forall e,
  cRHFJE_cRWHFJE_SEXP (cRHFE_cRHFJE_SEXP (cRHE_cRHFE_SEXP (cRH_cRHE_SEXP e)))
  ≅ cRWH_cRWHFJE_SEXP (cRH_cRWH_SEXP e).
Proof. apply ambiguous_coercion_cRH_cRWHJE. Qed.

Lemma ambiguous_coercion_cRH_cRWHJE_bool : forall e,
  cRHFJE_cRWHFJE_bool (cRHFE_cRHFJE_bool (cRHE_cRHFE_bool (cRH_cRHE_bool e)))
  ≅ cRWH_cRWHFJE_bool (cRH_cRWH_bool e).
Proof. apply ambiguous_coercion_cRH_cRWHJE. Qed.


Instance cRE_Inhab : forall A, Inhab (cRE A) :=
  fun _ => Inhab_of_val (trigger (impossible "[arbitrary]")).

Instance cRHE_Inhab : forall A, Inhab (cRHE A) :=
  fun _ => Inhab_of_val (cRE_cRHE arbitrary).

Instance cRHFE_Inhab : forall A, Inhab (cRHFE A) :=
  fun _ => Inhab_of_val (cRHE_cRHFE arbitrary).

Instance cRHFJE_Inhab : forall A, Inhab (cRHFJE A) :=
  fun _ => Inhab_of_val (cRHFE_cRHFJE arbitrary).

Instance cRWHFJE_Inhab : forall A, Inhab (cRWHFJE A) :=
  fun _ => Inhab_of_val (cRHFJE_cRWHFJE arbitrary).


Open Scope monad_scope.

Definition SEXP_cR_SEXP (e : SEXP) : cR_SEXP := ret e.
Coercion SEXP_cR_SEXP : SEXP >-> cR_SEXP.

Definition bool_cR_bool (b : bool) : cR_bool := ret b.
Coercion bool_cR_bool : bool >-> cR_bool.

Definition GlobalVariable_cR_SEXP (G : GlobalVariable) : cR_SEXP := trigger (rglobal G).
Coercion GlobalVariable_cR_SEXP : GlobalVariable >-> cR_SEXP.

Definition cR_and (a b : cR_bool) : cR_bool :=
  a <- a ;;
  b <- b ;;
  ret (a && b).

Infix "'&&" := cR_and (at level 40, left associativity).

(** The lift of [&&] to ['&&] is just a lift in the contextual monad. **)
Lemma cR_and_bool : forall a b : bool,
  a '&& b ≅ (a && b : cR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition cR_or (a b : cR_bool) : cR_bool :=
  a <- a ;;
  b <- b ;;
  (a || b : cR_bool).

Infix "'||" := cR_or (at level 50, left associativity).

Lemma cR_or_bool : forall a b : bool,
  a '|| b ≅ (a || b : cR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition cR_neg (b : cR_bool) : cR_bool :=
  b <- b ;;
  (negb b : cR_bool).

Notation "'! b" := (cR_neg b) (at level 35, right associativity).

Lemma cR_neg_bool : forall b : bool,
  '! b ≅ (negb b : cR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition cR_decide P `{Decidable P} : cR_bool := decide P.
Arguments cR_decide P {_}.

Notation "''decide' P" := (cR_decide P) (at level 70, no associativity).

Definition cR_eq A `{Comparable A} (a b : cR A) : cR_bool :=
  a <- a ;;
  b <- b ;;
  'decide (a = b).

Definition cR_eq_SEXP : cR_SEXP -> cR_SEXP -> cR_bool := @cR_eq _ _.

Infix "'==" := cR_eq (at level 70, no associativity).

Notation "a '!= b" := ('! (a '== b)) (at level 70, no associativity).

Notation "'ifc' b 'then' v1 'else' v2" :=
  (x <- (b : cR_bool) ;; if x then v1 else v2)
  (at level 200, right associativity) : type_scope.


(** * [FUNTAB] **)

(** We have defined above the [Funtab] effect.  This effects calls a
  function with the following type. **)
Definition funtab_function :=
  SEXP -> (** call **)
  SEXP -> (** op **)
  SEXP -> (** args **)
  SEXP -> (** rho **)
  cRHFJE SEXP.

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

