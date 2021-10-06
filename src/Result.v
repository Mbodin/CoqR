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

(** ** State **)

(** Events for the state: allocation, reading, and writing. **)

Inductive EState : Type -> Type :=
  | alloc_sexp : SExpRec -> EState unit
  | read_sexp : SEXP -> EState SExpRec
  | write_sexp : SEXP -> SExpRec -> EState unit
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

(** This project is based on the [itree] type.  This type is useful
  to define all the program’s effects, but in some context doesn’t
  behave well with coercions.
  In order to use Coq’s coercion mechanism, we identify the following
  usage cases, each being in a separate use-case of R functions:
  - R ([RGlobal]): the minimum level, only able to read global variables.
  - RE ([RGlobal +' Error]): as above, but are also allowed to fail.
  - RS ([RGlobal +' EState]): the level of most R functions that can’t fail:
    they read global variables as well as manipulate the C heap.
  - RSE ([RGlobal +' EState +' Error]): as above, but are also allowed to
    fail.
  - RSFE ([RGlobal +' EState +' Funtab +' Error]): the level of most R
    functions: they read global variables, manipulate the C heap, can call
    functions in the [FUNTAB] array, and fail.
  - RWS ([RGlobal +' WGlobal +' EState]): the level of some internal
    functions in [Rinit].
  - RSFJE ([RGlobal +' EState +' Funtab +' LongJump +' Error]): the level
    of some rare functions based on long jump, as well as the level of the
    functions in the [FUNTAB] array.
  - RWSFJE ([RGlobal +' WGlobal +' EState +' Funtab +' LongJump +' Error]):
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
Definition cRS T := itree (RGlobal +' EState) T.
Definition cRSE T := itree (RGlobal +' EState +' Error) T.
Definition cRSFE T := itree (RGlobal +' EState +' Funtab +' Error) T.
Definition cRWS T := itree (RGlobal +' WGlobal +' EState) T.
Definition cRSFJE T := itree (RGlobal +' EState +' Funtab +' LongJump +' Error) T.
Definition cRWSFJE T := itree (RGlobal +' WGlobal +' EState +' Funtab +' LongJump +' Error) T.

Instance Monad_cR : Monad cR := Monad_itree.
Instance Monad_cRE : Monad cRE := Monad_itree.
Instance Monad_cRS : Monad cRS := Monad_itree.
Instance Monad_cRSE : Monad cRSE := Monad_itree.
Instance Monad_cRSFE : Monad cRSE := Monad_itree.
Instance Monad_cRWS : Monad cRWS := Monad_itree.
Instance Monad_cRSFJE : Monad cRSFJE := Monad_itree.
Instance Monad_cRWSFJE : Monad cRWSFJE := Monad_itree.

Definition cR_bool := cR bool.
Definition cRE_bool := cRE bool.
Definition cRS_bool := cRS bool.
Definition cRSE_bool := cRSE bool.
Definition cRSFE_bool := cRSFE bool.
Definition cRWS_bool := cRWS bool.
Definition cRSFJE_bool := cRSFJE bool.
Definition cRWSFJE_bool := cRWSFJE bool.

Definition cR_SEXP := cR SEXP.
Definition cRE_SEXP := cRE SEXP.
Definition cRS_SEXP := cRS SEXP.
Definition cRSE_SEXP := cRSE SEXP.
Definition cRSFE_SEXP := cRSFE SEXP.
Definition cRWS_SEXP := cRWS SEXP.
Definition cRSFJE_SEXP := cRSFJE SEXP.
Definition cRWSFJE_SEXP := cRWSFJE SEXP.

Definition cR_cRE : forall T, cR T -> cRE T := fun _ => embed.
Coercion cR_cRE_bool := @cR_cRE bool : cR_bool -> cRE_bool.
Coercion cR_cRE_SEXP := @cR_cRE SEXP : cR_SEXP -> cRE_SEXP.

Definition cR_cRS : forall T, cR T -> cRS T := fun _ => embed.
Coercion cR_cRS_bool := @cR_cRS bool : cR_bool -> cRS_bool.
Coercion cR_cRS_SEXP := @cR_cRS SEXP : cR_SEXP -> cRS_SEXP.

Definition cRE_cRSE : forall T, cRE T -> cRSE T := fun _ => embed.
Coercion cRE_cRSE_bool := @cRE_cRSE bool : cRE_bool -> cRSE_bool.
Coercion cRE_cRSE_SEXP := @cRE_cRSE SEXP : cRE_SEXP -> cRSE_SEXP.

(** The following coercion technically introduce a warning, but it is
  a benign one, as shown by the lemmas
  [ambiguous_coercion_cR_cRS_cRE_CRSE_SEXP] and
  [ambiguous_coercion_cR_cRS_cRE_CRSE_bool] below.  We thus temporary
  disable the notation warning there. **)
Local Set Warnings "-ambiguous-paths".

Definition cRS_cRSE : forall T, cRS T -> cRSE T := fun _ => embed.
Coercion cRS_cRSE_bool := @cRS_cRSE bool : cRS_bool -> cRSE_bool.
Coercion cRS_cRSE_SEXP := @cRS_cRSE SEXP : cRS_SEXP -> cRSE_SEXP.

Local Set Warnings "ambiguous-paths". (** Setting the warning again. **)

Definition cRSE_cRSFE : forall T, cRSE T -> cRSFE T := fun _ => embed.
Coercion cRSE_cRSFE_bool := @cRSE_cRSFE bool : cRSE_bool -> cRSFE_bool.
Coercion cRSE_cRSFE_SEXP := @cRSE_cRSFE SEXP : cRSE_SEXP -> cRSFE_SEXP.

Definition cRS_cRWS : forall T, cRS T -> cRWS T := fun _ => embed.
Coercion cRS_cRWS_bool := @cRS_cRWS bool : cRS_bool -> cRWS_bool.
Coercion cRS_cRWS_SEXP := @cRS_cRWS SEXP : cRS_SEXP -> cRWS_SEXP.

Definition cRSFE_cRSFJE : forall T, cRSFE T -> cRSFJE T := fun _ => embed.
Coercion cRSFE_cRSFJE_bool := @cRSFE_cRSFJE bool : cRSFE_bool -> cRSFJE_bool.
Coercion cRSFE_cRSFJE_SEXP := @cRSFE_cRSFJE SEXP : cRSFE_SEXP -> cRSFJE_SEXP.

Definition cRSFJE_cRWSFJE : forall T, cRSFJE T -> cRWSFJE T := fun _ => embed.
Coercion cRSJE_cRWSFJE_bool := @cRSFJE_cRWSFJE bool : cRSFJE_bool -> cRWSFJE_bool.
Coercion cRSJE_cRWSFJE_SEXP := @cRSFJE_cRWSFJE SEXP : cRSFJE_SEXP -> cRWSFJE_SEXP.


(** Some coercions above introduced ambiguous pathes, which we prove
  to not change the result. **)

Lemma ambiguous_coercion_cR_cRS_cRE_CRSE_SEXP : forall e,
  cRS_cRSE_SEXP (cR_cRS_SEXP e) ≅ cRE_cRSE_SEXP (cR_cRE_SEXP e).
Proof.
  intros.
  unfolds cRS_cRSE_SEXP, cRS_cRSE. unfolds cR_cRS_SEXP, cR_cRS.
  unfolds cR_cRE_SEXP, cR_cRE. unfolds cRE_cRSE_SEXP, cRE_cRSE.
  repeat rewrite embed_unfold. unfolds Embeddable_itree_event.
  do 2 rewrite <- translate_cmpE. reflexivity.
Qed.

Lemma ambiguous_coercion_cR_cRS_cRE_CRSE_bool : forall b,
  cRS_cRSE_bool (cR_cRS_bool b) ≅ cRE_cRSE_bool (cR_cRE_bool b).
Proof.
  intros.
  unfolds cRS_cRSE_bool, cRS_cRSE. unfolds cR_cRS_bool, cR_cRS.
  unfolds cR_cRE_bool, cR_cRE. unfolds cRE_cRSE_bool, cRE_cRSE.
  repeat rewrite embed_unfold. unfolds Embeddable_itree_event.
  do 2 rewrite <- translate_cmpE. reflexivity.
Qed.


Instance cRE_Inhab : forall A, Inhab (cRE A) :=
  fun _ => Inhab_of_val (trigger (impossible "[arbitrary]")).

Instance cRSE_Inhab : forall A, Inhab (cRSE A) :=
  fun _ => Inhab_of_val (cRE_cRSE arbitrary).

Instance cRSFE_Inhab : forall A, Inhab (cRSFE A) :=
  fun _ => Inhab_of_val (cRSE_cRSFE arbitrary).

Instance cRSFJE_Inhab : forall A, Inhab (cRSFJE A) :=
  fun _ => Inhab_of_val (cRSFE_cRSFJE arbitrary).

Instance cRWSFJE_Inhab : forall A, Inhab (cRWSFJE A) :=
  fun _ => Inhab_of_val (cRSFJE_cRWSFJE arbitrary).


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
  cRSFJE SEXP.

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

