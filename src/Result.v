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

Section UniverseHelp. (* See https://github.com/coq/coq/issues/15049 *)
Constraint itreeF.u1 < ArrayList.array.u.
End UniverseHelp.

(** This project is based on the [itree] type.  This type is useful
  to define all the program’s effects, but in some context doesn’t
  behave well with coercions.
  In order to use Coq’s coercion mechanism, we identify the following
  usage cases, each being in a separate use-case of R functions:
  - R ([RGlobal]): the minimum level, only able to read global variables
    (typically [R_NilValue]—see [Globals]).
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
  For each of these levels, we define a monadic type (for instance, [mRE] for
  the RE level), as well as coercions to other levels to easily manipulate them.)
  Unfortunately, Coq coercions don’t manipulate [forall] quantifiers, and we
  have to limit ourselves to the two most common results: [bool] and [SEXP].
  The fact that we can split all R functions into these separate levels was
  not obvious from the organisation of GNU R, but shows some intuition on
  how it is structured. **)

Definition mR T := itree RGlobal T.
Definition mRE T := itree (RGlobal +' Error) T.
Definition mRH T := itree (RGlobal +' EHeap) T.
Definition mRHE T := itree (RGlobal +' EHeap +' Error) T.
Definition mRHFE T := itree (RGlobal +' EHeap +' Funtab +' Error) T.
Definition mRHFJE T := itree (RGlobal +' EHeap +' Funtab +' LongJump +' Error) T.
Definition mRWH T := itree (RGlobal +' WGlobal +' EHeap) T.
Definition mRWHFJE T := itree (RGlobal +' WGlobal +' EHeap +' Funtab +' LongJump +' Error) T.

Instance Monad_mR : Monad mR := Monad_itree.
Instance Monad_mRE : Monad mRE := Monad_itree.
Instance Monad_mRH : Monad mRH := Monad_itree.
Instance Monad_mRHE : Monad mRHE := Monad_itree.
Instance Monad_mRHFE : Monad mRHE := Monad_itree.
Instance Monad_mRHFJE : Monad mRHFJE := Monad_itree.
Instance Monad_mRWH : Monad mRWH := Monad_itree.
Instance Monad_mRWHFJE : Monad mRWHFJE := Monad_itree.

Definition mR_bool := mR bool.
Definition mRE_bool := mRE bool.
Definition mRH_bool := mRH bool.
Definition mRHE_bool := mRHE bool.
Definition mRHFE_bool := mRHFE bool.
Definition mRHFJE_bool := mRHFJE bool.
Definition mRWH_bool := mRWH bool.
Definition mRWHFJE_bool := mRWHFJE bool.

Definition mR_SEXP := mR SEXP.
Definition mRE_SEXP := mRE SEXP.
Definition mRH_SEXP := mRH SEXP.
Definition mRHE_SEXP := mRHE SEXP.
Definition mRHFE_SEXP := mRHFE SEXP.
Definition mRHFJE_SEXP := mRHFJE SEXP.
Definition mRWH_SEXP := mRWH SEXP.
Definition mRWHFJE_SEXP := mRWHFJE SEXP.

Definition mR_mRE : forall T, mR T -> mRE T := fun _ => embed.
Coercion mR_mRE_bool := @mR_mRE bool : mR_bool -> mRE_bool.
Coercion mR_mRE_SEXP := @mR_mRE SEXP : mR_SEXP -> mRE_SEXP.

Definition mR_mRH : forall T, mR T -> mRH T := fun _ => embed.
Coercion mR_mRH_bool := @mR_mRH bool : mR_bool -> mRH_bool.
Coercion mR_mRH_SEXP := @mR_mRH SEXP : mR_SEXP -> mRH_SEXP.

Definition mRE_mRHE : forall T, mRE T -> mRHE T := fun _ => embed.
Coercion mRE_mRHE_bool := @mRE_mRHE bool : mRE_bool -> mRHE_bool.
Coercion mRE_mRHE_SEXP := @mRE_mRHE SEXP : mRE_SEXP -> mRHE_SEXP.

(** The following coercion technically introduce a warning, but it is
  a benign one, as shown by the lemmas [ambiguous_coercion_mR_mRHE*]
  below.  We thus temporary disable the notation warning there. **)
Local Set Warnings "-ambiguous-paths".
Definition mRH_mRHE : forall T, mRH T -> mRHE T := fun _ => embed.
Coercion mRH_mRHE_bool := @mRH_mRHE bool : mRH_bool -> mRHE_bool.
Coercion mRH_mRHE_SEXP := @mRH_mRHE SEXP : mRH_SEXP -> mRHE_SEXP.
Local Set Warnings "ambiguous-paths". (** Setting the warning again. **)

Definition mRHE_mRHFE : forall T, mRHE T -> mRHFE T := fun _ => embed.
Coercion mRHE_mRHFE_bool := @mRHE_mRHFE bool : mRHE_bool -> mRHFE_bool.
Coercion mRHE_mRHFE_SEXP := @mRHE_mRHFE SEXP : mRHE_SEXP -> mRHFE_SEXP.

Definition mRHFE_mRHFJE : forall T, mRHFE T -> mRHFJE T := fun _ => embed.
Coercion mRHFE_mRHFJE_bool := @mRHFE_mRHFJE bool : mRHFE_bool -> mRHFJE_bool.
Coercion mRHFE_mRHFJE_SEXP := @mRHFE_mRHFJE SEXP : mRHFE_SEXP -> mRHFJE_SEXP.

Definition mRH_mRWH : forall T, mRH T -> mRWH T := fun _ => embed.
Coercion mRH_mRWH_bool := @mRH_mRWH bool : mRH_bool -> mRWH_bool.
Coercion mRH_mRWH_SEXP := @mRH_mRWH SEXP : mRH_SEXP -> mRWH_SEXP.

Definition mRWH_mRWHFJE : forall T, mRWH T -> mRWHFJE T := fun _ => embed.
Coercion mRWH_mRWHFJE_bool := @mRWH_mRWHFJE bool : mRWH_bool -> mRWHFJE_bool.
Coercion mRWH_mRWHFJE_SEXP := @mRWH_mRWHFJE SEXP : mRWH_SEXP -> mRWHFJE_SEXP.

(** As above, an ambiguous path is created, but it is a benign one, as shown by the lemmas
  [ambiguous_coercion_mRH_mRWHFJE*] below. **)
Local Set Warnings "-ambiguous-paths".
Definition mRHFJE_mRWHFJE : forall T, mRHFJE T -> mRWHFJE T := fun _ => embed.
Coercion mRHFJE_mRWHFJE_bool := @mRHFJE_mRWHFJE bool : mRHFJE_bool -> mRWHFJE_bool.
Coercion mRHFJE_mRWHFJE_SEXP := @mRHFJE_mRWHFJE SEXP : mRHFJE_SEXP -> mRWHFJE_SEXP.
Local Set Warnings "ambiguous-paths". (** Setting the warning again. **)

(** Some coercions above introduced ambiguous pathes, which we prove
  to not change the result. **)

Lemma ambiguous_coercion_mR_CRHE : forall T (e : mR T),
  mRH_mRHE (mR_mRH e) ≅ mRE_mRHE (mR_mRE e).
Proof.
  intros. unfolds mRH_mRHE, mR_mRH, mRE_mRHE, mR_mRE.
  repeat rewrite embed_unfold. unfolds Embeddable_itree_event.
  do 2 rewrite <- translate_cmpE. reflexivity.
Qed.

Lemma ambiguous_coercion_mR_CRHE_bool : forall b,
  mRH_mRHE_bool (mR_mRH_bool b) ≅ mRE_mRHE_bool (mR_mRE_bool b).
Proof. apply ambiguous_coercion_mR_CRHE. Qed.

Lemma ambiguous_coercion_mR_CRHE_SEXP : forall e,
  mRH_mRHE_SEXP (mR_mRH_SEXP e) ≅ mRE_mRHE_SEXP (mR_mRE_SEXP e).
Proof. apply ambiguous_coercion_mR_CRHE. Qed.

Lemma ambiguous_coercion_mRH_mRWHJE : forall T (e : mRH T),
  mRHFJE_mRWHFJE (mRHFE_mRHFJE (mRHE_mRHFE (mRH_mRHE e))) ≅ mRWH_mRWHFJE (mRH_mRWH e).
Proof.
  intros. unfolds mRHFJE_mRWHFJE, mRHFE_mRHFJE, mRHE_mRHFE, mRH_mRHE, mRWH_mRWHFJE, mRH_mRWH.
  repeat rewrite embed_unfold. unfolds Embeddable_itree_event.
  repeat rewrite <- translate_cmpE.
  lazymatch goal with |- translate ?f _ ≅ translate ?g _ => asserts E: (f = g) end.
  { clear. extens. intros T e. destruct~ e. }
  rewrite E. reflexivity.
Qed.

Lemma ambiguous_coercion_mRH_mRWHJE_bool : forall e,
  mRHFJE_mRWHFJE_bool (mRHFE_mRHFJE_bool (mRHE_mRHFE_bool (mRH_mRHE_bool e)))
  ≅ mRWH_mRWHFJE_bool (mRH_mRWH_bool e).
Proof. apply ambiguous_coercion_mRH_mRWHJE. Qed.

Lemma ambiguous_coercion_mRH_mRWHJE_SEXP : forall e,
  mRHFJE_mRWHFJE_SEXP (mRHFE_mRHFJE_SEXP (mRHE_mRHFE_SEXP (mRH_mRHE_SEXP e)))
  ≅ mRWH_mRWHFJE_SEXP (mRH_mRWH_SEXP e).
Proof. apply ambiguous_coercion_mRH_mRWHJE. Qed.

Lemma ambiguous_coercion_mR_mRWHJE : forall T (e : mR T),
  mRHFJE_mRWHFJE (mRHFE_mRHFJE (mRHE_mRHFE (mRE_mRHE (mR_mRE e))))
  ≅ mRWH_mRWHFJE (mRH_mRWH (mR_mRH e)).
Proof.
  intros. unfolds mRHFJE_mRWHFJE, mRHFE_mRHFJE, mRHE_mRHFE, mRE_mRHE, mR_mRE.
  unfolds mRWH_mRWHFJE, mRH_mRWH, mR_mRH.
  repeat rewrite embed_unfold. unfolds Embeddable_itree_event.
  repeat rewrite <- translate_cmpE.
  lazymatch goal with |- translate ?f _ ≅ translate ?g _ => asserts E: (f = g) end.
  { clear. extens. intros T e. destruct~ e. }
  rewrite E. reflexivity.
Qed.

Lemma ambiguous_coercion_mR_mRWHJE_bool : forall e,
  mRHFJE_mRWHFJE_bool (mRHFE_mRHFJE_bool (mRHE_mRHFE_bool (mRE_mRHE_bool (mR_mRE_bool e))))
  ≅ mRWH_mRWHFJE_bool (mRH_mRWH_bool (mR_mRH_bool e)).
Proof. apply ambiguous_coercion_mR_mRWHJE. Qed.

Lemma ambiguous_coercion_mR_mRWHJE_SEXP : forall e,
  mRHFJE_mRWHFJE_SEXP (mRHFE_mRHFJE_SEXP (mRHE_mRHFE_SEXP (mRE_mRHE_SEXP (mR_mRE_SEXP e))))
  ≅ mRWH_mRWHFJE_SEXP (mRH_mRWH_SEXP (mR_mRH_SEXP e)).
Proof. apply ambiguous_coercion_mR_mRWHJE. Qed.

Instance mRE_Inhab : forall A, Inhab (mRE A) :=
  fun _ => Inhab_of_val (trigger (impossible "[arbitrary]")).

Instance mRHE_Inhab : forall A, Inhab (mRHE A) :=
  fun _ => Inhab_of_val (mRE_mRHE arbitrary).

Instance mRHFE_Inhab : forall A, Inhab (mRHFE A) :=
  fun _ => Inhab_of_val (mRHE_mRHFE arbitrary).

Instance mRHFJE_Inhab : forall A, Inhab (mRHFJE A) :=
  fun _ => Inhab_of_val (mRHFE_mRHFJE arbitrary).

Instance mRWHFJE_Inhab : forall A, Inhab (mRWHFJE A) :=
  fun _ => Inhab_of_val (mRHFJE_mRWHFJE arbitrary).


Open Scope monad_scope.

Definition SEXP_mR_SEXP (e : SEXP) : mR_SEXP := ret e.
Coercion SEXP_mR_SEXP : SEXP >-> mR_SEXP.

Definition bool_mR_bool (b : bool) : mR_bool := ret b.
Coercion bool_mR_bool : bool >-> mR_bool.

Definition GlobalVariable_mR_SEXP (G : GlobalVariable) : mR_SEXP := trigger (rglobal G).
Coercion GlobalVariable_mR_SEXP : GlobalVariable >-> mR_SEXP.

Definition mR_and (a b : mR_bool) : mR_bool :=
  a <- a ;;
  b <- b ;;
  ret (a && b).

Infix "'&&" := mR_and (at level 40, left associativity).

(** The lift of [&&] to ['&&] is just a lift in the contextual monad. **)
Lemma mR_and_bool : forall a b : bool,
  a '&& b ≅ (a && b : mR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition mR_or (a b : mR_bool) : mR_bool :=
  a <- a ;;
  b <- b ;;
  (a || b : mR_bool).

Infix "'||" := mR_or (at level 50, left associativity).

Lemma mR_or_bool : forall a b : bool,
  a '|| b ≅ (a || b : mR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition mR_neg (b : mR_bool) : mR_bool :=
  b <- b ;;
  (negb b : mR_bool).

Notation "'! b" := (mR_neg b) (at level 35, right associativity).

Lemma mR_neg_bool : forall b : bool,
  '! b ≅ (negb b : mR_bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition mR_decide P `{Decidable P} : mR_bool := decide P.
Arguments mR_decide P {_}.

Notation "''decide' P" := (mR_decide P) (at level 70, no associativity).

Definition mR_eq A `{Comparable A} (a b : mR A) : mR_bool :=
  a <- a ;;
  b <- b ;;
  'decide (a = b).

Definition mR_eq_SEXP : mR_SEXP -> mR_SEXP -> mR_bool := @mR_eq _ _.

Infix "'==" := mR_eq (at level 70, no associativity).

Notation "a '!= b" := ('! (a '== b)) (at level 70, no associativity).

Notation "'ifc' b 'then' v1 'else' v2" :=
  (x <- (b : mR_bool) ;; if x then v1 else v2)
  (at level 200, right associativity) : type_scope.


(** * [FUNTAB] **)

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

