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
From ITree Require Export ITree.
From ExtLib Require Structures.Monad.


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

(** ** Control-flow **)

(** We distinguish between erroneous events and jumping events. **)

(** Erroneous events break the control-flow, halting the execution. **)

Inductive Error : Type -> Type :=
  | error : forall T, string -> Error T
  (** The program yielded an error described by the provided message.
    This error is not guaranteed not to happen. **)
  | impossible : forall T, string -> Error T
  (** Similar to [error], but this error is not meant to happens.
    If such an error happens, it is either a bug in the CoqR interpreter, or an undefined
    behaviour of the (source code of the) reference interpreter GNU R. **)
  | not_implemented : forall T, string -> Error T
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
  | longjump : forall T, nat -> context_type -> LongJump T
  (** the program yielded a call to [LONGJMP] with the provided arguments. **)
  .


(** * Standard Events **)

(** The events declared in the previous section are useful to separately
  express all the kinds of events that a R function can use.
  However, it would be cumbersome to assume all the assumptions of the
  form [eff -< Error] for each of the usual kinds.
  We thus introduce, as a shortcut, the following definition. **)

Class StandardEvents eff := {
    StandardRGlobal :> RGlobal -< eff ;
    (** Reading global variables is usual, but writing is not. **)
    StandardEState :> EState -< eff ;
    StandardError :> Error -< eff ;
    (** Long jumps are not commons. **)
  }.


(** * Contextual Type **)

(** This project is based on the [itree] type.  This type is useful
  to define all the program’s effects, but in some context doesn’t
  behave well with coercions.  We introduce an ad-hoc type
  [contextual] in order to help us coercing global variables into
  the [SEXP] type in specific [if]-conditions.
  In order to activate these coercions, we wrap them within a module. **)

Module Type StandardEventsType.

Parameter eff : Type -> Type.
Parameter std : StandardEvents eff.

End StandardEventsType.

Module Contextual (EFF : StandardEventsType).

Export EFF.

Local Instance std : StandardEvents eff := std.

Import Structures.Monad.
Import Monads.
Import MonadNotation.

Open Scope monad_scope.

Definition contextual T := itree eff T.

Instance Monad_contextual : Monad contextual := Monad_itree.

Definition _bool := contextual bool.
Definition _SEXP := contextual SEXP.

Definition SEXP_SEXP (e : SEXP) : _SEXP := ret e.
Coercion SEXP_SEXP : SEXP >-> _SEXP.

Definition bool_bool (b : bool) : _bool := ret b.
Coercion bool_bool : bool >-> _bool.

Definition GlobalVariable_SEXP (G : GlobalVariable) : _SEXP := trigger (rglobal G).
Coercion GlobalVariable_SEXP : GlobalVariable >-> _SEXP.

Definition contextual_and (a b : _bool) : _bool :=
  a <- a ;;
  b <- b ;;
  ret (a && b).

Infix "'&&" := contextual_and (at level 40, left associativity).

Open Scope type_scope.
Import Eq.

(** The lift of [&&] to ['&&] is just a lift in the contextual monad. **)
Lemma contextual_and_bool : forall a b : bool,
  a '&& b ≈ (a && b : _bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition contextual_or (a b : _bool) : _bool :=
  a <- a ;;
  b <- b ;;
  (a || b : _bool).

Infix "'||" := contextual_or (at level 50, left associativity).

Lemma contextual_or_bool : forall a b : bool,
  a '|| b ≈ (a || b : _bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition contextual_neg (b : _bool) : _bool :=
  b <- b ;;
  (negb b : _bool).

Notation "'! b" := (contextual_neg b) (at level 35, right associativity).

Lemma contextual_neg_bool : forall b : bool,
  '! b ≈ (negb b : _bool).
Proof. intros. tau_steps. reflexivity. Qed.

Definition contextual_decide P `{Decidable P} : _bool := decide P.
Arguments contextual_decide P {_}.

Notation "''decide' P" := (contextual_decide P) (at level 70, no associativity).

Definition contextual_eq A `{Comparable A} (a b : contextual A) : _bool :=
  a <- a ;;
  b <- b ;;
  'decide (a = b).

Definition contextual_eq_SEXP : _SEXP -> _SEXP -> _bool := @contextual_eq _ _.

Infix "'==" := contextual_eq (at level 70, no associativity).

Notation "a '!= b" := ('! (a '== b)) (at level 70, no associativity).

Notation "'ifc' b 'then' v1 'else' v2" :=
  (x <- (b : _bool) ;; if x then v1 else v2)
  (at level 200, right associativity) : type_scope.

End Contextual.


(* TODO: update ************************************************** *)

(** ** [contextual]: [_SEXP] and [_bool] **)

(** The [contextual A] type represents something that can be converted into
  a [A] given the right context, of global variables and current state.
  This monad is used in the [result] monad below. **)

Definition contextual (A : Type) := Globals -> state -> A.

(** The most frequently used instances are [_SEXP] and [_bool]. **)
Definition _SEXP := contextual SEXP.
Definition _bool := contextual bool.

(** The bind operation of the monad. **)
Definition contextual_bind A B (e : contextual A) (cont : A -> contextual B) : contextual B :=
  fun globals S => cont (e globals S) globals S.

(** The return operation of the monad. **)
Definition contextual_ret A (a : A) : contextual A :=
  fun _ _ => a.

Declare Scope monad_scope.

Notation "'let%contextual' a ':=' e 'in' cont" :=
  (contextual_bind e (fun a => cont))
  (at level 50, left associativity) : monad_scope.


(** ** The main monad: [result] **)

(** The monad type of results.
  Every function in this formalisation returns a type in this monad.
  A result can be:
  - [rresult_success r A]: the program succeedingly resulted in [r] in the state [S].
  - [rresult_longjump]: the program yielded a call to [LONGJMP] with the provided arguments.
  - [rresult_error_stack stack msg S]: the program resulted in an error described by [msg],
    with the state [S], and the call stack [stack].
    This error is not meant to be caught: it will be propagated along to be printed.
  - [rresult_impossible_stack]: this result should never happen.
    It corresponds to either a bug in the CoqR interpreter, or an undefined behaviour of the
    (source code of the) reference interpreter GNU R.
  - [rresult_not_implemented_stack]: the result relies on a feature not yet implemented.
  - [rresult_bottom]: a termination monad.
    Indeed, in Coq, any function has to terminate.  As R program may not, we provide some
    fuel which is decremented along the way.  Reaching [0] yields this result: we went out
    of fuel during the computation. **)
Inductive rresult (A : Type) :=
  | rresult_success : A -> state -> rresult A
  | rresult_longjump : nat -> context_type -> state -> rresult A
  | rresult_error_stack : list string -> string -> state -> rresult A
  | rresult_impossible_stack : list string -> string -> state -> rresult A
  | rresult_not_implemented_stack : list string -> string -> rresult A
  | rresult_bottom : state -> rresult A
  .
Arguments rresult_success [A].
Arguments rresult_longjump [A].
Arguments rresult_error_stack [A].
Arguments rresult_impossible_stack [A].
Arguments rresult_not_implemented_stack [A].
Arguments rresult_bottom {A}.

(** We wrap [rresult] in a state monad. **)
Definition result A := contextual (rresult A).


Definition result_success : forall A, A -> result A :=
  fun _ a _ => rresult_success a.
Arguments result_success [A].

Definition result_longjump (A : Type) : nat -> context_type -> result A :=
  fun i ct _ => rresult_longjump i ct.
Arguments result_longjump [A].

Definition result_error (A : Type) msg : result A :=
  fun _ => rresult_error_stack nil msg.
Arguments result_error [A].

Definition result_impossible (A : Type) msg : result A :=
  fun _ => rresult_impossible_stack nil msg.
Arguments result_impossible [A].

Definition result_not_implemented (A : Type) msg : result A :=
  fun _ S => rresult_not_implemented_stack nil msg.
Arguments result_not_implemented [A].

Definition result_bottom : forall A, result A :=
  fun _ _ => rresult_bottom.
Arguments result_bottom {A}.

Global Instance result_Inhab : forall A, Inhab (result A) :=
  fun _ => Inhab_of_val (result_impossible "[arbitrary]").



(** * [FUNTAB] **)

(** This section defines the [FUNTAB] structure, which is used to store
  primitive and internal functions, as well as some constructs to
  evaluate it. Most of these constructs can be found in
  include/Defn.h. **)

(** Following GNU R, all functions in the array [R_FunTab] have the same type: they take four SEXP
  and return an SEXP.
  The four SEXP respectively correspond to the call, op, args, and rho parameters of each functions.
  The most important is args, which is an R list of arguments. **)
Definition function_code :=
  SEXP -> (** call **)
  SEXP -> (** op **)
  SEXP -> (** args **)
  SEXP -> (** rho **)
  result SEXP.

(** [FUNTAB] **)
Record funtab_cell := make_funtab_cell {
    fun_name : string ;
    fun_cfun : function_code ;
    fun_code : int ; (** The number stored here can be quite large. We thus use [int] instead of [nat] here. **)
    fun_eval : funtab_eval_arg ;
    fun_arity : int ;
    fun_gram : PPinfo
  }.

Instance funtab_cell_Inhab : Inhab funtab_cell.
  apply Inhab_of_val. constructors; apply arbitrary.
Qed.

Definition funtab := ArrayList.array funtab_cell.

