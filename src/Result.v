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
Require Import Rinternals State InternalTypes Globals.


(** * Monadic Type **)

(** A monad type for results. **)
Inductive rresult (A : Type) :=
  | rresult_success : A -> state -> rresult A (** The program resulted in this state with this result. **)
  | rresult_longjump : nat -> context_type -> state -> rresult A (** The program yielded a call to [LONGJMP] with these arguments. **)
  | rresult_error_stack : list string -> string -> state -> rresult A (** The program resulted in the following error (not meant to be caught). **)
  | rresult_impossible_stack : list string -> string -> state -> rresult A (** This result should never happen. We provide a string and a call stack to help debugging. **)
  | rresult_not_implemented_stack : list string -> string -> rresult A (** The result relies on a feature not yet implemented. **)
  | rresult_bottom : state -> rresult A (** We went out of fuel during the computation. **)
  .
Arguments rresult_success [A].
Arguments rresult_longjump [A].
Arguments rresult_error_stack [A].
Arguments rresult_impossible_stack [A].
Arguments rresult_not_implemented_stack [A].
Arguments rresult_bottom {A}.

(** We wrap [rresult] in a state monad. **)
Definition result A := Globals -> state -> rresult A.


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
  fun _ => prove_Inhab (result_impossible "[arbitrary]").


(** A precision about [result_not_implemented] and [result_error]:
  if the C source code of R throw a not-implemented error, we consider
  this as an error thrown in the original interpreter and use the
  constructor [result_error].
  We only throw [result_not_implemented] when our Coq code has not
  implemented a behaviour of R.
  The construct [result_error] thus models the errors thrown by the
  R program. **)

(** The difference between [result_error] and [result_impossible] is
  that [result_error] is thrown when the R interpreter throws an error
  (usally using the [error] C function), and [result_impossible] is
  thrown when R does not throw an error, but we know for sure that such
  a case can never happen, or such a case would lead an undefined
  behaviour in the original program. Typically because the C program accepts
  an impossible case to be missing, but that Coq does not recognise this
  case to be impossible. So if there is a possible case in which Coq
  must return something, but that the R interpreter in C does not cover
  this case (for instance by writting [e->type] without checking whether
  [e] actually maps to a valid expression), the Coq interpreter will
  return [result_impossible]. **)


(** * [_SEXP] **)

(** The [eventually A] type represents something that can be converted into
  a [A] given the right context (corresponding to the ones of [result A]. **)

Definition eventually (A : Type) := Globals -> state -> A.

(** The most frequently used is [_SEXP]. **)
Definition _SEXP := eventually SEXP.


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
  apply prove_Inhab. constructors; apply arbitrary.
Qed.

Definition funtab := ArrayList.array funtab_cell.

