(** InternalTypes.
  This file describes central internal data types used in the source of R. **)

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
Require Import Rinternals State MiscellaneousTypes Globals.


(** * Monadic Type **)

(** A monad type for results. **)
Inductive rresult (A : Type) :=
  | result_success : A -> state -> rresult A (** The program resulted in this state with this result. **)
  | result_longjump : nat -> context_type -> state -> rresult A (** The program yielded a call to [LONGJMP] with these arguments. **)
  | result_error_stack : list string -> string -> state -> rresult A (** The program resulted in the following error (not meant to be caught). **)
  | result_impossible_stack : list string -> string -> state -> rresult A (** This result should never happen. We provide a string and a call stack to help debugging. **)
  | result_not_implemented_stack : list string -> string -> rresult A (** The result relies on a feature not yet implemented. **)
  | result_bottom : state -> rresult A (** We went out of fuel during the computation. **)
  .
Arguments result_longjump [A].
Arguments result_error_stack [A].
Arguments result_impossible_stack [A].
Arguments result_not_implemented_stack [A].
Arguments result_bottom {A}.

(** We wrap [rresult] in a state monad. **)
Definition result A := Globals -> state -> rresult A.

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


Definition result_error (A : Type) msg : result A :=
  fun _ => result_error_stack nil msg.
Arguments result_error [A].

Definition result_impossible (A : Type) msg : result A :=
  fun _ => result_impossible_stack nil msg.
Arguments result_impossible [A].

Definition result_not_implemented (A : Type) msg : result A :=
  fun _ S => result_not_implemented_stack nil msg.
Arguments result_not_implemented [A].

Global Instance result_Inhab : forall A, Inhab (result A) :=
  fun _ => prove_Inhab (result_impossible "[arbitrary]").


(** * [FUNTAB] **)

(** This section defines the FUNTAB structure, which is used to store
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

(** The following type is represented in C as an integer, each of its figure
  (in base 10) representing a different bit of information. **)
Record funtab_eval_arg := make_funtab_eval_arg {
    funtab_eval_arg_internal : bool ; (** Whether it is stored in the array [.Internals] or directly visible. **)
    funtab_eval_arg_eval : bool (** Whether its arguments should be evaluated before calling (that is, whether it is a [BuiltinSxp] or a [SpecialSxp]). **)
  }.

Instance funtab_eval_arg_Inhab : Inhab funtab_eval_arg.
  apply prove_Inhab. constructors; typeclass.
Qed.

(** [PPkind] **)
Inductive PPkind :=
  | PP_INVALID
  | PP_ASSIGN
  | PP_ASSIGN2
  | PP_BINARY
  | PP_BINARY2
  | PP_BREAK
  | PP_CURLY
  | PP_FOR
  | PP_FUNCALL
  | PP_FUNCTION
  | PP_IF
  | PP_NEXT
  | PP_PAREN
  | PP_RETURN
  | PP_SUBASS
  | PP_SUBSET
  | PP_WHILE
  | PP_UNARY
  | PP_DOLLAR
  | PP_FOREIGN
  | PP_REPEAT
  .

Instance PPkind_Comparable : Comparable PPkind.
  prove_comparable_trivial_inductive.
Defined.

Instance PPkind_Inhab : Inhab PPkind.
  apply prove_Inhab. constructors~.
Qed.

(** [PPprec] **)
Inductive PPprec :=
  | PREC_FN
  | PREC_EQ
  | PREC_LEFT
  | PREC_RIGHT
  | PREC_TILDE
  | PREC_OR
  | PREC_AND
  | PREC_NOT
  | PREC_COMPARE
  | PREC_SUM
  | PREC_PROD
  | PREC_PERCENT
  | PREC_COLON
  | PREC_SIGN
  | PREC_POWER
  | PREC_SUBSET
  | PREC_DOLLAR
  | PREC_NS
  .

Instance PPprec_Comparable : Comparable PPprec.
  prove_comparable_trivial_inductive.
Defined.

Instance PPprecd_Inhab : Inhab PPprec.
  apply prove_Inhab. constructors~.
Qed.

(** [PPinfo] **)
Record PPinfo := make_PPinfo {
    PPinfo_kind : PPkind ;
    PPinfo_precedence : PPprec ;
    PPinfo_rightassoc : bool
  }.

Instance PPinfo_Inhab : Inhab PPinfo.
  apply prove_Inhab. constructors; typeclass.
Qed.

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
