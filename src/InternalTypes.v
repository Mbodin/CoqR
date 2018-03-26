(** InternalTypes.
  This file describes various internal data types used in the source of R. **)

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
Require Import Rinternals State.


(** * Monadic Type **)

(** A monad type for results. **)
Inductive result (A : Type) :=
  | result_success : state -> A -> result A (** The program resulted in this state with this result. **)
  | result_longjump : state -> nat -> context_type -> result A (** The program yielded a call to [LONGJMP] with these arguments. **)
  | result_error_stack : state -> list string -> string -> result A (** The program resulted in the following error (not meant to be caught). **)
  | result_impossible_stack : state -> list string -> string -> result A (** This result should never happen. We provide a string and a call stack to help debugging. **)
  | result_not_implemented_stack : list string -> string -> result A (** The result relies on a feature not yet implemented. **)
  | result_bottom : state -> result A (** We went out of fuel during the computation. **)
  .
Arguments result_longjump [A].
Arguments result_error_stack [A].
Arguments result_impossible_stack [A].
Arguments result_not_implemented_stack [A].
Arguments result_bottom [A].

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


Definition result_error (A : Type) S msg : result A :=
  result_error_stack S nil msg.
Arguments result_error [A].

Definition result_impossible (A : Type) S msg : result A :=
  result_impossible_stack S nil msg.
Arguments result_impossible [A].

Definition result_not_implemented (A : Type) msg : result A :=
  result_not_implemented_stack nil msg.
Arguments result_not_implemented [A].

Global Instance result_Inhab : forall A, Inhab (result A) :=
  fun _ => prove_Inhab (result_impossible arbitrary "[arbitrary]").


(** * [FUNTAB] **)

(** This section defines the FUNTAB structure, which is used to store
  primitive and internal functions, as well as some constructs to
  evaluate it. Most of these constructs can be found in
  include/Defn.h. **)

(** All function in the array [R_FunTab] have the same type. **)
Definition function_code :=
  state ->
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

Definition funtab := option (ArrayList.array funtab_cell).


(** * [Type2Table] **)

(** These definitions can be found in the file main/util.c. **)

Record Type2Table_type := make_Type2Table_type {
    Type2Table_cstrName : string ;
    Type2Table_rcharName : SEXP ;
    Type2Table_rstrName : SEXP ;
    Type2Table_rsymName : SEXP ;
  }.

Instance Type2Table_type_Inhab : Inhab Type2Table_type.
  apply prove_Inhab. constructors; apply arbitrary.
Qed.


(** * [BindData] **)

(** These definitions can be found in the file main/bind.c. **)

Record BindData := make_BindData {
    BindData_ans_flags : nbits 10 ;
    BindData_ans_ptr : SEXP ;
    BindData_ans_length : nat ;
    BindData_ans_names : SEXP ;
    BindData_ans_nnames : nat
  }.

Definition BindData_with_ans_flags d f := {|
    BindData_ans_flags := f ;
    BindData_ans_ptr := BindData_ans_ptr d ;
    BindData_ans_length := BindData_ans_length d ;
    BindData_ans_names := BindData_ans_names d ;
    BindData_ans_nnames := BindData_ans_nnames d
  |}.

Definition BindData_with_ans_ptr d p := {|
    BindData_ans_flags := BindData_ans_flags d ;
    BindData_ans_ptr := p ;
    BindData_ans_length := BindData_ans_length d ;
    BindData_ans_names := BindData_ans_names d ;
    BindData_ans_nnames := BindData_ans_nnames d
  |}.

Definition BindData_with_ans_length d l := {|
    BindData_ans_flags := BindData_ans_flags d ;
    BindData_ans_ptr := BindData_ans_ptr d ;
    BindData_ans_length := l ;
    BindData_ans_names := BindData_ans_names d ;
    BindData_ans_nnames := BindData_ans_nnames d
  |}.

Definition BindData_with_ans_names d n := {|
    BindData_ans_flags := BindData_ans_flags d ;
    BindData_ans_ptr := BindData_ans_ptr d ;
    BindData_ans_length := BindData_ans_length d ;
    BindData_ans_names := n ;
    BindData_ans_nnames := BindData_ans_nnames d
  |}.

Definition BindData_with_ans_nnames d n := {|
    BindData_ans_flags := BindData_ans_flags d ;
    BindData_ans_ptr := BindData_ans_ptr d ;
    BindData_ans_length := BindData_ans_length d ;
    BindData_ans_names := BindData_ans_names d ;
    BindData_ans_nnames := n
  |}.


(** * [pmatch] **)

(** These definitions can be found in the file main/subset.c. **)

Inductive pmatch :=
  | NO_MATCH
  | EXACT_MATCH
  | PARTIAL_MATCH
  .

