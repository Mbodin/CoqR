(** InternalTypes.
  This file describes various internal data types used in the source of R. **)

(* Copyright © 2020 Martin Bodin

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

Require Export Rinternals.
From Lib Require Export Common.

(** * [Type2Table] **)

(** These definitions can be found in the file main/util.c. **)

Record Type2Table_type := make_Type2Table_type {
    Type2Table_cstrName : string ;
    Type2Table_rcharName : SEXP ;
    Type2Table_rstrName : SEXP ;
    Type2Table_rsymName : SEXP ;
  }.

Instance Type2Table_type_Inhab : Inhab Type2Table_type.
  apply Inhab_of_val. constructors; apply arbitrary.
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

(** * [FUNTAB] **)

(** This section defines types used by the [FUNTAB] structure,
  which is used to store primitive and internal functions, as
  well as some constructs to evaluate it.
  Not all definitions could be placed in this file as some
  depends on the [result] monad: see Result.v to get the rest
  of the definitions.
  Most of these constructs can be found in include/Defn.h. **)

(** The following type is represented in C as an integer, each of its figure
  (in base 10) representing a different bit of information. **)
Record funtab_eval_arg := make_funtab_eval_arg {
    funtab_eval_arg_internal : bool ; (** Whether it is stored in the array [.Internals] or directly visible. **)
    funtab_eval_arg_eval : bool (** Whether its arguments should be evaluated before calling (that is, whether it is a [BuiltinSxp] or a [SpecialSxp]). **)
  }.

Instance funtab_eval_arg_Inhab : Inhab funtab_eval_arg.
  apply Inhab_of_val. constructors; typeclass.
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
Proof. prove_comparable_trivial_inductive. Defined.

Instance PPkind_Inhab : Inhab PPkind.
  apply Inhab_of_val. constructors~.
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
Proof. prove_comparable_trivial_inductive. Defined.

Instance PPprecd_Inhab : Inhab PPprec.
  apply Inhab_of_val. constructors~.
Qed.

(** [PPinfo] **)
Record PPinfo := make_PPinfo {
    PPinfo_kind : PPkind ;
    PPinfo_precedence : PPprec ;
    PPinfo_rightassoc : bool
  }.

Instance PPinfo_Inhab : Inhab PPinfo.
  apply Inhab_of_val. constructors; typeclass.
Qed.

