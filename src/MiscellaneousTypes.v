(** MiscellaneousTypes.
  This file describes various internal data types used in the source of R.
  In contrary to [InternalTypes], the types described here are fairly independent. **)

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

Require Export Rinternals Common.

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
