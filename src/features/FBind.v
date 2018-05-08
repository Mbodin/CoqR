(** Features.FBind.
  The function names of this file correspond to the function names
  in the file main/bind.c. **)

(* Copyright © 2018 Martin Bodin, Tomás Díaz

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
Require Import Ascii.
Require Import Rcore.
Require Import Util.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition HasNames S x :=
  add%stack "HasNames" in
  if%success isVector S x using S then
    let%success att := getAttrib globals runs S x R_NamesSymbol using S in
    let%success att_n := isNull S att using S in
    if negb att_n then
      result_success S true
    else result_success S false
  else if%success isList globals S x using S then
    do%return x := x
    while
        let%success x_n := isNull S x using S in
        result_success S (negb x_n) do
      read%list _, x_cdr, x_tag := x using S in
      let%success x_tag_n := isNull S x_tag using S in
      if negb x_tag_n then
        result_rreturn S true
      else result_rsuccess S x_cdr using S, runs in
    result_success S false
  else result_success S false.

Definition AnswerType S x (recurse usenames : bool) data (call : SEXP) :=
  add%stack "AnswerType" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp =>
    result_success S data
  | RawSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 0 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | LglSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 1 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | IntSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 4 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | RealSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 5 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | CplxSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 6 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | StrSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 7 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | SymSxp
  | LangSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let data :=
      BindData_with_ans_length data (1 + BindData_ans_length data) in
    result_success S data
  | VecSxp
  | ExprSxp =>
    if recurse then
      let%success n := XLENGTH S x using S in
      let%success data :=
        let%success attr := getAttrib globals runs S x R_NamesSymbol using S in
        let%success attr_n := isNull S attr using S in
        ifb usenames /\ BindData_ans_nnames data = 0 /\ ~ attr_n then
          result_success S (BindData_with_ans_nnames data 1)
        else result_success S data using S in
      do%let data := data
      for i from 0 to n - 1 do
        let%success x_i := VECTOR_ELT S x i using S in
        let%success data :=
          ifb usenames /\ BindData_ans_nnames data = 0 then
            let%success hn := HasNames S x_i using S in
            result_success S (BindData_with_ans_nnames data hn)
          else result_success S data using S in
        runs_AnswerType runs S x_i recurse usenames data call using S
    else
      let data :=
        ifb x_t = ExprSxp then
          BindData_with_ans_flags data
            (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data))
        else
          BindData_with_ans_flags data
            (@write_nbit 10 8 ltac:(nbits_ok) true (BindData_ans_flags data)) in
      let%success len := XLENGTH S x using S in
      let data :=
        BindData_with_ans_length data (BindData_ans_length data + len) in
      result_success S data
  | ListSxp =>
    if recurse then
      fold%let data := data
      along x
      as x_car, x_tag do
        let%success data :=
          ifb usenames /\ BindData_ans_nnames data = 0 then
            let%success x_tag_n := isNull S x_tag using S in
            if negb x_tag_n then
              result_success S (BindData_with_ans_nnames data 1)
            else
              let%success hn := HasNames S x_car using S in
              result_success S (BindData_with_ans_nnames data hn)
          else result_success S data using S in
        runs_AnswerType runs S x_car recurse usenames data call using S, runs, globals
    else
      let data :=
        BindData_with_ans_flags data
          (@write_nbit 10 8 ltac:(nbits_ok) true (BindData_ans_flags data)) in
      let%success len := XLENGTH S x using S in
      let data :=
        BindData_with_ans_length data (BindData_ans_length data + len) in
      result_success S data
  | _ =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let data :=
      BindData_with_ans_length data (1 + BindData_ans_length data) in
    result_success S data
  end.

Definition c_Extract_opt S (ans call : SEXP) :=
  add%stack "c_Extract_opt" in
  fold%success (recurse, usenames, ans, last, n_recurse, n_usenames) := (false, true, ans, NULL, 0, 0)
  along ans as a, a_, a_list do
    let n := list_tagval a_list in
    let next := list_cdrval a_list in
    let a_car := list_carval a_list in
    if%success
        ifb n <> R_NilValue then
          pmatch S R_RecursiveSymbol n true
        else result_success S false using S then
      ifb n_recurse = 1 then
        result_error S "Repeated argument ‘recursive’."
      else
        let n_recurse := 1 + n_recurse in
        let%success v := asLogical globals S a_car using S in
        let%success recurse :=
          ifb v <> NA_INTEGER then
            result_success S (decide (v <> 0))
          else result_success S recurse using S in
        let%success ans :=
          ifb last = NULL then
            result_success S next
          else
            set%cdr last := next using S in
            result_success S ans using S in
        result_success S (recurse, usenames, ans, last, n_recurse, n_usenames)
    else if%success
        ifb n <> R_NilValue then
          pmatch S R_UseNamesSymbol n true
        else result_success S false using S then
      ifb n_usenames = 1 then
        result_error S "Repeated argument ‘use.names’."
      else
        let n_usenames := 1 + n_usenames in
        let%success v := asLogical globals S a_car using S in
        let%success usenames :=
          ifb v <> NA_INTEGER then
            result_success S (decide (v <> 0))
          else result_success S usenames using S in
        let%success ans :=
          ifb last = NULL then
            result_success S next
          else
            set%cdr last := next using S in
            result_success S ans using S in
        result_success S (recurse, usenames, ans, last, n_recurse, n_usenames)
    else result_success S (recurse, usenames, ans, a, n_recurse, n_usenames) using S, runs, globals in
  result_success S (ans, recurse, usenames).

Definition ListAnswer S x (recurse : bool) data call :=
  add%stack "ListAnswer" in
  let LIST_ASSIGN S data x :=
    run%success SET_VECTOR_ELT S (BindData_ans_ptr data) (BindData_ans_length data) x using S in
    result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i using S in
      LIST_ASSIGN S data (ScalarLogical globals x_i) using S
  | RawSxp => result_not_implemented "Raw case."
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer x_i := x at i using S in
      let (S, si) := ScalarInteger globals S x_i in
      LIST_ASSIGN S data si using S
  | RealSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i using S in
      let (S, sr) := ScalarReal globals S x_i in
      LIST_ASSIGN S data sr using S
  | CplxSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Complex x_i := x at i using S in
      let (S, sc) := ScalarComplex globals S x_i in
      LIST_ASSIGN S data sc using S
  | StrSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := STRING_ELT S x i using S in
      let%success ss := ScalarString globals S x_i using S in
      LIST_ASSIGN S data ss using S
  | VecSxp
  | ExprSxp =>
    let%success len := XLENGTH S x using S in
    if recurse then
      do%let data := data
      for i from 0 to len - 1 do
        let%success x_i := VECTOR_ELT S x i using S in
        runs_ListAnswer runs S x_i recurse data call using S
    else
      do%let data := data
      for i from 0 to len - 1 do
        let%success x_i := VECTOR_ELT S x i using S in
        let%success x_i := lazy_duplicate S x_i using S in
        LIST_ASSIGN S data x_i using S
  | ListSxp =>
    if recurse then
      fold%let data := data
      along x
      as x_car, _ do
        runs_ListAnswer runs S x_car recurse data call using S, runs, globals
    else
      fold%let data := data
      along x
      as x_car, _ do
        let%success x_car := lazy_duplicate S x_car using S in
        LIST_ASSIGN S data x_car using S, runs, globals
  | _ =>
    let%success x := lazy_duplicate S x using S in
    LIST_ASSIGN S data x
  end.

Definition StringAnswer S x data call :=
  add%stack "StringAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_StringAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_StringAnswer runs S x_i data call using S
  | _ =>
    let%success x := coerceVector globals runs S x StrSxp using S in
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := STRING_ELT S x i using S in
      run%success SET_STRING_ELT S (BindData_ans_ptr data) (BindData_ans_length data) x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  end.

Definition LogicalAnswer S x data call :=
  add%stack "LogicalAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_LogicalAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_LogicalAnswer runs S x_i data call using S
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i using S in
      write%Logical BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer v := x at i using S in
      write%Logical BindData_ans_ptr data at BindData_ans_length data :=
        ifb v = NA_INTEGER then NA_LOGICAL else decide (v <> 0) using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition IntegerAnswer S x data call :=
  add%stack "IntegerAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_IntegerAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_IntegerAnswer runs S x_i data call using S
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i using S in
      write%Integer BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer x_i := x at i using S in
      write%Integer BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition RealAnswer S x data call :=
  add%stack "RealAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_RealAnswer runs S x_car data call using S, runs, globals
  | VecSxp
  | ExprSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_RealAnswer runs S x_i data call using S
  | RealSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i using S in
      write%Real BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical xi := x at i using S in
      ifb xi = NA_LOGICAL then
        write%Real BindData_ans_ptr data at BindData_ans_length data := NA_REAL using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Real BindData_ans_ptr data at BindData_ans_length data := xi using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer xi := x at i using S in
      ifb xi = NA_INTEGER then
        write%Real BindData_ans_ptr data at BindData_ans_length data := NA_REAL using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Real BindData_ans_ptr data at BindData_ans_length data := xi using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition ComplexAnswer S x data call :=
  add%stack "ComplexAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_ComplexAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_ComplexAnswer runs S x_i data call using S
  | RealSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i using S in
      write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex x_i 0 using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | CplxSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Complex x_i := x at i using S in
      write%Complex BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical xi := x at i using S in
      ifb xi = NA_LOGICAL then
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex NA_REAL NA_REAL using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex xi 0 using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer xi := x at i using S in
      ifb xi = NA_INTEGER then
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex NA_REAL NA_REAL using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex xi 0 using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition RawAnswer S x data call :=
  add%stack "RawAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_RawAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_RawAnswer runs S x_i data call using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition do_c_dftl S (call op args env : SEXP) : result SEXP :=
  add%stack "do_c_dftl" in
  let%success (ans, recurse, usenames) := c_Extract_opt S args call using S in
  let data := make_BindData (@nat_to_nbits 10 0 ltac:(nbits_ok)) NULL 0 NULL 0 in
  fold%success data := data
  along args
  as t_car, t_tag do
    let%success data :=
      ifb usenames /\ BindData_ans_nnames data = 0 then
        let%success t_tag_n := isNull S t_tag using S in
        if negb t_tag_n then
          result_success S (BindData_with_ans_nnames data 1)
        else
          let%success hn := HasNames S t_car using S in
          result_success S (BindData_with_ans_nnames data hn)
      else result_success S data using S in
    AnswerType S t_car recurse usenames data call using S, runs, globals in
  let mode :=
    if nth_bit 9 (BindData_ans_flags data) ltac:(nbits_ok) then ExprSxp
    else if nth_bit 8 (BindData_ans_flags data) ltac:(nbits_ok) then VecSxp
    else if nth_bit 7 (BindData_ans_flags data) ltac:(nbits_ok) then StrSxp
    else if nth_bit 6 (BindData_ans_flags data) ltac:(nbits_ok) then CplxSxp
    else if nth_bit 5 (BindData_ans_flags data) ltac:(nbits_ok) then RealSxp
    else if nth_bit 4 (BindData_ans_flags data) ltac:(nbits_ok) then IntSxp
    else if nth_bit 1 (BindData_ans_flags data) ltac:(nbits_ok) then LglSxp
    else if nth_bit 0 (BindData_ans_flags data) ltac:(nbits_ok) then RawSxp
    else NilSxp in
  let%success ans := allocVector globals S mode (BindData_ans_length data) using S in
  let data := BindData_with_ans_ptr data ans in
  let data := BindData_with_ans_length data 0 in
  let t := args in
  let%success data :=
    ifb mode = VecSxp \/ mode = ExprSxp then
      let%success data :=
        if negb recurse then
          fold%let data := data
          along args
          as args_car, _ do
            ListAnswer S args_car false data call using S, runs, globals
        else ListAnswer S args recurse data call using S in
      let%success len := xlength globals runs S ans using S in
      result_success S (BindData_with_ans_length data len)
    else ifb mode = StrSxp then
      StringAnswer S args data call
    else ifb mode = CplxSxp then
      ComplexAnswer S args data call
    else ifb mode = RealSxp then
      RealAnswer S args data call
    else ifb mode = RawSxp then
      RawAnswer S args data call
    else ifb mode = LglSxp then
      LogicalAnswer S args data call
    else IntegerAnswer S args data call using S in
  let args := t in
  let%success data :=
    ifb BindData_ans_nnames data <> 0 /\ BindData_ans_length data > 0 then
      let%success data_ans_names := allocVector globals S StrSxp (BindData_ans_length data) using S in
      let data := BindData_with_ans_names data data_ans_names in
      fold%success (nameData, data) := (tt, data)
      along args
      as args_car, _ do
        unimplemented_function "NewExtractNames" using S, runs, globals in
      run%success setAttrib globals runs S ans R_NamesSymbol (BindData_ans_names data) using S in
      result_success S data
    else result_success S data using S in
  result_success S ans.

Definition do_c S (call op args env : SEXP) : result SEXP :=
  add%stack "do_c" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  let%success (disp, ans) :=
    DispatchAnyOrEval globals runs S call op "c" args env true true using S in
  if disp then result_success S ans
  else do_c_dftl S call op ans env.

End Parameters.

