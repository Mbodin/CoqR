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
From CoqR Require Import Rcore.
From CoqR.features Require Import FUtil.

Section Parameters.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition HasNames x :=
  add%stack "HasNames" in
  if%success isVector x then
    let%success att := getAttrib globals runs x R_NamesSymbol in
    let%success att_n := isNull att in
    if negb att_n then
      result_success true
    else result_success false
  else if%success isList globals x then
    do%return x := x
    while
        let%success x_n := isNull x in
        result_success (negb x_n) do
      read%list _, x_cdr, x_tag := x in
      let%success x_tag_n := isNull x_tag in
      if negb x_tag_n then
        result_rreturn true
      else result_rsuccess x_cdr using runs in
    result_success false
  else result_success false.

Definition AnswerType x (recurse usenames : bool) data (call : SEXP) :=
  add%stack "AnswerType" in
  let%success x_t := TYPEOF x in
  match x_t with
  | NilSxp =>
    result_success data
  | RawSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 0 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH x in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success data
  | LglSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 1 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH x in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success data
  | IntSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 4 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH x in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success data
  | RealSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 5 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH x in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success data
  | CplxSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 6 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH x in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success data
  | StrSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 7 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH x in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success data
  | SymSxp
  | LangSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let data :=
      BindData_with_ans_length data (1 + BindData_ans_length data) in
    result_success data
  | VecSxp
  | ExprSxp =>
    if recurse then
      let%success n := XLENGTH x in
      let%success data :=
        let%success attr := getAttrib globals runs x R_NamesSymbol in
        let%success attr_n := isNull attr in
        ifb usenames /\ BindData_ans_nnames data = 0 /\ ~ attr_n then
          result_success (BindData_with_ans_nnames data 1)
        else result_success data in
      do%let data := data
      for i from 0 to n - 1 do
        let%success x_i := VECTOR_ELT x i in
        let%success data :=
          ifb usenames /\ BindData_ans_nnames data = 0 then
            let%success hn := HasNames x_i in
            result_success (BindData_with_ans_nnames data hn)
          else result_success data in
        runs_AnswerType runs x_i recurse usenames data call
    else
      let data :=
        ifb x_t = ExprSxp then
          BindData_with_ans_flags data
            (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data))
        else
          BindData_with_ans_flags data
            (@write_nbit 10 8 ltac:(nbits_ok) true (BindData_ans_flags data)) in
      let%success len := XLENGTH x in
      let data :=
        BindData_with_ans_length data (BindData_ans_length data + len) in
      result_success data
  | ListSxp =>
    if recurse then
      fold%let data := data
      along x
      as x_car, x_tag do
        let%success data :=
          ifb usenames /\ BindData_ans_nnames data = 0 then
            let%success x_tag_n := isNull x_tag in
            if negb x_tag_n then
              result_success (BindData_with_ans_nnames data 1)
            else
              let%success hn := HasNames x_car in
              result_success (BindData_with_ans_nnames data hn)
          else result_success data in
        runs_AnswerType runs x_car recurse usenames data call using runs
    else
      let data :=
        BindData_with_ans_flags data
          (@write_nbit 10 8 ltac:(nbits_ok) true (BindData_ans_flags data)) in
      let%success len := XLENGTH x in
      let data :=
        BindData_with_ans_length data (BindData_ans_length data + len) in
      result_success data
  | _ =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let data :=
      BindData_with_ans_length data (1 + BindData_ans_length data) in
    result_success data
  end.

Definition c_Extract_opt (ans call : SEXP) :=
  add%stack "c_Extract_opt" in
  fold%success (recurse, usenames, ans, last, n_recurse, n_usenames) := (false, true, ans, NULL, 0, 0)
  along ans as a, a_, a_list do
    let n := list_tagval a_list in
    let next := list_cdrval a_list in
    let a_car := list_carval a_list in
    if%success
        ifb n <> R_NilValue then
          pmatch R_RecursiveSymbol n true
        else result_success false then
      ifb n_recurse = 1 then
        result_error "Repeated argument ‘recursive’."
      else
        let n_recurse := 1 + n_recurse in
        let%success v := asLogical globals a_car in
        let%success recurse :=
          ifb v <> NA_INTEGER then
            result_success (decide (v <> 0))
          else result_success recurse in
        let%success ans :=
          ifb last = NULL then
            result_success next
          else
            set%cdr last := next in
            result_success ans in
        result_success (recurse, usenames, ans, last, n_recurse, n_usenames)
    else if%success
        ifb n <> R_NilValue then
          pmatch R_UseNamesSymbol n true
        else result_success false then
      ifb n_usenames = 1 then
        result_error "Repeated argument ‘use.names’."
      else
        let n_usenames := 1 + n_usenames in
        let%success v := asLogical globals a_car in
        let%success usenames :=
          ifb v <> NA_INTEGER then
            result_success (decide (v <> 0))
          else result_success usenames in
        let%success ans :=
          ifb last = NULL then
            result_success next
          else
            set%cdr last := next in
            result_success ans in
        result_success (recurse, usenames, ans, last, n_recurse, n_usenames)
    else result_success (recurse, usenames, ans, a, n_recurse, n_usenames) using runs in
  result_success (ans, recurse, usenames).

Definition ListAnswer x (recurse : bool) data call :=
  add%stack "ListAnswer" in
  let LIST_ASSIGN data x :=
    run%success SET_VECTOR_ELT (BindData_ans_ptr data) (BindData_ans_length data) x in
    result_success (BindData_with_ans_length data (1 + BindData_ans_length data)) in
  let%success x_t := TYPEOF x in
  match x_t with
  | NilSxp => result_success data
  | LglSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i in
      LIST_ASSIGN data (ScalarLogical globals x_i)
  | RawSxp => result_not_implemented "Raw case."
  | IntSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer x_i := x at i in
      let%success si := ScalarInteger globals x_i in
      LIST_ASSIGN data si
  | RealSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i in
      let%success sr := ScalarReal globals x_i in
      LIST_ASSIGN data sr
  | CplxSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Complex x_i := x at i in
      let%success sc := ScalarComplex globals x_i in
      LIST_ASSIGN data sc
  | StrSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := STRING_ELT x i in
      let%success ss := ScalarString globals x_i in
      LIST_ASSIGN data ss
  | VecSxp
  | ExprSxp =>
    let%success len := XLENGTH x in
    if recurse then
      do%let data := data
      for i from 0 to len - 1 do
        let%success x_i := VECTOR_ELT x i in
        runs_ListAnswer runs x_i recurse data call
    else
      do%let data := data
      for i from 0 to len - 1 do
        let%success x_i := VECTOR_ELT x i in
        let%success x_i := lazy_duplicate x_i in
        LIST_ASSIGN data x_i
  | ListSxp =>
    if recurse then
      fold%let data := data
      along x
      as x_car, _ do
        runs_ListAnswer runs x_car recurse data call using runs
    else
      fold%let data := data
      along x
      as x_car, _ do
        let%success x_car := lazy_duplicate x_car in
        LIST_ASSIGN data x_car using runs
  | _ =>
    let%success x := lazy_duplicate x in
    LIST_ASSIGN data x
  end.

Definition StringAnswer x data call :=
  add%stack "StringAnswer" in
  let%success x_t := TYPEOF x in
  match x_t with
  | NilSxp => result_success data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_StringAnswer runs x_car data call using runs
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT x i in
      runs_StringAnswer runs x_i data call
  | _ =>
    let%success x := coerceVector globals runs x StrSxp in
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := STRING_ELT x i in
      run%success SET_STRING_ELT (BindData_ans_ptr data) (BindData_ans_length data) x_i in
      result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  end.

Definition LogicalAnswer x data call :=
  add%stack "LogicalAnswer" in
  let%success x_t := TYPEOF x in
  match x_t with
  | NilSxp => result_success data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_LogicalAnswer runs x_car data call using runs
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT x i in
      runs_LogicalAnswer runs x_i data call
  | LglSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i in
      write%Logical BindData_ans_ptr data at BindData_ans_length data := x_i in
      result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | IntSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer v := x at i in
      write%Logical BindData_ans_ptr data at BindData_ans_length data :=
        ifb v = NA_INTEGER then NA_LOGICAL else decide (v <> 0) in
      result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error "Unimplemented type."
  end.

Definition IntegerAnswer x data call :=
  add%stack "IntegerAnswer" in
  let%success x_t := TYPEOF x in
  match x_t with
  | NilSxp => result_success data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_IntegerAnswer runs x_car data call using runs
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT x i in
      runs_IntegerAnswer runs x_i data call
  | LglSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i in
      write%Integer BindData_ans_ptr data at BindData_ans_length data := x_i in
      result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | IntSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer x_i := x at i in
      write%Integer BindData_ans_ptr data at BindData_ans_length data := x_i in
      result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error "Unimplemented type."
  end.

Definition RealAnswer x data call :=
  add%stack "RealAnswer" in
  let%success x_t := TYPEOF x in
  match x_t with
  | NilSxp => result_success data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_RealAnswer runs x_car data call using runs
  | VecSxp
  | ExprSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT x i in
      runs_RealAnswer runs x_i data call
  | RealSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i in
      write%Real BindData_ans_ptr data at BindData_ans_length data := x_i in
      result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | LglSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical xi := x at i in
      ifb xi = NA_LOGICAL then
        write%Real BindData_ans_ptr data at BindData_ans_length data := NA_REAL in
        result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Real BindData_ans_ptr data at BindData_ans_length data := xi in
        result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | IntSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer xi := x at i in
      ifb xi = NA_INTEGER then
        write%Real BindData_ans_ptr data at BindData_ans_length data := NA_REAL in
        result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Real BindData_ans_ptr data at BindData_ans_length data := xi in
        result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error "Unimplemented type."
  end.

Definition ComplexAnswer x data call :=
  add%stack "ComplexAnswer" in
  let%success x_t := TYPEOF x in
  match x_t with
  | NilSxp => result_success data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_ComplexAnswer runs x_car data call using runs
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT x i in
      runs_ComplexAnswer runs x_i data call
  | RealSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i in
      write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex x_i 0 in
      result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | CplxSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Complex x_i := x at i in
      write%Complex BindData_ans_ptr data at BindData_ans_length data := x_i in
      result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | LglSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical xi := x at i in
      ifb xi = NA_LOGICAL then
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex NA_REAL NA_REAL in
        result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex xi 0 in
        result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | IntSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer xi := x at i in
      ifb xi = NA_INTEGER then
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex NA_REAL NA_REAL in
        result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex xi 0 in
        result_success (BindData_with_ans_length data (1 + BindData_ans_length data))
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error "Unimplemented type."
  end.

Definition RawAnswer x data call :=
  add%stack "RawAnswer" in
  let%success x_t := TYPEOF x in
  match x_t with
  | NilSxp => result_success data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_RawAnswer runs x_car data call using runs
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH x in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT x i in
      runs_RawAnswer runs x_i data call
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error "Unimplemented type."
  end.

Definition do_c_dftl (call op args env : SEXP) : result_SEXP :=
  add%stack "do_c_dftl" in
  let%success (ans, recurse, usenames) := c_Extract_opt args call in
  let data := make_BindData (@nat_to_nbits 10 0 ltac:(nbits_ok)) NULL 0 NULL 0 in
  fold%success data := data
  along args
  as t_car, t_tag do
    let%success data :=
      ifb usenames /\ BindData_ans_nnames data = 0 then
        let%success t_tag_n := isNull t_tag in
        if negb t_tag_n then
          result_success (BindData_with_ans_nnames data 1)
        else
          let%success hn := HasNames t_car in
          result_success (BindData_with_ans_nnames data hn)
      else result_success data in
    AnswerType t_car recurse usenames data call using runs in
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
  let%success ans := allocVector globals mode (BindData_ans_length data) in
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
            ListAnswer args_car false data call using runs
        else ListAnswer args recurse data call in
      let%success len := xlength globals runs ans in
      result_success (BindData_with_ans_length data len)
    else ifb mode = StrSxp then
      StringAnswer args data call
    else ifb mode = CplxSxp then
      ComplexAnswer args data call
    else ifb mode = RealSxp then
      RealAnswer args data call
    else ifb mode = RawSxp then
      RawAnswer args data call
    else ifb mode = LglSxp then
      LogicalAnswer args data call
    else IntegerAnswer args data call in
  let args := t in
  let%success data :=
    ifb BindData_ans_nnames data <> 0 /\ BindData_ans_length data > 0 then
      let%success data_ans_names := allocVector globals StrSxp (BindData_ans_length data) in
      let data := BindData_with_ans_names data data_ans_names in
      fold%success (nameData, data) := (tt, data)
      along args
      as args_car, _ do
        unimplemented_function "NewExtractNames" using runs in
      run%success setAttrib globals runs ans R_NamesSymbol (BindData_ans_names data) in
      result_success data
    else result_success data in
  result_success ans.

Definition do_c (call op args env : SEXP) : result_SEXP :=
  add%stack "do_c" in
  run%success Rf_checkArityCall globals runs op args call in
  let%success (disp, ans) :=
    DispatchAnyOrEval globals runs call op "c" args env true true in
  if disp then result_success ans
  else do_c_dftl call op ans env.

End Parameters.

