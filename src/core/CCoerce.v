(** Core.CCoerce.
  The function names in this file correspond to the function names
  in the file main/coerce.c. **)

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
Require Import Ascii.
Require Import Double.
Require Import Loops.
Require Import Conflicts.
Require Import CRmath.
Require Import CRinternals.
Require Import CMemory.
Require Import CRinlinedfuns.
Require Import CDuplicate.
Require Import CArithmetic.
Require Import CPrintutils.
Require Import CSysutils.
Require Import CUtil.
Require Import CEnvir.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

(** The following two functions are actually from main/attrib.c. It has been
  placed here to solve a circular file dependency. **)

Definition installAttrib vec name val :=
  add%stack "installAttrib" in
  let%success vec_type := TYPEOF vec in
  ifb vec_type = CharSxp then
    result_error "Cannot set attribute on a CharSxp."
  else ifb vec_type = SymSxp then
    result_error "Cannot set attribute on a symbol."
  else
    let%success vec_attr := ATTRIB vec in
    fold%return t := R_NilValue : SEXP
    along vec_attr
    as s, _, s_list do
      ifb list_tagval s_list = name then
        set%car s := val in
        result_rreturn val
      else result_rsuccess s using runs in
    let%success s := CONS globals val R_NilValue in
    set%tag s := name in
    run%success
      ifb vec_attr = R_NilValue then
        run%success SET_ATTRIB vec s in
        result_skip
      else
        set%cdr t := s in
        result_skip in
    result_success val.

Definition copyMostAttrib (inp ans : SEXP) :=
  add%stack "copyMostAttrib" in
  ifb ans = R_NilValue then
    result_error "Attempt to set an attribute on NULL."
  else
    let%success inp_attr := ATTRIB inp in
    fold%success
    along inp_attr
    as s_car, s_tag do
      ifb s_tag <> R_NamesSymbol
          /\ s_tag <> R_DimSymbol
          /\ s_tag <> R_DimNamesSymbol then
        run%success installAttrib ans s_tag s_car in
        result_skip
      else result_skip using runs in
    if%success OBJECT inp then
      SET_OBJECT ans true in
    if%success IS_S4_OBJECT inp then
      SET_S4_OBJECT ans
    else UNSET_S4_OBJECT ans.


Definition LogicalFromString (x : SEXP) :=
  add%stack "LogicalFromString" in
  ifb x <> R_NaString then
    let%success c := CHAR x in
    if StringTrue c then result_success (1 : int)
    else if StringFalse c then result_success (0 : int)
    else result_success NA_LOGICAL
  else result_success NA_LOGICAL.

Definition LogicalFromInteger (x : int) : result int :=
  add%stack "LogicalFromInteger" in
  ifb x = NA_INTEGER then result_success NA_LOGICAL
  else result_success (decide (x <> 0) : int).

Definition LogicalFromReal x : result int :=
  add%stack "LogicalFromReal" in
  ifb ISNAN x then result_success NA_LOGICAL
  else result_success (negb (Double.is_zero x) : int).

Definition LogicalFromComplex x : result int :=
  add%stack "LogicalFromComplex" in
  ifb ISNAN (Rcomplex_r x) \/ ISNAN (Rcomplex_i x) then result_success NA_LOGICAL
  else result_success (decide (~ Double.is_zero (Rcomplex_r x)
                                 \/ ~ Double.is_zero (Rcomplex_i x)) : int).

Definition asLogical x :=
  add%stack "asLogical" in
  if%success isVectorAtomic x then
    let%success len := XLENGTH x in
    ifb len < 1 then
      result_success NA_LOGICAL
    else
      let%success x_type := TYPEOF x in
      match x_type with
      | LglSxp => LOGICAL_ELT x 0
      | IntSxp =>
        let%success i := INTEGER_ELT x 0 in
        LogicalFromInteger i
      | RealSxp =>
        let%success r := REAL_ELT x 0 in
        LogicalFromReal r
      | CplxSxp =>
        let%success c := COMPLEX_ELT x 0 in
        LogicalFromComplex c
      | StrSxp =>
        let%success s := STRING_ELT x 0 in
        LogicalFromString s
      | RawSxp =>
        let%success s := RAW_ELT x 0 in
        LogicalFromString s
      | _ => result_error "Unimplemented type."
      end
  else
    let%success x_type := TYPEOF x in
    ifb x_type = CharSxp then
      LogicalFromString x
    else result_success NA_LOGICAL.

Definition IntegerFromString (x : SEXP) :=
  add%stack "IntegerFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR x in
      result_success (negb (isBlankString c))
    else result_success false then
    unimplemented_function "R_strtod."
  else result_success NA_INTEGER.

Definition IntegerFromLogical x :=
  ifb x = NA_LOGICAL then
    NA_INTEGER
  else x.

Definition IntegerFromReal x :=
  if ISNAN x then
    NA_INTEGER
  else ifb x >= Double.add (int_to_double (INT_MAX)) (1 : double) \/ x <= (INT_MIN : double) then
    (* A warning has been formalised out here. *)
    NA_INTEGER
  else Double.double_to_int_zero x.

Definition IntegerFromComplex x :=
  ifb ISNAN (Rcomplex_r x) \/ ISNAN (Rcomplex_i x) then
    NA_INTEGER
  else ifb (Rcomplex_r x) >= Double.add (int_to_double (INT_MAX)) (1 : double) \/ (Rcomplex_r x) <= (INT_MIN : double) then
    (* A warning has been formalised out here. *)
    NA_INTEGER
  else Double.double_to_int_zero (Rcomplex_r x).

Definition asInteger x :=
  add%stack "asInteger" in
  let%success t := TYPEOF x in
  if%success
      if%success isVectorAtomic x then
        let%success l := XLENGTH x in
        result_success (decide (l >= 1))
      else result_success false then
    match t with
    | LglSxp =>
      read%Logical x0 := x at 0 in
      result_success (IntegerFromLogical x0)
    | IntSxp =>
      read%Integer x0 := x at 0 in
      result_success x0
    | RealSxp =>
      read%Real x0 := x at 0 in
      result_success (IntegerFromReal x0)
    | CplxSxp =>
      read%Complex x0 := x at 0 in
      result_success (IntegerFromComplex x0)
    | StrSxp =>
      read%Pointer x0 := x at 0 in
      IntegerFromString x0
    | _ => result_error "Unimplemented type."
    end
  else ifb t = CharSxp then
    IntegerFromString x
  else result_success NA_INTEGER.

Definition RealFromLogical x :=
  ifb x = NA_LOGICAL then
    NA_REAL
  else (x : double).

Definition RealFromInteger x :=
  ifb x = NA_INTEGER then
    NA_REAL
  else (x : double).

Definition RealFromComplex x :=
  ifb ISNAN (Rcomplex_r x) \/ ISNAN (Rcomplex_i x) then
    NA_REAL
  else if ISNAN (Rcomplex_r x) then
    Rcomplex_r x
  else if ISNAN (Rcomplex_i x) then
    NA_REAL
  else Rcomplex_r x.

Definition RealFromString (x : SEXP) :=
  add%stack "RealFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR x in
      result_success (negb (isBlankString c))
    else result_success false then
    unimplemented_function "R_strtod."
  else result_success NA_REAL.

Definition asReal x :=
  add%stack "asReal" in
  let%success t := TYPEOF x in
  if%success
      if%success isVectorAtomic x then
        let%success l := XLENGTH x in
        result_success (decide (l >= 1))
      else result_success false then
    match t with
    | LglSxp =>
      read%Logical x0 := x at 0 in
      result_success (RealFromLogical x0)
    | IntSxp =>
      read%Integer x0 := x at 0 in
      result_success (RealFromInteger x0)
    | RealSxp =>
      read%Real x0 := x at 0 in
      result_success x0
    | CplxSxp =>
      read%Complex x0 := x at 0 in
      result_success (RealFromComplex x0)
    | StrSxp =>
      read%Pointer x0 := x at 0 in
      RealFromString x0
    | _ => result_error "Unimplemented type."
    end
  else ifb t = CharSxp then
    RealFromString x
  else result_success NA_REAL.

Definition coerceSymbol v type :=
  add%stack "coerceSymbol" in
  let%success rval :=
    ifb type = ExprSxp then
      let%success rval := allocVector globals type 1 in
      run%success SET_VECTOR_ELT rval 0 v in
      result_success rval
    else ifb type = CharSxp then
      PRINTNAME v
    else ifb type = StrSxp then
      let%success v_name := PRINTNAME v in
      ScalarString globals v_name
    else
      (* A warning has been formalised out here. *)
      result_success (R_NilValue : SEXP) in
  result_success rval.

Definition PairToVectorList (x : SEXP) : result SEXP :=
  unimplemented_function "PairToVectorList".

Definition VectorToPairList (x : SEXP) : result SEXP :=
  add%stack "VectorToPairList" in
  let%success len := R_length globals runs x in

  let%success xnew := allocList globals len in
  let%success xnames := runs_getAttrib runs x R_NamesSymbol in
  let named := decide (xnames <> R_NilValue) in

  do%success xptr := xnew
  for i from 0 to len - 1 do

    let%success x_i := VECTOR_ELT x i in
    let%success x_named := NAMED x in
    run%success RAISE_NAMED x_i x_named in

    set%car xptr := x_i in

    let%success xnames_i := STRING_ELT xnames i in
    let%success xnames_i_char := CHAR xnames_i in
    let xnames_i_char_0 := LibOption.unsome_default "000"%char (String.get 0 xnames_i_char) in
    ifb named /\  xnames_i_char_0 <> "000"%char then
      let%success xnames_i_install := installTrChar globals runs xnames_i in
      set%tag xptr := xnames_i_install in
      read%list _, xptr_cdr, _ := xptr in
      result_success xptr_cdr
    else
      read%list _, xptr_cdr, _ := xptr in
      result_success xptr_cdr
  in
  ifb len > 0 then
    run%success copyMostAttrib x xnew in
    result_success xnew
  else
    result_success xnew.

Definition ComplexFromString (x : SEXP) :=
  add%stack "ComplexFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR x in
      result_success (negb (isBlankString c))
    else result_success false then
    unimplemented_function "R_strtod."
  else result_success (make_Rcomplex NA_REAL NA_REAL).

Definition ComplexFromLogical x :=
  ifb x = NA_LOGICAL then
    make_Rcomplex NA_REAL NA_REAL
  else make_Rcomplex x 0.

Definition ComplexFromInteger x :=
  ifb x = NA_INTEGER then
    make_Rcomplex NA_REAL NA_REAL
  else make_Rcomplex x 0.

Definition ComplexFromReal x :=
  make_Rcomplex x 0.

Definition asComplex x :=
  add%stack "asComplex" in
  let%success x_va := isVectorAtomic x in
  let%success x_len := XLENGTH x in
  let%success x_type := TYPEOF x in
  ifb x_va /\ x_len >= 1 then
    match x_type with
    | LglSxp =>
      let%success x_0 := LOGICAL_ELT x 0 in
      result_success (ComplexFromLogical x_0)
    | IntSxp =>
      let%success x_0 := INTEGER_ELT x 0 in
      result_success (ComplexFromInteger x_0)
    | RealSxp =>
      let%success x_0 := REAL_ELT x 0 in
      result_success (ComplexFromReal x_0)
    | CplxSxp =>
      COMPLEX_ELT x 0
    | StrSxp =>
      let%success x_0 := STRING_ELT x 0 in
      ComplexFromString x_0
    | _ =>
      result_error "Unimplemented type."
    end
  else ifb x_type = CharSxp then
    ComplexFromString x
  else result_success (make_Rcomplex NA_REAL NA_REAL).

Definition coercePairList v type :=
  add%stack "coercePairList" in
  let%exit (rval, n) :=
    ifb type = ListSxp then
      result_rreturn v
    else ifb type = ExprSxp then
      let%success rval := allocVector globals type 1 in
      run%success SET_VECTOR_ELT rval 0 v in
      result_rreturn rval
    else ifb type = StrSxp then
      let%success n := R_length globals runs v in
      let%success rval := allocVector globals type n in
      fold%success i := 0
      along v
      as v_car, _ do
        let%success v_car_is := isString v_car in
        let%success v_car_len := R_length globals runs v_car in
        run%success
          ifb v_car_is /\ v_car_len = 1 then
            let%success v_car_0 := STRING_ELT v_car 0 in
            SET_STRING_ELT rval i v_car_0
          else unimplemented_function "deparse1line" in
        result_success (1 + i) using runs in
      result_rsuccess (rval, n)
    else ifb type = VecSxp then
      let%success rval := PairToVectorList v in
      result_rreturn rval
    else if%success isVectorizable globals runs v then
      let%success n := R_length globals runs v in
      let%success rval := allocVector globals type n in
      run%success
        match type with
        | LglSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp in
            let%success vp_car_lgl := asLogical vp_car in
            write%Logical rval at i := vp_car_lgl in
            result_success vp_cdr
        | IntSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp in
            let%success vp_car_lgl := asInteger vp_car in
            write%Integer rval at i := vp_car_lgl in
            result_success vp_cdr
        | RealSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp in
            let%success vp_car_lgl := asReal vp_car in
            write%Real rval at i := vp_car_lgl in
            result_success vp_cdr
        | CplxSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp in
            let%success vp_car_lgl := asComplex vp_car in
            write%Complex rval at i := vp_car_lgl in
            result_success vp_cdr
        | RawSxp => result_not_implemented "Raw case."
        | _ => result_error "Unimplemented type."
        end in
      result_rsuccess (rval, n)
    else result_error "‘pairlist’ object cannot be coerce as-is." in
  fold%success i := false
  along v
  as _, v_tag do
    ifb v_tag <> R_NilValue then
      result_success true
    else result_success i using runs in
  run%success
    if i then
      let%success names := allocVector globals StrSxp n in
      fold%success i := 0
      along v
      as _, v_tag do
        run%success
          ifb v_tag <> R_NilValue then
            let%success v_tag_name := PRINTNAME v_tag in
            SET_STRING_ELT names i v_tag_name
          else result_skip in
        result_success (1 + i) using runs in
      result_skip
    else result_skip in
  result_success rval.

Definition coerceVectorList (v : SEXP) (type : SExpType) : result SEXP :=
  unimplemented_function "coerceVectorList".

Definition StringFromLogical x :=
  add%stack "StringFromLogical" in
  ifb x = NA_LOGICAL then
    result_success (NA_STRING : SEXP)
  else
    let%success r := mkChar globals (EncodeLogical x) in
    result_success r.

Definition StringFromInteger x :=
  add%stack "StringFromInteger" in
  ifb x = NA_INTEGER then
    result_success (NA_STRING : SEXP)
  else unimplemented_function "formatInteger".

Definition StringFromComplex x :=
  add%stack "StringFromComplex" in
  ifb R_IsNA (Rcomplex_r x) \/ R_IsNA (Rcomplex_i x) then
    result_success (NA_STRING : SEXP)
  else unimplemented_function "EncodeComplex".

Definition coerceToSymbol v :=
  add%stack "coerceToSymbol" in
  let%success v_len := R_length globals runs v in
  ifb v_len <= 0 then
    result_error "Invalid data."
  else
    let%success v_type := TYPEOF v in
    let%success ans :=
      match v_type with
      | LglSxp =>
        let%success v_0 := LOGICAL_ELT v 0 in
        StringFromLogical v_0
      | IntSxp =>
        let%success v_0 := INTEGER_ELT v 0 in
        StringFromInteger v_0
      | RealSxp =>
        let%success v_0 := REAL_ELT v 0 in
        StringFromReal globals v_0
      | CplxSxp =>
        let%success v_0 := COMPLEX_ELT v 0 in
        StringFromComplex v_0
      | StrSxp =>
        STRING_ELT v 0
      | RawSxp => result_not_implemented "Raw case."
      | _ => result_error "Unimplemented type."
      end in
    installTrChar globals runs ans.

Definition coerceToLogical v :=
  add%stack "coerceToLogical" in
  let%success n := XLENGTH v in
  let%success ans := allocVector globals LglSxp n in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs ans v in
  let%success v_type := TYPEOF v in
  run%success
    match v_type with
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT v i in
        let%success pa_i := LogicalFromInteger v_i in
        write%Logical ans at i := pa_i in
        result_skip
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT v i in
        let%success pa_i := LogicalFromReal v_i in
        write%Logical ans at i := pa_i in
        result_skip
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT v i in
        let%success pa_i := LogicalFromComplex v_i in
        write%Logical ans at i := pa_i in
        result_skip
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT v i in
        let%success pa_i := LogicalFromString v_i in
        write%Logical ans at i := pa_i in
        result_skip
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error "Unimplemented type."
    end in
  result_success ans.

Definition coerceToInteger v :=
  add%stack "coerceToInteger" in
  let%success n := XLENGTH v in
  let%success ans := allocVector globals IntSxp n in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs ans v in
  let%success v_type := TYPEOF v in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT v i in
        write%Integer ans at i := IntegerFromLogical v_i in
        result_skip
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT v i in
        write%Integer ans at i := IntegerFromReal v_i in
        result_skip
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT v i in
        write%Integer ans at i := IntegerFromComplex v_i in
        result_skip
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT v i in
        let%success pa_i := IntegerFromString v_i in
        write%Integer ans at i := pa_i in
        result_skip
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error "Unimplemented type."
    end in
  result_success ans.

Definition coerceToReal v :=
  add%stack "coerceToReal" in
  let%success n := XLENGTH v in
  let%success ans := allocVector globals RealSxp n in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs ans v in
  let%success v_type := TYPEOF v in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT v i in
        write%Real ans at i := RealFromLogical v_i in
        result_skip
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT v i in
        write%Real ans at i := RealFromInteger v_i in
        result_skip
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT v i in
        write%Real ans at i := RealFromComplex v_i in
        result_skip
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT v i in
        let%success pa_i := RealFromString v_i in
        write%Real ans at i := pa_i in
        result_skip
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error "Unimplemented type."
    end in
  result_success ans.

Definition coerceToComplex v :=
  add%stack "coerceToComplex" in
  let%success n := XLENGTH v in
  let%success ans := allocVector globals CplxSxp n in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs ans v in
  let%success v_type := TYPEOF v in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT v i in
        write%Complex ans at i := ComplexFromLogical v_i in
        result_skip
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT v i in
        write%Complex ans at i := ComplexFromInteger v_i in
        result_skip
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT v i in
        write%Complex ans at i := ComplexFromReal v_i in
        result_skip
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT v i in
        let%success pa_i := ComplexFromString v_i in
        write%Complex ans at i := pa_i in
        result_skip
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error "Unimplemented type."
    end in
  result_success ans.

Definition coerceToRaw (v : SEXP) : result SEXP :=
  unimplemented_function "coerceToRaw".

Definition coerceToString v :=
  add%stack "coerceToString" in
  let%success n := XLENGTH v in
  let%success ans := allocVector globals StrSxp n in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs ans v in
  let%success v_type := TYPEOF v in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT v i in
        let%success s_i := StringFromLogical v_i in
        SET_STRING_ELT ans i s_i
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT v i in
        let%success s_i := StringFromInteger v_i in
        SET_STRING_ELT ans i s_i
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT v i in
        let%success s_i := StringFromReal globals v_i in
        SET_STRING_ELT ans i s_i
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT v i in
        let%success s_i := StringFromComplex v_i in
        SET_STRING_ELT ans i s_i
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error "Unimplemented type."
    end in
  result_success ans.

Definition coerceToExpression v :=
  add%stack "coerceToExpression" in
  let%success ans :=
    if%success isVectorAtomic v then
      let%success n := XLENGTH v in
      let%success ans := allocVector globals ExprSxp n in
      let%success v_type := TYPEOF v in
      run%success
        match v_type with
        | LglSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := LOGICAL_ELT v i in
            run%success SET_VECTOR_ELT ans i (ScalarLogical globals v_i) in
            result_skip
        | IntSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := INTEGER_ELT v i in
            let%success s_i := ScalarInteger globals v_i in
            run%success SET_VECTOR_ELT ans i s_i in
            result_skip
        | RealSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := REAL_ELT v i in
            let%success s_i := ScalarReal globals v_i in
            run%success SET_VECTOR_ELT ans i s_i in
            result_skip
        | CplxSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := COMPLEX_ELT v i in
            let%success s_i := ScalarComplex globals v_i in
            run%success SET_VECTOR_ELT ans i s_i in
            result_skip
        | StrSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := STRING_ELT v i in
            let%success s_i := ScalarString globals v_i in
            run%success SET_VECTOR_ELT ans i s_i in
            result_skip
        | RawSxp => result_not_implemented "Raw case."
        | _ =>
          result_error "Unimplemented type."
        end in
      result_success ans
    else
      let%success ans := allocVector globals ExprSxp 1 in
      let%success v_d := duplicate globals runs v in
      run%success SET_VECTOR_ELT ans 0 v_d in
      result_success ans in
  result_success ans.

Definition coerceToVectorList v :=
  add%stack "coerceToVectorList" in
  let%success n := xlength globals runs v in
  let%success ans := allocVector globals VecSxp n in
  let%success v_type := TYPEOF v in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT v i in
        run%success SET_VECTOR_ELT ans i (ScalarLogical globals v_i) in
        result_skip
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT v i in
        let%success s_i := ScalarInteger globals v_i in
        run%success SET_VECTOR_ELT ans i s_i in
        result_skip
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT v i in
        let%success s_i := ScalarReal globals v_i in
        run%success SET_VECTOR_ELT ans i s_i in
        result_skip
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT v i in
        let%success s_i := ScalarComplex globals v_i in
        run%success SET_VECTOR_ELT ans i s_i in
        result_skip
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT v i in
        let%success s_i := ScalarString globals v_i in
        run%success SET_VECTOR_ELT ans i s_i in
        result_skip
    | RawSxp => result_not_implemented "Raw case."
    | ListSxp
    | LangSxp =>
      do%success tmp := v
      for i from 0 to n - 1 do
        read%list tmp_car, tmp_cdr, _ := tmp in
        run%success SET_VECTOR_ELT ans i tmp_car in
        result_success tmp_cdr in
      result_skip
    | _ =>
      result_error "Unimplemented type."
    end in
  let%success tmp := runs_getAttrib runs v R_NamesSymbol in
  run%success
    ifb tmp <> R_NilValue then
      run%success runs_setAttrib runs ans R_NamesSymbol tmp in
      result_skip
    else result_skip in
  result_success ans.

Definition coerceToPairList v :=
  add%stack "coerceToPairList" in
  let%success n := LENGTH globals v in
  let%success ans := allocList globals n in
  do%success ansp := ans
  for i from 0 to n - 1 do
    read%list _, ansp_cdr, _ := ansp in
    run%success
      let%success v_type := TYPEOF v in
      match v_type with
      | LglSxp =>
        let%success ansp_car := allocVector globals LglSxp 1 in
        set%car ansp := ansp_car in
        let%success v_i := LOGICAL_ELT v i in
        write%Logical ansp_car at 0 := v_i in
        result_skip
      | IntSxp =>
        let%success ansp_car := allocVector globals IntSxp 1 in
        set%car ansp := ansp_car in
        let%success v_i := INTEGER_ELT v i in
        write%Integer ansp_car at 0 := v_i in
        result_skip
      | RealSxp =>
        let%success ansp_car := allocVector globals RealSxp 1 in
        set%car ansp := ansp_car in
        let%success v_i := REAL_ELT v i in
        write%Real ansp_car at 0 := v_i in
        result_skip
      | CplxSxp =>
        let%success ansp_car := allocVector globals CplxSxp 1 in
        set%car ansp := ansp_car in
        let%success v_i := COMPLEX_ELT v i in
        write%Complex ansp_car at 0 := v_i in
        result_skip
      | StrSxp =>
        let%success v_i := STRING_ELT v i in
        let%success ansp_car := ScalarString globals v_i in
        set%car ansp := ansp_car in
        result_skip
      | RawSxp => result_not_implemented "Raw case."
      | VecSxp =>
        let%success v_i := VECTOR_ELT v i in
        set%car ansp := v_i in
        result_skip
      | ExprSxp =>
        let%success v_i := VECTOR_ELT v i in
        set%car ansp := v_i in
        result_skip
      | _ =>
        result_error "Unimplemented type."
      end in
    result_success ansp_cdr in
  let%success ansp := runs_getAttrib runs v R_NamesSymbol in
  run%success
    ifb ansp <> R_NilValue then
      run%success runs_setAttrib runs ans R_NamesSymbol ansp in
      result_skip
    else result_skip in
  result_success ans.

Definition coerceVector v type :=
  add%stack "coerceVector" in
  let%success v_type := TYPEOF v in
  ifb v_type = type then
    result_success v
  else
    let%success v_s4 := IS_S4_OBJECT v in
    let%exit v :=
      ifb v_s4 /\ v_type = S4Sxp then
        unimplemented_function "R_getS4DataSlot"
      else result_rsuccess v in
    let%success ans :=
      let%success v_type := TYPEOF v in
      match v_type with
      | SymSxp =>
        coerceSymbol v type
      | NilSxp
      | ListSxp =>
        coercePairList v type
      | LangSxp =>
        ifb type <> StrSxp then
          coercePairList v type
        else
          let%success n := R_length globals runs v in
          let%success ans := allocVector globals type n in
          ifb n = 0 then
            result_success ans
          else
            read%list v_car, v_cdr, _ := v in
            let op := v_car in
            let%success op_type := TYPEOF op in
            let%success (i, v) :=
              ifb op_type = SymSxp then
                let%success op_name := PRINTNAME op in
                run%success SET_STRING_ELT ans 0 op_name in
                result_success (1, v_cdr)
              else result_success (0, v) in
            fold%success i := i
            along v
            as v_car, _ do
              let%success v_car_is := isString v_car in
              let%success v_car_len := R_length globals runs v_car in
              run%success
                ifb v_car_is /\ v_car_len = 1 then
                  let%success v_car_0 := STRING_ELT v_car 0 in
                  SET_STRING_ELT ans i v_car_0
                else unimplemented_function "deparse1line" in
              result_success (1 + i) using runs in
            result_success ans
      | VecSxp
      | ExprSxp =>
        coerceVectorList v type
      | EnvSxp =>
        result_error "Environments can not be coerced."
      | LglSxp
      | IntSxp
      | RealSxp
      | CplxSxp
      | StrSxp
      | RawSxp =>
        match type with
        | SymSxp => coerceToSymbol v
        | LglSxp => coerceToLogical v
        | IntSxp => coerceToInteger v
        | RealSxp => coerceToReal v
        | CplxSxp => coerceToComplex v
        | RawSxp => coerceToRaw v
        | StrSxp => coerceToString v
        | ExprSxp => coerceToExpression v
        | VecSxp => coerceToVectorList v
        | ListSxp => coerceToPairList v
        | _ =>
          result_error "Cannot coerce to this type."
        end
      | _ =>
        result_error "Cannot coerce this type to this other type."
      end in
    result_success ans.

Definition CreateTag x :=
  add%stack "CreateTag" in
  let%success x_n := isNull x in
  let%success x_sy := isSymbol x in
  ifb x_n \/ x_sy then
    result_success x
  else
    if%success
        let%success x_st := isString x in
        let%success x_len := R_length globals runs x in
        ifb x_st /\ x_len >= 1 then
          let%success x_0 := STRING_ELT x 0 in
          let%success x_0_len := R_length globals runs x_0 in
          result_success (decide (x_0_len >= 1))
        else result_success false then
      let%success x_0 := STRING_ELT x 0 in
      installTrChar globals runs x_0
    else unimplemented_function "deparse1".

Definition copyDimAndNames x ans :=
  add%stack "copyDimAndNames" in
  if%success isVector x then
    let%success dims := runs_getAttrib runs x R_DimSymbol in
    run%success
      ifb dims <> R_NilValue then
        run%success runs_setAttrib runs ans R_DimSymbol dims in
        result_skip
      else result_skip in
    if%success isArray globals runs x then
      let%success names := runs_getAttrib runs x R_DimNamesSymbol in
      ifb names <> R_NilValue then
        run%success runs_setAttrib runs ans R_DimNamesSymbol names in
        result_skip
      else result_skip
    else
      let%success names := runs_getAttrib runs x R_NamesSymbol in
      ifb names <> R_NilValue then
        run%success runs_setAttrib runs ans R_NamesSymbol names in
        result_skip
      else result_skip
  else result_skip.


Definition substitute (lang rho : SEXP) : result SEXP :=
  add%stack "substitute" in
  let%success lang_type := TYPEOF lang in
  match lang_type with
  | PromSxp => let%success lang_prexpr := PREXPR globals lang in
               runs_substitute runs lang_prexpr rho
  | SymSxp => ifb rho <> R_NilValue then
                let%success t := findVarInFrame3 globals runs rho lang true in
                ifb t <> R_UnboundValue then
                  let%success t_type := TYPEOF t in

                  ifb t_type = PromSxp then
                    let%success t_prexpr := PREXPR globals t in
                    do%success t := t_prexpr
                    while let%success t_type := TYPEOF t in
                      result_success (decide (t_type = PromSxp)) do PREXPR globals t
                    using runs in
                    (** make sure code will not be modified: **)
                    set%named t := named_plural in
                    result_success t
                  else ifb t_type = DotSxp then
                    result_error "'...' used in an incorrect context"
                  else ifb rho <> R_GlobalEnv then
                    result_success t
                  else result_success lang
                else result_success lang
             else result_success lang
  | LangSxp => runs_substituteList runs lang rho
  | _ => result_success lang
  end.


Definition substituteList (el rho : SEXP) :=
  add%stack "substituteList" in
  if%success isNull el then
      result_success el
  else
    do%success (el, p, res) := (el, R_NilValue : SEXP, R_NilValue : SEXP)
    whileb el <> R_NilValue do
      (** walk along the pairlist, substituting elements.
          res is the result
          p is the current last element
          h is the element currently being processed
       **)
      let%success h :=
      read%list el_car, el_cdr, el_tag := el in

      ifb el_car = R_DotsSymbol then
        let%success h :=
        ifb rho = R_NilValue then
          result_success (R_UnboundValue : SEXP) (** so there is no substitution below **)
        else
          findVarInFrame3 globals runs rho el_car true
        in
        ifb h = R_UnboundValue then
          LCONS globals R_DotsSymbol R_NilValue
        else ifb h = R_NilValue \/ h = R_MissingArg then
          result_success (R_NilValue : SEXP)
        else
          let%success h_type := TYPEOF h in
          ifb h_type = DotSxp then
            runs_substituteList runs h R_NilValue
          else
            result_error "'...' used in an incorrect context"
      else
        let%success h := substitute el_car rho in
        let%success h :=
        if%success isLanguage globals el then
          LCONS globals h R_NilValue
        else
          let%success h := CONS globals h R_NilValue in
          result_success h
        in
        set%tag h := el_tag in
        result_success h
      in

      let%success (p, res) :=
      ifb h <> R_NilValue then
        let%success res :=
        ifb res = R_NilValue then
          result_success h
        else
          set%cdr p := h in
          result_success res
        in
        (** now set 'p': dots might have expanded to a list of length > 1 **)
        do%success h := h
        while read%list _, h_cdr, _ := h in
          result_success (decide (h_cdr <> R_NilValue))
          do read%list _, h_cdr, _ := h in
          result_success h_cdr using runs in
        result_success (h, res)
      else
        result_success (p, res) in
      read%list _, el_cdr, _ := el in
      result_success (el_cdr, p, res)
    using runs in
  result_success res.

Definition asCharacterFactor (x : SEXP) : result SEXP :=
  add%stack "asCharacterfactor" in
  let%success x_inherits := inherits2 globals runs x "factor" in
  if negb x_inherits then
    result_error "attempting to coerce non-factor"
  else
    result_not_implemented "asCharacterfactor".

End Parameterised.

