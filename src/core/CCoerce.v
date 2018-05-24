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

Definition installAttrib S vec name val :=
  add%stack "installAttrib" in
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "Cannot set attribute on a CharSxp."
  else ifb vec_type = SymSxp then
    result_error S "Cannot set attribute on a symbol."
  else
    let%success vec_attr := ATTRIB S vec using S in
    fold%return t := R_NilValue : SEXP
    along vec_attr
    as s, _, s_list do
      ifb list_tagval s_list = name then
        set%car s := val using S in
        result_rreturn S val
      else result_rsuccess S s using S, runs, globals in
    let (S, s) := CONS globals S val R_NilValue in
    set%tag s := name using S in
    run%success
      ifb vec_attr = R_NilValue then
        run%success SET_ATTRIB S vec s using S in
        result_skip S
      else
        set%cdr t := s using S in
        result_skip S using S in
    result_success S val.

Definition copyMostAttrib S (inp ans : SEXP) :=
  add%stack "copyMostAttrib" in
  ifb ans = R_NilValue then
    result_error S "Attempt to set an attribute on NULL."
  else
    let%success inp_attr := ATTRIB S inp using S in
    fold%success
    along inp_attr
    as s_car, s_tag do
      ifb s_tag <> R_NamesSymbol
          /\ s_tag <> R_DimSymbol
          /\ s_tag <> R_DimNamesSymbol then
        run%success installAttrib S ans s_tag s_car using S in
        result_skip S
      else result_skip S using S, runs, globals in
    if%success OBJECT S inp using S then
      SET_OBJECT S ans true in
    if%success IS_S4_OBJECT S inp using S then
      SET_S4_OBJECT S ans
    else UNSET_S4_OBJECT S ans.


Definition LogicalFromString S (x : SEXP) :=
  add%stack "LogicalFromString" in
  ifb x <> R_NaString then
    let%success c := CHAR S x using S in
    if StringTrue c then result_success S (1 : int)
    else if StringFalse c then result_success S (0 : int)
    else result_success S NA_LOGICAL
  else result_success S NA_LOGICAL.

Definition LogicalFromInteger S (x : int) : result int :=
  add%stack "LogicalFromInteger" in
  ifb x = NA_INTEGER then result_success S NA_LOGICAL
  else result_success S (decide (x <> 0) : int).

Definition LogicalFromReal S x : result int :=
  add%stack "LogicalFromReal" in
  ifb ISNAN x then result_success S NA_LOGICAL
  else result_success S (negb (Double.is_zero x) : int).

Definition LogicalFromComplex S x : result int :=
  add%stack "LogicalFromComplex" in
  ifb ISNAN (Rcomplex_r x) \/ ISNAN (Rcomplex_i x) then result_success S NA_LOGICAL
  else result_success S (decide (~ Double.is_zero (Rcomplex_r x)
                                 \/ ~ Double.is_zero (Rcomplex_i x)) : int).

Definition asLogical S x :=
  add%stack "asLogical" in
  if%success isVectorAtomic S x using S then
    let%success len := XLENGTH S x using S in
    ifb len < 1 then
      result_success S NA_LOGICAL
    else
      let%success x_type := TYPEOF S x using S in
      match x_type with
      | LglSxp => LOGICAL_ELT S x 0
      | IntSxp =>
        let%success i := INTEGER_ELT S x 0 using S in
        LogicalFromInteger S i
      | RealSxp =>
        let%success r := REAL_ELT S x 0 using S in
        LogicalFromReal S r
      | CplxSxp =>
        let%success c := COMPLEX_ELT S x 0 using S in
        LogicalFromComplex S c
      | StrSxp =>
        let%success s := STRING_ELT S x 0 using S in
        LogicalFromString S s
      | RawSxp =>
        let%success s := RAW_ELT S x 0 using S in
        LogicalFromString S s
      | _ => result_error S "Unimplemented type."
      end
  else
    let%success x_type := TYPEOF S x using S in
    ifb x_type = CharSxp then
      LogicalFromString S x
    else result_success S NA_LOGICAL.

Definition IntegerFromString S (x : SEXP) :=
  add%stack "IntegerFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR S x using S in
      result_success S (negb (isBlankString c))
    else result_success S false using S then
    unimplemented_function "R_strtod."
  else result_success S NA_INTEGER.

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

Definition asInteger S x :=
  add%stack "asInteger" in
  let%success t := TYPEOF S x using S in
  if%success
      if%success isVectorAtomic S x using S then
        let%success l := XLENGTH S x using S in
        result_success S (decide (l >= 1))
      else result_success S false using S then
    match t with
    | LglSxp =>
      read%Logical x0 := x at 0 using S in
      result_success S (IntegerFromLogical x0)
    | IntSxp =>
      read%Integer x0 := x at 0 using S in
      result_success S x0
    | RealSxp =>
      read%Real x0 := x at 0 using S in
      result_success S (IntegerFromReal x0)
    | CplxSxp =>
      read%Complex x0 := x at 0 using S in
      result_success S (IntegerFromComplex x0)
    | StrSxp =>
      read%Pointer x0 := x at 0 using S in
      IntegerFromString S x0
    | _ => result_error S "Unimplemented type."
    end
  else ifb t = CharSxp then
    IntegerFromString S x
  else result_success S NA_INTEGER.

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

Definition RealFromString S (x : SEXP) :=
  add%stack "RealFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR S x using S in
      result_success S (negb (isBlankString c))
    else result_success S false using S then
    unimplemented_function "R_strtod."
  else result_success S NA_REAL.

Definition asReal S x :=
  add%stack "asReal" in
  let%success t := TYPEOF S x using S in
  if%success
      if%success isVectorAtomic S x using S then
        let%success l := XLENGTH S x using S in
        result_success S (decide (l >= 1))
      else result_success S false using S then
    match t with
    | LglSxp =>
      read%Logical x0 := x at 0 using S in
      result_success S (RealFromLogical x0)
    | IntSxp =>
      read%Integer x0 := x at 0 using S in
      result_success S (RealFromInteger x0)
    | RealSxp =>
      read%Real x0 := x at 0 using S in
      result_success S x0
    | CplxSxp =>
      read%Complex x0 := x at 0 using S in
      result_success S (RealFromComplex x0)
    | StrSxp =>
      read%Pointer x0 := x at 0 using S in
      RealFromString S x0
    | _ => result_error S "Unimplemented type."
    end
  else ifb t = CharSxp then
    RealFromString S x
  else result_success S NA_REAL.

Definition coerceSymbol S v type :=
  add%stack "coerceSymbol" in
  let%success rval :=
    ifb type = ExprSxp then
      let%success rval := allocVector globals S type 1 using S in
      run%success SET_VECTOR_ELT S rval 0 v using S in
      result_success S rval
    else ifb type = CharSxp then
      PRINTNAME S v
    else ifb type = StrSxp then
      let%success v_name := PRINTNAME S v using S in
      ScalarString globals S v_name
    else
      (* A warning has been formalised out here. *)
      result_success S (R_NilValue : SEXP) using S in
  result_success S rval.

Definition PairToVectorList (S : state) (x : SEXP) : result SEXP :=
  unimplemented_function "PairToVectorList".

Definition VectorToPairList (S : state) (x : SEXP) : result SEXP :=
  add%stack "VectorToPairList" in
    let%success len := R_length globals runs S x using S in
    
    let (S, xnew) := allocList globals S len in 
    let%success xnames := runs_getAttrib runs S x R_NamesSymbol using S in
    let named := decide (xnames <> R_NilValue) in
    
    do%success xptr := xnew
    for i from 0 to len - 1 do
                                                                                 
        let%success x_i := VECTOR_ELT S x i using S in
        let%success x_named := NAMED S x using S in                      
        run%success RAISE_NAMED S x_i x_named using S in
               
        set%car xptr := x_i using S in
        
        let%success xnames_i := STRING_ELT S xnames i using S in
        let%success xnames_i_char := CHAR S xnames_i using S in
        let xnames_i_char_0 := LibOption.unsome_default "000"%char (String.get 0 xnames_i_char) in 
        ifb named /\  xnames_i_char_0 <> "000"%char then
            let%success xnames_i_install := installTrChar globals runs S xnames_i using S in
            set%tag xptr := xnames_i_install using S in
            read%list _, xptr_cdr, _ := xptr using S in
            result_success S xptr_cdr      
        else  
            read%list _, xptr_cdr, _ := xptr using S in
            result_success S xptr_cdr
    using S in
    ifb len > 0 then
        run%success copyMostAttrib S x xnew using S in
        result_success S xnew
    else
        result_success S xnew.  
                     
Definition ComplexFromString S (x : SEXP) :=
  add%stack "ComplexFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR S x using S in
      result_success S (negb (isBlankString c))
    else result_success S false using S then
    unimplemented_function "R_strtod."
  else result_success S (make_Rcomplex NA_REAL NA_REAL).

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

Definition asComplex S x :=
  add%stack "asComplex" in
  let%success x_va := isVectorAtomic S x using S in
  let%success x_len := XLENGTH S x using S in
  let%success x_type := TYPEOF S x using S in
  ifb x_va /\ x_len >= 1 then
    match x_type with
    | LglSxp =>
      let%success x_0 := LOGICAL_ELT S x 0 using S in
      result_success S (ComplexFromLogical x_0)
    | IntSxp =>
      let%success x_0 := INTEGER_ELT S x 0 using S in
      result_success S (ComplexFromInteger x_0)
    | RealSxp =>
      let%success x_0 := REAL_ELT S x 0 using S in
      result_success S (ComplexFromReal x_0)
    | CplxSxp =>
      COMPLEX_ELT S x 0
    | StrSxp =>
      let%success x_0 := STRING_ELT S x 0 using S in
      ComplexFromString S x_0
    | _ =>
      result_error S "Unimplemented type."
    end
  else ifb x_type = CharSxp then
    ComplexFromString S x
  else result_success S (make_Rcomplex NA_REAL NA_REAL).

Definition coercePairList S v type :=
  add%stack "coercePairList" in
  let%exit (rval, n) :=
    ifb type = ListSxp then
      result_rreturn S v
    else ifb type = ExprSxp then
      let%success rval := allocVector globals S type 1 using S in
      run%success SET_VECTOR_ELT S rval 0 v using S in
      result_rreturn S rval
    else ifb type = StrSxp then
      let%success n := R_length globals runs S v using S in
      let%success rval := allocVector globals S type n using S in
      fold%success i := 0
      along v
      as v_car, _ do
        let%success v_car_is := isString S v_car using S in
        let%success v_car_len := R_length globals runs S v_car using S in
        run%success
          ifb v_car_is /\ v_car_len = 1 then
            let%success v_car_0 := STRING_ELT S v_car 0 using S in
            SET_STRING_ELT S rval i v_car_0
          else unimplemented_function "deparse1line" using S in
        result_success S (1 + i) using S, runs, globals in
      result_rsuccess S (rval, n)
    else ifb type = VecSxp then
      let%success rval := PairToVectorList S v using S in
      result_rreturn S rval
    else if%success isVectorizable globals runs S v using S then
      let%success n := R_length globals runs S v using S in
      let%success rval := allocVector globals S type n using S in
      run%success
        match type with
        | LglSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp using S in
            let%success vp_car_lgl := asLogical S vp_car using S in
            write%Logical rval at i := vp_car_lgl using S in
            result_success S vp_cdr using S
        | IntSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp using S in
            let%success vp_car_lgl := asInteger S vp_car using S in
            write%Integer rval at i := vp_car_lgl using S in
            result_success S vp_cdr using S
        | RealSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp using S in
            let%success vp_car_lgl := asReal S vp_car using S in
            write%Real rval at i := vp_car_lgl using S in
            result_success S vp_cdr using S
        | CplxSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp using S in
            let%success vp_car_lgl := asComplex S vp_car using S in
            write%Complex rval at i := vp_car_lgl using S in
            result_success S vp_cdr using S
        | RawSxp => result_not_implemented "Raw case."
        | _ => result_error S "Unimplemented type."
        end using S in
      result_rsuccess S (rval, n)
    else result_error S "‘pairlist’ object cannot be coerce as-is." using S in
  fold%success i := false
  along v
  as _, v_tag do
    ifb v_tag <> R_NilValue then
      result_success S true
    else result_success S i using S, runs, globals in
  run%success
    if i then
      let%success names := allocVector globals S StrSxp n using S in
      fold%success i := 0
      along v
      as _, v_tag do
        run%success
          ifb v_tag <> R_NilValue then
            let%success v_tag_name := PRINTNAME S v_tag using S in
            SET_STRING_ELT S names i v_tag_name
          else result_skip S using S in
        result_success S (1 + i) using S, runs, globals in
      result_skip S
    else result_skip S using S in
  result_success S rval.

Definition coerceVectorList (S : state) (v : SEXP) (type : SExpType) : result SEXP :=
  unimplemented_function "coerceVectorList".

Definition StringFromLogical S x :=
  add%stack "StringFromLogical" in
  ifb x = NA_LOGICAL then
    result_success S (NA_STRING : SEXP)
  else
    let (S, r) := mkChar globals S (EncodeLogical x) in
    result_success S r.

Definition StringFromInteger S x :=
  add%stack "StringFromInteger" in
  ifb x = NA_INTEGER then
    result_success S (NA_STRING : SEXP)
  else unimplemented_function "formatInteger".

Definition StringFromComplex S x :=
  add%stack "StringFromComplex" in
  ifb R_IsNA (Rcomplex_r x) \/ R_IsNA (Rcomplex_i x) then
    result_success S (NA_STRING : SEXP)
  else unimplemented_function "EncodeComplex".

Definition coerceToSymbol S v :=
  add%stack "coerceToSymbol" in
  let%success v_len := R_length globals runs S v using S in
  ifb v_len <= 0 then
    result_error S "Invalid data."
  else
    let%success v_type := TYPEOF S v using S in
    let%success ans :=
      match v_type with
      | LglSxp =>
        let%success v_0 := LOGICAL_ELT S v 0 using S in
        StringFromLogical S v_0
      | IntSxp =>
        let%success v_0 := INTEGER_ELT S v 0 using S in
        StringFromInteger S v_0
      | RealSxp =>
        let%success v_0 := REAL_ELT S v 0 using S in
        StringFromReal globals S v_0
      | CplxSxp =>
        let%success v_0 := COMPLEX_ELT S v 0 using S in
        StringFromComplex S v_0
      | StrSxp =>
        STRING_ELT S v 0
      | RawSxp => result_not_implemented "Raw case."
      | _ => result_error S "Unimplemented type."
      end using S in
    installTrChar globals runs S ans.

Definition coerceToLogical S v :=
  add%stack "coerceToLogical" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector globals S LglSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        let%success pa_i := LogicalFromInteger S v_i using S in
        write%Logical ans at i := pa_i using S in
        result_skip S using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        let%success pa_i := LogicalFromReal S v_i using S in
        write%Logical ans at i := pa_i using S in
        result_skip S using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        let%success pa_i := LogicalFromComplex S v_i using S in
        write%Logical ans at i := pa_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success pa_i := LogicalFromString S v_i using S in
        write%Logical ans at i := pa_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToInteger S v :=
  add%stack "coerceToInteger" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector globals S IntSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        write%Integer ans at i := IntegerFromLogical v_i using S in
        result_skip S using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        write%Integer ans at i := IntegerFromReal v_i using S in
        result_skip S using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        write%Integer ans at i := IntegerFromComplex v_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success pa_i := IntegerFromString S v_i using S in
        write%Integer ans at i := pa_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToReal S v :=
  add%stack "coerceToReal" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector globals S RealSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        write%Real ans at i := RealFromLogical v_i using S in
        result_skip S using S
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        write%Real ans at i := RealFromInteger v_i using S in
        result_skip S using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        write%Real ans at i := RealFromComplex v_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success pa_i := RealFromString S v_i using S in
        write%Real ans at i := pa_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToComplex S v :=
  add%stack "coerceToComplex" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector globals S CplxSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        write%Complex ans at i := ComplexFromLogical v_i using S in
        result_skip S using S
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        write%Complex ans at i := ComplexFromInteger v_i using S in
        result_skip S using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        write%Complex ans at i := ComplexFromReal v_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success pa_i := ComplexFromString S v_i using S in
        write%Complex ans at i := pa_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToRaw (S : state) (v : SEXP) : result SEXP :=
  unimplemented_function "coerceToRaw".

Definition coerceToString S v :=
  add%stack "coerceToString" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector globals S StrSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB globals runs S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        let%success s_i := StringFromLogical S v_i using S in
        SET_STRING_ELT S ans i s_i using S
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        let%success s_i := StringFromInteger S v_i using S in
        SET_STRING_ELT S ans i s_i using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        let%success s_i := StringFromReal globals S v_i using S in
        SET_STRING_ELT S ans i s_i using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        let%success s_i := StringFromComplex S v_i using S in
        SET_STRING_ELT S ans i s_i using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToExpression S v :=
  add%stack "coerceToExpression" in
  let%success ans :=
    if%success isVectorAtomic S v using S then
      let%success n := XLENGTH S v using S in
      let%success ans := allocVector globals S ExprSxp n using S in
      let%success v_type := TYPEOF S v using S in
      run%success
        match v_type with
        | LglSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := LOGICAL_ELT S v i using S in
            run%success SET_VECTOR_ELT S ans i (ScalarLogical globals v_i) using S in
            result_skip S using S
        | IntSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := INTEGER_ELT S v i using S in
            let (S, s_i) := ScalarInteger globals S v_i in
            run%success SET_VECTOR_ELT S ans i s_i using S in
            result_skip S using S
        | RealSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := REAL_ELT S v i using S in
            let (S, s_i) := ScalarReal globals S v_i in
            run%success SET_VECTOR_ELT S ans i s_i using S in
            result_skip S using S
        | CplxSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := COMPLEX_ELT S v i using S in
            let (S, s_i) := ScalarComplex globals S v_i in
            run%success SET_VECTOR_ELT S ans i s_i using S in
            result_skip S using S
        | StrSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := STRING_ELT S v i using S in
            let%success s_i := ScalarString globals S v_i using S in
            run%success SET_VECTOR_ELT S ans i s_i using S in
            result_skip S using S
        | RawSxp => result_not_implemented "Raw case."
        | _ =>
          result_error S "Unimplemented type."
        end using S in
      result_success S ans
    else
      let%success ans := allocVector globals S ExprSxp 1 using S in
      let%success v_d := duplicate globals runs S v using S in
      run%success SET_VECTOR_ELT S ans 0 v_d using S in
      result_success S ans using S in
  result_success S ans.

Definition coerceToVectorList S v :=
  add%stack "coerceToVectorList" in
  let%success n := xlength globals runs S v using S in
  let%success ans := allocVector globals S VecSxp n using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        run%success SET_VECTOR_ELT S ans i (ScalarLogical globals v_i) using S in
        result_skip S using S
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        let (S, s_i) := ScalarInteger globals S v_i in
        run%success SET_VECTOR_ELT S ans i s_i using S in
        result_skip S using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        let (S, s_i) := ScalarReal globals S v_i in
        run%success SET_VECTOR_ELT S ans i s_i using S in
        result_skip S using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        let (S, s_i) := ScalarComplex globals S v_i in
        run%success SET_VECTOR_ELT S ans i s_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success s_i := ScalarString globals S v_i using S in
        run%success SET_VECTOR_ELT S ans i s_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | ListSxp
    | LangSxp =>
      do%success tmp := v
      for i from 0 to n - 1 do
        read%list tmp_car, tmp_cdr, _ := tmp using S in
        run%success SET_VECTOR_ELT S ans i tmp_car using S in
        result_success S tmp_cdr using S in
      result_skip S
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  let%success tmp := runs_getAttrib runs S v R_NamesSymbol using S in
  run%success
    ifb tmp <> R_NilValue then
      run%success runs_setAttrib runs S ans R_NamesSymbol tmp using S in
      result_skip S
    else result_skip S using S in
  result_success S ans.

Definition coerceToPairList S v :=
  add%stack "coerceToPairList" in
  let%success n := LENGTH globals S v using S in
  let (S, ans) := allocList globals S n in
  do%success ansp := ans
  for i from 0 to n - 1 do
    read%list _, ansp_cdr, _ := ansp using S in
    run%success
      let%success v_type := TYPEOF S v using S in
      match v_type with
      | LglSxp =>
        let%success ansp_car := allocVector globals S LglSxp 1 using S in
        set%car ansp := ansp_car using S in
        let%success v_i := LOGICAL_ELT S v i using S in
        write%Logical ansp_car at 0 := v_i using S in
        result_skip S
      | IntSxp =>
        let%success ansp_car := allocVector globals S IntSxp 1 using S in
        set%car ansp := ansp_car using S in
        let%success v_i := INTEGER_ELT S v i using S in
        write%Integer ansp_car at 0 := v_i using S in
        result_skip S
      | RealSxp =>
        let%success ansp_car := allocVector globals S RealSxp 1 using S in
        set%car ansp := ansp_car using S in
        let%success v_i := REAL_ELT S v i using S in
        write%Real ansp_car at 0 := v_i using S in
        result_skip S
      | CplxSxp =>
        let%success ansp_car := allocVector globals S CplxSxp 1 using S in
        set%car ansp := ansp_car using S in
        let%success v_i := COMPLEX_ELT S v i using S in
        write%Complex ansp_car at 0 := v_i using S in
        result_skip S
      | StrSxp =>
        let%success v_i := STRING_ELT S v i using S in
        let%success ansp_car := ScalarString globals S v_i using S in
        set%car ansp := ansp_car using S in
        result_skip S
      | RawSxp => result_not_implemented "Raw case."
      | VecSxp =>
        let%success v_i := VECTOR_ELT S v i using S in
        set%car ansp := v_i using S in
        result_skip S
      | ExprSxp =>
        let%success v_i := VECTOR_ELT S v i using S in
        set%car ansp := v_i using S in
        result_skip S
      | _ =>
        result_error S "Unimplemented type."
      end using S in
    result_success S ansp_cdr using S in
  let%success ansp := runs_getAttrib runs S v R_NamesSymbol using S in
  run%success
    ifb ansp <> R_NilValue then
      run%success runs_setAttrib runs S ans R_NamesSymbol ansp using S in
      result_skip S
    else result_skip S using S in
  result_success S ans.

Definition coerceVector S v type :=
  add%stack "coerceVector" in
  let%success v_type := TYPEOF S v using S in
  ifb v_type = type then
    result_success S v
  else
    let%success v_s4 := IS_S4_OBJECT S v using S in
    let%exit v :=
      ifb v_s4 /\ v_type = S4Sxp then
        unimplemented_function "R_getS4DataSlot"
      else result_rsuccess S v using S in
    let%success ans :=
      let%success v_type := TYPEOF S v using S in
      match v_type with
      | SymSxp =>
        coerceSymbol S v type
      | NilSxp
      | ListSxp =>
        coercePairList S v type
      | LangSxp =>
        ifb type <> StrSxp then
          coercePairList S v type
        else
          let%success n := R_length globals runs S v using S in
          let%success ans := allocVector globals S type n using S in
          ifb n = 0 then
            result_success S ans
          else
            read%list v_car, v_cdr, _ := v using S in
            let op := v_car in
            let%success op_type := TYPEOF S op using S in
            let%success (i, v) :=
              ifb op_type = SymSxp then
                let%success op_name := PRINTNAME S op using S in
                run%success SET_STRING_ELT S ans 0 op_name using S in
                result_success S (1, v_cdr)
              else result_success S (0, v) using S in
            fold%success i := i
            along v
            as v_car, _ do
              let%success v_car_is := isString S v_car using S in
              let%success v_car_len := R_length globals runs S v_car using S in
              run%success
                ifb v_car_is /\ v_car_len = 1 then
                  let%success v_car_0 := STRING_ELT S v_car 0 using S in
                  SET_STRING_ELT S ans i v_car_0
                else unimplemented_function "deparse1line" using S in
              result_success S (1 + i) using S, runs, globals in
            result_success S ans
      | VecSxp
      | ExprSxp =>
        coerceVectorList S v type
      | EnvSxp =>
        result_error S "Environments can not be coerced."
      | LglSxp
      | IntSxp
      | RealSxp
      | CplxSxp
      | StrSxp
      | RawSxp =>
        match type with
        | SymSxp => coerceToSymbol S v
        | LglSxp => coerceToLogical S v
        | IntSxp => coerceToInteger S v
        | RealSxp => coerceToReal S v
        | CplxSxp => coerceToComplex S v
        | RawSxp => coerceToRaw S v
        | StrSxp => coerceToString S v
        | ExprSxp => coerceToExpression S v
        | VecSxp => coerceToVectorList S v
        | ListSxp => coerceToPairList S v
        | _ =>
          result_error S "Cannot coerce to this type."
        end
      | _ =>
        result_error S "Cannot coerce this type to this other type."
      end using S in
    result_success S ans.

Definition CreateTag S x :=
  add%stack "CreateTag" in
  let%success x_n := isNull S x using S in
  let%success x_sy := isSymbol S x using S in
  ifb x_n \/ x_sy then
    result_success S x
  else
    if%success
        let%success x_st := isString S x using S in
        let%success x_len := R_length globals runs S x using S in
        ifb x_st /\ x_len >= 1 then
          let%success x_0 := STRING_ELT S x 0 using S in
          let%success x_0_len := R_length globals runs S x_0 using S in
          result_success S (decide (x_0_len >= 1))
        else result_success S false using S then
      let%success x_0 := STRING_ELT S x 0 using S in
      installTrChar globals runs S x_0
    else unimplemented_function "deparse1".

Definition copyDimAndNames S x ans :=
  add%stack "copyDimAndNames" in
  if%success isVector S x using S then
    let%success dims := runs_getAttrib runs S x R_DimSymbol using S in
    run%success
      ifb dims <> R_NilValue then
        run%success runs_setAttrib runs S ans R_DimSymbol dims using S in
        result_skip S
      else result_skip S using S in
    if%success isArray globals runs S x using S then
      let%success names := runs_getAttrib runs S x R_DimNamesSymbol using S in
      ifb names <> R_NilValue then
        run%success runs_setAttrib runs S ans R_DimNamesSymbol names using S in
        result_skip S
      else result_skip S
    else
      let%success names := runs_getAttrib runs S x R_NamesSymbol using S in
      ifb names <> R_NilValue then
        run%success runs_setAttrib runs S ans R_NamesSymbol names using S in
        result_skip S
      else result_skip S
  else result_skip S.


Definition substitute S (lang rho : SEXP) : result SEXP :=
  add%stack "substitute" in
    let%success lang_type := TYPEOF S lang using S in
    match lang_type with
    | PromSxp => let%success lang_prexpr := PREXPR globals S lang using S in
                runs_substitute runs S lang_prexpr rho
    | SymSxp => ifb rho <> R_NilValue then
                   let%success t := findVarInFrame3 globals runs S rho lang true using S in
                   ifb t <> R_UnboundValue then
                       let%success t_type := TYPEOF S t using S in

                       ifb t_type = PromSxp then
                           let%success t_prexpr := PREXPR globals S t using S in
                           do%success t := t_prexpr
                           while let%success t_type := TYPEOF S t using S in
                                 result_success S (decide (t_type = PromSxp)) do PREXPR globals S t
                           using S, runs in
                           (** make sure code will not be modified: **)
                           set%named t := named_plural using S in
                           result_success S t
                       else ifb t_type = DotSxp then
                           result_error S "'...' used in an incorrect context"
                       else ifb rho <> R_GlobalEnv then
                           result_success S t
                       else result_success S lang                 
                   else result_success S lang
               else result_success S lang
    | LangSxp => runs_substituteList runs S lang rho
    | _ => result_success S lang
    end.
                       
               
Definition substituteList (S : state) (el rho : SEXP) :=
  add%stack "substituteList" in
    if%success isNull S el using S then
        result_success S el           
    else
        do%success (el, p, res) := (el, R_NilValue : SEXP, R_NilValue : SEXP)
        whileb el <> R_NilValue do
            (**
               walk along the pairlist, substituting elements.
	       res is the result
	       p is the current last element
	       h is the element currently being processed
           **)
            let%success h :=  
            read%list el_car, el_cdr, el_tag := el using S in

            ifb el_car = R_DotsSymbol then
                let%success h :=
                ifb rho = R_NilValue then
                    result_success S (R_UnboundValue : SEXP) (** so there is no substitution below **)
                else
                    findVarInFrame3 globals runs S rho el_car true
                using S in
                ifb h = R_UnboundValue then
                    LCONS globals S R_DotsSymbol R_NilValue
                else ifb h = R_NilValue \/ h = R_MissingArg then
                    result_success S (R_NilValue : SEXP)
                else
                    let%success h_type := TYPEOF S h using S in
                    ifb h_type = DotSxp then
                        runs_substituteList runs S h R_NilValue
                    else
                        result_error S "'...' used in an incorrect context"
            else 
                let%success h := substitute S el_car rho using S in
                let%success h :=
                if%success isLanguage globals S el using S then
                    LCONS globals S h R_NilValue
                else
                    let (S, h) := CONS globals S h R_NilValue in
                    result_success S h
                using S in
                set%tag h := el_tag using S in
                result_success S h
            using S in

            let%success (p, res) :=       
            ifb h <> R_NilValue then
                let%success res :=
                ifb res = R_NilValue then
                    result_success S h
                else
                    set%cdr p := h using S in
                    result_success S res
                using S in
                (** now set 'p': dots might have expanded to a list of length > 1 **)
                do%success h := h
                while read%list _, h_cdr, _ := h using S in
                    result_success S (decide (h_cdr <> R_NilValue))
                    do read%list _, h_cdr, _ := h using S in
                    result_success S h_cdr using S, runs in
                result_success S (h, res)    
            else
                result_success S (p, res) using S in
            read%list _, el_cdr, _ := el using S in
            result_success S (el_cdr, p, res)
        using S, runs in
    result_success S res.    
  
End Parameterised.

