(** Core.CArithmetic.
  The function names in this file correspond to the function names
  in the file main/arithmetic.c. **)

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
From Lib Require Import Double.
From CoqR Require Import Loops.
From CoqR.core Require Import CRinternals CRinlinedfuns Conflicts CAttrib.
From CoqR.core Require Import CEval CCoerce CDuplicate CRmath.


Section Parameterised.

(** Global Variables **)

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

Definition isRaw x :=
  add%stack "isRaw" in
  let%success x_type := TYPEOF x in
  result_success (decide (x_type = RawSxp)).

Definition binaryLogic code (s1 s2 : SEXP) : result_SEXP :=
  add%stack "binaryLogic" in
  let%success n1 := XLENGTH s1 in
  let%success n2 := XLENGTH s2 in
  let n := ifb n1 > n2 then n1 else n2 in
  ifb n1 = 0 \/ n2 = 0 then
    allocVector globals LglSxp 0
  else

  let%success ans := allocVector globals LglSxp n in
  run%success
  match code with
  | 1 => (* & : AND *)
    do%success (i1, i2) := (0, 0)
    for i from 0 to n - 1 do
      read%Logical x1 := s1 at i1 in
      read%Logical x2 := s2 at i2 in
      run%success
      ifb x1 = 0 \/ x2 = 0 then
        write%Logical ans at i := 0 in
        result_skip
      else ifb x1 = NA_LOGICAL \/ x2 = NA_LOGICAL then
        write%Logical ans at i := NA_LOGICAL in
        result_skip
      else
        write%Logical ans at i := 1 in
        result_skip
      in
      result_success (ifb (i1 + 1) = n1 then 0 else (i1 + 1), ifb (i2 + 1) = n2 then 0 else (i2 + 1))
    in result_skip
  | 2 => (* | : OR *)
    do%success (i1, i2) := (0, 0)
    for i from 0 to n - 1 do
      read%Logical x1 := s1 at i1 in
      read%Logical x2 := s2 at i2 in
      run%success
      ifb (x1 <> NA_LOGICAL /\ x1 <> 0) \/ (x2 <> NA_LOGICAL /\ x2 <> 0) then
        write%Logical ans at i := 1 in
        result_skip
      else ifb x1 = 0 /\ x2 = 0 then
        write%Logical ans at i := 0 in
        result_skip
      else
        write%Logical ans at i := NA_LOGICAL in
        result_skip
      in
      result_success (ifb (i1 + 1) = n1 then 0 else (i1 + 1), ifb (i2 + 1) = n2 then 0 else (i2 + 1))
    in result_skip
    | 3 => result_error "Unary operator '!' called with two arguments"
    | _ => result_impossible "binaryLogic with wrong code"
  end
  in
  result_success ans.


Definition binaryLogic2 (code : int) (s1 s2 : SEXP) : result_SEXP :=
  add%stack "binaryLogic2" in
  let%success n1 := XLENGTH s1 in
  let%success n2 := XLENGTH s2 in
  let n := ifb n1 > n2 then n1 else n2 in
  ifb n1 = 0 \/ n2 = 0 then
    allocVector globals RawSxp 0
  else
    result_not_implemented "Raw vector read".

Definition lunary (call op arg : SEXP) : result_SEXP :=
  add%stack "lunary" in

  let%success arg_isLogical := isLogical arg in
  let%success arg_isNumber := isNumber globals runs arg in
  let%success arg_isRaw := isRaw arg in

  ifb ~ arg_isLogical /\ ~ arg_isNumber /\ ~ arg_isRaw then
    result_error "invalid argument type"
  else

  let%success len := XLENGTH arg in
  let%success x :=
  ifb arg_isLogical \/ arg_isRaw then
    shallow_duplicate globals runs arg
  else
    let%success x := allocVector globals (if arg_isRaw then RawSxp else LglSxp) len in
    let%success names := getAttrib globals runs arg R_NamesSymbol in
    let%success dim := getAttrib globals runs arg R_DimSymbol in
    let%success dimnames := getAttrib globals runs arg R_DimNamesSymbol in
    let%success x :=
    ifb names <> R_NilValue then setAttrib globals runs x R_NamesSymbol names else result_success x in
    let%success x :=
    ifb dim <> R_NilValue then setAttrib globals runs x R_DimSymbol dim else result_success x in
    let%success x :=
    ifb dimnames <> R_NilValue then setAttrib globals runs x R_DimNamesSymbol dimnames else result_success x in
    result_success x

   in
   let%success arg_type := TYPEOF arg in
   run%success
   match arg_type with
   | LglSxp => do%success
               for i from 0 to len - 1 do
                 read%Logical arg_i := arg at i in
                 write%Logical x at i := ifb arg_i = NA_LOGICAL then NA_LOGICAL else decide (arg_i = 0)
                 in result_skip
               in
               result_skip
   | IntSxp => do%success
               for i from 0 to len - 1 do
                 read%Integer arg_i := arg at i in
                 write%Logical x at i := ifb arg_i = NA_INTEGER then NA_LOGICAL else decide (arg_i = 0)
                 in result_skip
               in
               result_skip
   | RealSxp => do%success
                for i from 0 to len - 1 do
                  read%Real arg_i := arg at i in
                  write%Logical x at i := ifb ISNAN arg_i then NA_LOGICAL else decide (arg_i = 0%Z)
                  in result_skip
                in
                result_skip
   | CplxSxp => result_not_implemented "complex case"
   | RawSxp => result_not_implemented "raw case"
   | _ => result_error "UNIMPLEMENTED TYPE 'lunary'"
   end
   in
   result_success x.



Definition tsConform x y :=
  add%stack "tsConform" in
  let%success x := getAttrib globals runs x R_TspSymbol in
  let%success y := getAttrib globals runs y R_TspSymbol in

  ifb x <> R_NilValue /\ y <> R_NilValue then
    let%success x_type := TYPEOF x in
    let%success y_type := TYPEOF y in
    ifb x_type = RealSxp /\ y_type = RealSxp then
      read%Real x_0 := x at 0 in
      read%Real x_1 := x at 1 in
      read%Real x_2 := x at 2 in
      result_success (decide (x_0 = x_0 /\ x_1 = x_1 /\ x_2 = x_2))
    else
      result_success false
  else
    result_success false.

(* logical binary : "&" or "|" *)
Definition lbinary (call op args : SEXP) :=
  add%stack "lbinary" in
  read%list args_car, args_cdr, _ := args in
  read%list args_cdr_car, _, _ := args_cdr in
  let x := args_car in
  let y := args_cdr_car in

  let%success x_isRaw := isRaw x in
  let%success y_isRaw := isRaw y in

  let%success x_isNull := isNull x in
  let%success y_isNull := isNull y in
  let%success x_isNumber := isNumber globals runs x in
  let%success y_isNumber := isNumber globals runs y in

  (* Omitting raw type check due to empty body in if *)
  ifb ~ (x_isNull \/ x_isNumber) \/ ~ (y_isNull \/ y_isNumber) then
    result_error "operations are possible only for numeric, logical or complex types"
  else
  let%success nx := xlength globals runs x in
  let%success ny := xlength globals runs y in

  let%success xarray := isArray globals runs x in
  let%success yarray := isArray globals runs y in

  let%success xts := isTs globals runs x in
  let%success yts := isTs globals runs y in

  let%success (dims, xnames, ynames) :=
  ifb xarray \/ yarray then
    let%success dims :=
    ifb xarray /\ yarray then
      let%success x_y_conformable := conformable globals runs x y in
      if negb x_y_conformable then
        result_error "non-conformable arrays"
      else
        getAttrib globals runs x R_DimSymbol

    else ifb xarray /\ (ny <> 0 \/ nx = 0) then
      getAttrib globals runs x R_DimSymbol

    else ifb yarray /\ (nx <> 0 \/ ny = 0) then
      getAttrib globals runs y R_DimSymbol

    else
      result_success (R_NilValue : SEXP)

    in
    let%success xnames := getAttrib globals runs x R_DimNamesSymbol in
    let%success ynames := getAttrib globals runs y R_DimNamesSymbol in
    result_success (dims, xnames, ynames)

  else
    let dims := (R_NilValue : SEXP) in
    let%success xnames := getAttrib globals runs x R_NamesSymbol in
    let%success ynames := getAttrib globals runs y R_NamesSymbol in
    result_success (dims, xnames, ynames)

  in
  let%success (klass, tsp) :=
  ifb xts \/ yts then
    ifb xts /\ yts then
      let%success x_y_tsConform := tsConform x y in
      if negb x_y_tsConform then
        result_error "non-conformable time series"
      else
      let%success tsp := getAttrib globals runs x R_TspSymbol in
      let%success klass := getAttrib globals runs x R_ClassSymbol in
      result_success (klass, tsp)
    else if xts then
      ifb nx < ny then
        result_error "TS vector mismatch"
      else
        let%success tsp := getAttrib globals runs x R_TspSymbol in
        let%success klass := getAttrib globals runs x R_ClassSymbol in
        result_success (klass, tsp)
    else (*(yts)*)
      ifb ny < nx then
        result_error "TS vector mismatch"
      else
        let%success tsp := getAttrib globals runs y R_TspSymbol in
        let%success klass := getAttrib globals runs y R_ClassSymbol in
        result_success (klass, tsp)
  else
    result_success (NULL, NULL)

  in
  let%success x :=
  ifb nx > 0 /\ ny > 0 then
    (* Warning omitted *)

    ifb x_isRaw /\ y_isRaw then
      let%success op_primval := PRIMVAL runs op in
      binaryLogic2 op_primval x y

    else
      let%success x :=
      if x_isNull then
        let%success alloc_Vec := allocVector globals LglSxp 0 in
        set%car args := alloc_Vec in
        result_success alloc_Vec
      else (* isNumeric(x) *)
        let%success coerce_Vec := coerceVector globals runs x LglSxp in
        set%car args := coerce_Vec in
        result_success coerce_Vec
      in

      let%success y :=
      if y_isNull then
        let%success alloc_Vec := allocVector globals LglSxp 0 in
        set%car args := alloc_Vec in
        result_success alloc_Vec
      else (* isNumeric(y) *)
        let%success coerce_Vec := coerceVector globals runs y LglSxp in
        set%car args_cdr := coerce_Vec in
        result_success coerce_Vec
      in

      let%success op_primval := PRIMVAL runs op in
      binaryLogic (Z.to_nat op_primval) x y
  else  (* nx == 0 || ny == 0 *)
    allocVector globals LglSxp 0
  in

  let%success x :=
  ifb dims <> R_NilValue then
    run%success setAttrib globals runs x R_DimSymbol dims in

    ifb xnames <> R_NilValue then
      run%success setAttrib globals runs x R_DimNamesSymbol xnames in
      result_success x
    else ifb ynames <> R_NilValue then
      run%success setAttrib globals runs x R_DimNamesSymbol ynames in
      result_success x
    else
      result_success x
  else
    let%success x_xlength := XLENGTH x in
    ifb xnames <> R_NilValue then
      let%success xnames_xlength := XLENGTH xnames in
      ifb x_xlength = xnames_xlength then
        run%success setAttrib globals runs x R_NamesSymbol xnames in
        result_success x
      else
        ifb ynames <> R_NilValue then
          let%success ynames_xlength := XLENGTH ynames in
          ifb x_xlength = ynames_xlength then
            run%success setAttrib globals runs x R_NamesSymbol ynames in
            result_success x
          else
            result_success x
        else
          result_success x
    else
      ifb ynames <> R_NilValue then
        let%success ynames_xlength := XLENGTH ynames in
        ifb x_xlength = ynames_xlength then
          run%success setAttrib globals runs x R_NamesSymbol ynames in
          result_success x
        else
          result_success x
      else
        result_success x
  in

  let%success x :=
  ifb xts \/ yts then
    run%success setAttrib globals runs x R_TspSymbol tsp in
    run%success setAttrib globals runs x R_ClassSymbol klass in
    result_success x
  else
    result_success x
  in
  result_success x.

End Parameterised.
