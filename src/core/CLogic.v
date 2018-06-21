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
Require Import Double.
Require Import Loops.
Require Import CRinternals.
Require Import CRinlinedfuns.
Require Import Conflicts.
Require Import CAttrib.
Require Import CEval.
Require Import CCoerce.
Require Import CDuplicate.
Require Import CRmath.


Section Parameterised.

(** Global Variables **)

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

Definition isRaw S x :=
  add%stack "isRaw" in
    let%success x_type := TYPEOF S x using S in
    result_success S (decide (x_type = RawSxp)).

Definition binaryLogic S code (s1 s2 : SEXP) : result SEXP :=
  add%stack "binaryLogic" in
    let%success n1 := XLENGTH S s1 using S in
    let%success n2 := XLENGTH S s2 using S in
    let n := ifb n1 > n2 then n1 else n2 in
    ifb n1 = 0 \/ n2 = 0 then
        allocVector globals S LglSxp 0
    else

    let%success ans := allocVector globals S LglSxp n using S in
    run%success
    match code with
    | 1 => (* & : AND *)
      do%success (i1, i2) := (0, 0)
      for i from 0 to n - 1 do
          read%Logical x1 := s1 at i1 using S in
          read%Logical x2 := s2 at i2 using S in
          run%success
          ifb x1 = 0 \/ x2 = 0 then 
              write%Logical ans at i := 0 using S in
              result_skip S
          else ifb x1 = NA_LOGICAL \/ x2 = NA_LOGICAL then
              write%Logical ans at i := NA_LOGICAL using S in
              result_skip S
          else
              write%Logical ans at i := 1 using S in
              result_skip S                            
          using S in
          result_success S (ifb (i1 + 1) = n1 then 0 else (i1 + 1), ifb (i2 + 1) = n2 then 0 else (i2 + 1))
      using S in result_skip S    
    | 2 => (* | : OR *)
      do%success (i1, i2) := (0, 0)
      for i from 0 to n - 1 do
          read%Logical x1 := s1 at i1 using S in
          read%Logical x2 := s2 at i2 using S in
          run%success
          ifb (x1 <> NA_LOGICAL /\ x1 <> 0) \/ (x2 <> NA_LOGICAL /\ x2 <> 0) then 
              write%Logical ans at i := 1 using S in
              result_skip S
          else ifb x1 = 0 /\ x2 = 0 then
              write%Logical ans at i := 0 using S in
              result_skip S
          else
              write%Logical ans at i := NA_LOGICAL using S in
              result_skip S
          using S in
          result_success S (ifb (i1 + 1) = n1 then 0 else (i1 + 1), ifb (i2 + 1) = n2 then 0 else (i2 + 1))
      using S in result_skip S
      | 3 => result_error S "Unary operator '!' called with two arguments"
      | _ => result_impossible S "binaryLogic with wrong code"
    end
    using S in
    result_success S ans.


Definition binaryLogic2 S (code : int) (s1 s2 : SEXP) : result SEXP :=
  add%stack "binaryLogic2" in
    let%success n1 := XLENGTH S s1 using S in
    let%success n2 := XLENGTH S s2 using S in
    let n := ifb n1 > n2 then n1 else n2 in
    ifb n1 = 0 \/ n2 = 0 then
        allocVector globals S RawSxp 0
    else
        result_not_implemented "Raw vector read".

Definition lunary S (call op arg : SEXP) : result SEXP :=
  add%stack "lunary" in
    
    let%success arg_isLogical := isLogical S arg using S in
    let%success arg_isNumber := isNumber globals runs S arg using S in
    let%success arg_isRaw := isRaw S arg using S in
    
    ifb ~ arg_isLogical /\ ~ arg_isNumber /\ ~ arg_isRaw then  
        result_error S "invalid argument type"
    else

    let%success len := XLENGTH S arg using S in
    let%success x :=
    ifb arg_isLogical \/ arg_isRaw then
        shallow_duplicate globals runs S arg 
    else
        let%success x := allocVector globals S (if arg_isRaw then RawSxp else LglSxp) len using S in
        let%success names := getAttrib globals runs S arg R_NamesSymbol using S in
        let%success dim := getAttrib globals runs S arg R_DimSymbol using S in
        let%success dimnames := getAttrib globals runs S arg R_DimNamesSymbol using S in
        let%success x :=
        ifb names <> R_NilValue then setAttrib globals runs S x R_NamesSymbol names else result_success S x using S in
        let%success x :=
        ifb dim <> R_NilValue then setAttrib globals runs S x R_DimSymbol dim else result_success S x using S in
        let%success x :=
        ifb dimnames <> R_NilValue then setAttrib globals runs S x R_DimNamesSymbol dimnames else result_success S x using S in
        result_success S x

     using S in
     let%success arg_type := TYPEOF S arg using S in
     run%success
     match arg_type with
     | LglSxp => do%success
                  for i from 0 to len - 1 do
                      read%Logical arg_i := arg at i using S in
                      write%Logical x at i := ifb arg_i = NA_LOGICAL then NA_LOGICAL else decide (arg_i = 0)
                      using S in result_skip S                                                                
                using S in                                                                
                result_skip S                              
     | IntSxp =>  do%success
                  for i from 0 to len - 1 do
                      read%Integer arg_i := arg at i using S in
                      write%Logical x at i := ifb arg_i = NA_INTEGER then NA_LOGICAL else decide (arg_i = 0)
                      using S in result_skip S
                 using S in                                                                
                 result_skip S
     | RealSxp => do%success
                  for i from 0 to len - 1 do
                      read%Real arg_i := arg at i using S in
                      write%Logical x at i := ifb ISNAN arg_i then NA_LOGICAL else decide (arg_i = 0%Z)
                      using S in result_skip S
                 using S in                                                                
                 result_skip S
     | CplxSxp => result_not_implemented "complex case" 
     | RawSxp => result_not_implemented "raw case"
     | _ => result_error S "UNIMPLEMENTED TYPE 'lunary'"
     end
     using S in
     result_success S x.



Definition tsConform S x y :=
  add%stack "tsConform" in
    let%success x := getAttrib globals runs S x R_TspSymbol using S in
    let%success y := getAttrib globals runs S y R_TspSymbol using S in

    ifb x <> R_NilValue /\ y <> R_NilValue then
        let%success x_type := TYPEOF S x using S in
        let%success y_type := TYPEOF S y using S in
        ifb x_type = RealSxp /\ y_type = RealSxp then
            read%Real x_0 := x at 0 using S in
            read%Real x_1 := x at 1 using S in
            read%Real x_2 := x at 2 using S in
            result_success S (decide (x_0 = x_0 /\ x_1 = x_1 /\ x_2 = x_2))
        else
            result_success S false
    else
        result_success S false.

(* logical binary : "&" or "|" *)
Definition lbinary S (call op args : SEXP) :=
  add%stack "lbinary" in
    read%list args_car, args_cdr, _ := args using S in
    read%list args_cdr_car, _, _ := args_cdr using S in
    let x := args_car in
    let y := args_cdr_car in

    let%success x_isRaw := isRaw S x using S in
    let%success y_isRaw := isRaw S y using S in
    
    let%success x_isNull := isNull S x using S in
    let%success y_isNull := isNull S y using S in
    let%success x_isNumber := isNumber globals runs S x using S in
    let%success y_isNumber := isNumber globals runs S y using S in

    (* Omitting raw type check due to empty body in if *)
    ifb ~ (x_isNull \/ x_isNumber) \/ ~ (y_isNull \/ y_isNumber) then
        result_error S "operations are possible only for numeric, logical or complex types"
    else
    let%success nx := xlength globals runs S x using S in
    let%success ny := xlength globals runs S y using S in

    let%success xarray := isArray globals runs S x using S in
    let%success yarray := isArray globals runs S y using S in

    let%success xts := isTs globals runs S x using S in
    let%success yts := isTs globals runs S y using S in

    let%success (dims, xnames, ynames) :=
    ifb xarray \/ yarray then
        let%success dims :=
        ifb xarray /\ yarray then
            let%success x_y_conformable := conformable globals runs S x y using S in
            if negb x_y_conformable then
                result_error S "non-conformable arrays"
            else
                getAttrib globals runs S x R_DimSymbol

        else ifb xarray /\ (ny <> 0 \/ nx = 0) then
            getAttrib globals runs S x R_DimSymbol  

        else ifb yarray /\ (nx <> 0 \/ ny = 0) then
            getAttrib globals runs S y R_DimSymbol

        else
            result_success S (R_NilValue : SEXP) 

        using S in
        let%success xnames := getAttrib globals runs S x R_DimNamesSymbol using S in
        let%success ynames := getAttrib globals runs S y R_DimNamesSymbol using S in
        result_success S (dims, xnames, ynames)

    else
        let dims := (R_NilValue : SEXP) in
        let%success xnames := getAttrib globals runs S x R_NamesSymbol using S in
        let%success ynames := getAttrib globals runs S y R_NamesSymbol using S in
        result_success S (dims, xnames, ynames)

    using S in
    let%success (klass, tsp) :=
    ifb xts \/ yts then
        ifb xts /\ yts then
            let%success x_y_tsConform := tsConform S x y using S in
            if negb x_y_tsConform then
                result_error S "non-conformable time series"
            else
            let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
            let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
            result_success S (klass, tsp)
        else if xts then
            ifb nx < ny then
                result_error S "TS vector mismatch"
            else
                let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
                let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
                result_success S (klass, tsp)
        else (*(yts)*)
            ifb ny < nx then
                result_error S "TS vector mismatch"
            else                        
                let%success tsp := getAttrib globals runs S y R_TspSymbol using S in
                let%success klass := getAttrib globals runs S y R_ClassSymbol using S in
                result_success S (klass, tsp)
    else  
        result_success S (NULL, NULL)

    using S in
    let%success x := 
    ifb nx > 0 /\ ny > 0 then
        (* Warning omitted *)
        
        ifb x_isRaw /\ y_isRaw then
            let%success op_primval := PRIMVAL runs S op using S in
            binaryLogic2 S op_primval x y

        else
            let%success x :=
            if x_isNull then
                let%success alloc_Vec := allocVector globals S LglSxp 0 using S in
                set%car args := alloc_Vec using S in
                result_success S alloc_Vec 
            else (* isNumeric(x) *)
                let%success coerce_Vec := coerceVector globals runs S x LglSxp using S in
                set%car args := coerce_Vec using S in
                result_success S coerce_Vec
            using S in
          
            let%success y :=
            if y_isNull then
                let%success alloc_Vec := allocVector globals S LglSxp 0 using S in
                set%car args := alloc_Vec using S in
                result_success S alloc_Vec 
            else (* isNumeric(y) *)
                let%success coerce_Vec := coerceVector globals runs S y LglSxp using S in
                set%car args_cdr := coerce_Vec using S in
                result_success S coerce_Vec
            using S in

            let%success op_primval := PRIMVAL runs S op using S in
            binaryLogic S (Z.to_nat op_primval) x y
    else  (* nx == 0 || ny == 0 *)
        allocVector globals S LglSxp 0
    using S in

    let%success x := 
    ifb dims <> R_NilValue then
        run%success setAttrib globals runs S x R_DimSymbol dims using S in
          
        ifb xnames <> R_NilValue then
            run%success setAttrib globals runs S x R_DimNamesSymbol xnames using S in
            result_success S x
        else ifb ynames <> R_NilValue then
            run%success setAttrib globals runs S x R_DimNamesSymbol ynames using S in
            result_success S x
        else
            result_success S x
    else
        let%success x_xlength := XLENGTH S x using S in
        ifb xnames <> R_NilValue then
            let%success xnames_xlength := XLENGTH S xnames using S in
            ifb x_xlength = xnames_xlength then
                run%success setAttrib globals runs S x R_NamesSymbol xnames using S in
                result_success S x
            else
                ifb ynames <> R_NilValue then  
                    let%success ynames_xlength := XLENGTH S ynames using S in
                    ifb x_xlength = ynames_xlength then
                        run%success setAttrib globals runs S x R_NamesSymbol ynames using S in
                        result_success S x
                    else
                        result_success S x
                else
                    result_success S x
        else
            ifb ynames <> R_NilValue then  
                let%success ynames_xlength := XLENGTH S ynames using S in
                ifb x_xlength = ynames_xlength then
                    run%success setAttrib globals runs S x R_NamesSymbol ynames using S in
                    result_success S x
                else
                    result_success S x
            else
                result_success S x
    using S in

    let%success x :=
    ifb xts \/ yts then
        run%success setAttrib globals runs S x R_TspSymbol tsp using S in
        run%success setAttrib globals runs S x R_ClassSymbol klass using S in
        result_success S x 
    else
        result_success S x
    using S in
    result_success S x.

End Parameterised.