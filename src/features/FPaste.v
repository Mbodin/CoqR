(** Features.FArithmetic.
  The function names of this file correspond to the function names
  in the file main/arithmetic.c. **)

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
Require Import Rcore.
Require Import FUtil.
Require Import Ascii.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition do_paste S (call op args env : SEXP) : result SEXP :=
  add%stack "do_paste" in
    let%success op_primval := PRIMVAL runs S op using S in
    let use_sep := decide (op_primval = 0) in
    
    run%success Rf_checkArityCall globals runs S op args call using S in

    (** Omitting PrintDefaults **)

    read%list args_car, args_cdr, _ := args using S in
    let x := args_car in
    let%success x_isVectorList := isVectorList S x using S in
    ifb negb x_isVectorList then
        result_error S "invalid first argument"
    else
        let%success nx := xlength globals runs S x using S in

    let%success (u_sepw, sepw, sep, collapse) :=
    if use_sep then
        result_not_implemented "do_paste use_sep check"
    else
        read%list args_cdr_car, _, _ := args_cdr using S in
        result_success S (0, 0, R_NilValue, args_cdr_car)
    using S in
  
    let%success collapse_isNull := isNull S collapse using S in
    run%success
    if negb collapse_isNull then
        let%success collapse_isString := isString S collapse using S in
        let%success collapse_length := LENGTH globals S collapse using S in
        let%success collapse_0 := STRING_ELT S collapse 0 using S in
         ifb negb collapse_isString \/ collapse_length <= 0 \/ collapse_0 = NA_STRING then
             result_error S "invalid 'collapse' argument"
         else
             result_skip S         
    else
        result_skip S
    using S in
    ifb nx = 0 then
        if negb collapse_isNull then
            let (S, res) := mkString globals S ""%string  in
            result_success S res
        else
            allocVector globals S StrSxp 0
    else

    do%success maxlen := 0
    for j from 0 to nx - 1 do
        let%success x_j := VECTOR_ELT S x j using S in
        let%success x_j_isString := isString S x_j using S in
        let%success x_j :=
        if negb x_j_isString then
            let%success x_j_object := OBJECT S x_j using S in
            let%success x_j := 
            if x_j_object then
                let%success call := lang2 globals S R_AsCharacterSymbol x_j using S in
                let%success call_eval := eval globals runs S call env using S in
                SET_VECTOR_ELT S x j call_eval 
            else if%success isSymbol S x_j using S then
                let%success x_j_printname := PRINTNAME S x_j using S in
                let%success x_j_scalarString := ScalarString globals S x_j_printname using S in
                SET_VECTOR_ELT S x j x_j_scalarString 
            else
                let%success x_j_coerce := coerceVector globals runs S x_j StrSxp using S in
                SET_VECTOR_ELT S x j x_j_coerce
            using S in
            let%success x_j_isString := isString S x_j using S in
            if negb x_j_isString then
                result_error S "non-string argument to internal 'paste'"
            else
                result_success S x_j
        else                    
            result_success S x_j
        using S in
        let%success x_j_xlength := XLENGTH S x_j using S in
        ifb x_j_xlength > maxlen then
            result_success S x_j_xlength
        else
            result_success S maxlen
    using S in

    ifb maxlen = 0 then
        if negb collapse_isNull then
            let (S, res) := mkString globals S ""%string in
            result_success S res
        else
            allocVector globals S StrSxp 0
    else

    let%success ans := allocVector globals S StrSxp maxlen using S in
    do%success
    for i from 0 to maxlen - 1 do
        
        do%success buf := ""%string 
        for j from 0 to nx - 1 do
            let%success x_j := VECTOR_ELT S x j using S in
            let%success k := XLENGTH S x_j using S in
            ifb k > 0 then
                let%success cs := STRING_ELT S x_j (i mod k) using S in
                let%success s := translateChar S cs using S in
                result_success S (buf ++ s)%string
            else
                result_success S buf
        using S in
        let (S, res) := mkChar globals S buf in
        SET_STRING_ELT S ans i res 
    using S in
    
    let%success nx := XLENGTH S ans using S in
    ifb collapse <> R_NilValue /\ nx > 0 then
        result_not_implemented "do_paste collapse check"
    else
        result_success S ans.


      
End Parameters.