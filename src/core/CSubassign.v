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
Require Import CArithmetic.
Require Import CAttrib.
Require Import CDuplicate.
Require Import Conflicts.

Section Parameterised.

(** Global Variables **)

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

(** ** util.c **)

(** The following function correspond to the function name
  in the file src/util.c. **)

(** Included to remove circular dependency **)

Definition ncols S s :=
  add%stack "ncols" in
    let%success s_vec := isVector S s using S in
    let%success s_list := isList globals S s using S in
    ifb s_vec \/ s_list then
      let%success t := getAttrib globals runs S s R_DimSymbol using S in
      ifb t = R_NilValue then
        result_success S 1%Z
      else
        let%success t_len := LENGTH globals S t using S in
        ifb t_len >= 2 then
          read%Integer r := t at 1 using S in
          result_success S r
        else result_success S 1%Z
    else if%success isFrame globals runs S s using S then
      let%success r := R_length globals runs S s using S in
      result_success S (r : int)
         else result_error S "Object is not a matrix.".

Definition SubAssignArgs S (args : SEXP) :=
  add%stack "SubAssignArgs" in
    read%list args_car, args_cdr, _ := args using S in
    ifb args_cdr = R_NilValue then
        result_error S "SubAssignArgs: invalid number of arguments"
    else
    let x := args_car in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
    ifb args_cdr_cdr = R_NilValue then
        result_success S (0, x, (R_NilValue : SEXP), args_cdr_car)
    else
        let nsubs := 1 in
        let s := args_cdr in
        do%success (p, nsubs) := (args_cdr, nsubs) 
        while read%list _, p_cdr, _ := p using S in
              read%list _, p_cdr_cdr, _ := p_cdr using S in
              result_success S (decide (p_cdr_cdr <> R_NilValue))
        do
            read%list _, p_cdr, _ := p using S in
            result_success S (p_cdr, nsubs + 1)
        using S, runs in                                                   
        read%list _, p_cdr, _ := p using S in
        read%list p_cdr_car, _, _ := p_cdr using S in                                  
        let y := p_cdr_car in
        set%cdr p := R_NilValue using S in                            
        result_success S (nsubs, x, s, y).

Definition VectorAssign S (call rho x s y : SEXP) :=
  add%stack "VectorAssign" in
    (* try for quick return for simple scalar case *)
    let%success s_attrib := ATTRIB S s using S in

    run%exit
    ifb s_attrib = R_NilValue then
        let%success x_type := TYPEOF S x using S in
        let%success y_isScalar := IS_SCALAR S y RealSxp using S in

        ifb x_type = RealSxp /\ y_isScalar then
            let%success s_isScalar := IS_SCALAR S s IntSxp using S in
            if s_isScalar then
                let%success ival := SCALAR_IVAL S s using S in
                let%success x_xlength := XLENGTH S x using S in
                ifb 1%Z <= ival /\ ival <= x_xlength then
                    let%success y_dval := SCALAR_DVAL S y using S in
                    write%Real x at (Z.to_nat(ival) - 1) := y_dval using S in
                    result_rreturn S x
                else
                    result_rskip S
            else
                let%success s_isScalar := IS_SCALAR S s RealSxp using S in
                if s_isScalar then
                    let%success dval := SCALAR_DVAL S s using S in
                    let%success x_xlength := XLENGTH S x using S in
                    if R_FINITE dval then
                        let ival := dval in
                        ifb 1%Z <= Double.double_to_int_zero ival /\ ival <= x_xlength then
                            let%success y_dval := SCALAR_DVAL S y using S in
                            write%Real x at (Z.to_nat(Double.double_to_int_zero ival) - 1) := y_dval using S in
                                result_rreturn S x
                        else
                            result_rskip S
                    else
                        result_rskip S
                else   
                    result_rskip S
        else
            result_rskip S
    else
        result_rskip S
    using S in 
    
    let%success x_isNull := isNull S x using S in
    let%success y_isNull := isNull S y using S in
    ifb x_isNull /\ y_isNull then
        result_success S (R_NilValue : SEXP)
    else
                       

    (* Check to see if we have special matrix subscripting.   
       If so, we manufacture a real subscript vector. *)

    let%success s :=
    ifb s_attrib <> R_NilValue then
        let%success dim := getAttrib globals runs S x R_DimSymbol using S in
        let%success s_isMatrix := isMatrix globals runs S s using S in
        let%success x_isArray := isArray globals runs S x using S in
        
        ifb s_isMatrix /\ x_isArray then
          let%success s_ncols := ncols S s using S in
          let%success dim_length := R_length globals runs S dim using S in

          ifb s_ncols = dim_length then
              let%success s_isString := isString S s using S in
              let%success s :=
              if s_isString then
                  let%success dnames := GetArrayDimnames globals runs S x using S in
                  unimplemented_function "strmat2intmat"
              else result_success S s
              using S in

              let%success s_isInteger := isInteger globals runs S s using S in
              let%success s_isReal := isReal S s using S in
              ifb s_isInteger \/ s_isReal then
                  unimplemented_function "mat2indsub"
                
              else
                  result_success S s
          else
              result_success S s
            
        else
            result_success S s
    else
        result_success S s
    using S in

    let stretch := 1 in
    unimplemented_function "makeSubscript".

Definition MatrixAssign (S : state) (call rho x s y : SEXP) : result SEXP :=
  add%stack "MatrixAssign" in
    result_not_implemented "MatrixAssign".

Definition ArrayAssign (S : state) (call rho x s y : SEXP) : result SEXP :=
  add%stack "ArrayAssign" in
    result_not_implemented "ArrayAssign".

End Parameterised.