(** Core.CArithmetic.
  The function names in this file correspond to the function names
  in the file main/subassign.c. **)

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
Require Import CSubscript.
Require Import CCoerce.

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


Definition SubassignTypeFix S (x y : SEXP) (stretch level : int) (call rho : SEXP) :=
  add%stack "SubassignTypeFix" in
    let redo_which := true in
    let%success x_type := TYPEOF S x using S in
    let%success y_type := TYPEOF S y using S in
    let which := 100 * (SExpType_to_nat x_type) + (SExpType_to_nat y_type) in
    let%success x_is_object := OBJECT S x using S in
    let%success (which, x, y, redo_which) :=
    match which with
    | 1000	(* logical    <- null       *)
    | 1300	(* integer    <- null       *)
    | 1400	(* real	      <- null       *)
    | 1500	(* complex    <- null       *)
    | 1600	(* character  <- null       *)
    | 1900  (* vector     <- null       *)
    | 2000  (* expression <- null       *)
    | 2400	(* raw        <- null       *)

    | 1010	(* logical    <- logical    *)
    | 1310	(* integer    <- logical    *)
    | 1410	(* real	      <- logical    *)
    | 1510	(* complex    <- logical    *)
    | 1313	(* integer    <- integer    *)
    | 1413	(* real	      <- integer    *)
    | 1513	(* complex    <- integer    *)
    | 1414	(* real	      <- real	    *)
    | 1514	(* complex    <- real	    *)
    | 1515	(* complex    <- complex    *)
    | 1616	(* character  <- character  *)
    | 1919  (* vector     <- vector     *)
    | 2020	(* expression <- expression *)
    | 2424 =>	(* raw        <- raw        *)
      result_success S (which, x, y, false)
    | 1013 =>	(* logical    <- integer    *)
      let%success x := coerceVector globals runs S x IntSxp using S in
      result_success S (which, x, y, redo_which)

    | 1014	(* logical    <- real	    *)
    | 1314 =>	(* integer    <- real	    *)
      let%success x := coerceVector globals runs S x RealSxp using S in
      result_success S (which, x, y, redo_which)

    | 1015	(* logical    <- complex    *)
    | 1315	(* integer    <- complex    *)
    | 1415 =>	(* real	      <- complex    *)
      let%success x := coerceVector globals runs S x CplxSxp using S in
      result_success S (which, x, y, redo_which)

    | 1610	(* character  <- logical    *)
    | 1613	(* character  <- integer    *)
    | 1614	(* character  <- real	    *)
    | 1615 =>	(* character  <- complex    *)
      let%success y := coerceVector globals runs S x StrSxp using S in
      result_success S (which, x, y, redo_which)

    | 1016	(* logical    <- character  *)
    | 1316	(* integer    <- character  *)
    | 1416	(* real	      <- character  *)
    | 1516 =>	(* complex    <- character  *)
       let%success x := coerceVector globals runs S x StrSxp using S in
       result_success S (which, x, y, redo_which)

    | 1901  (* vector     <- symbol   *)
    | 1902	(* vector     <- pairlist *)
    | 1904  (* vector     <- environment   *)
    | 1905  (* vector     <- promise   *)
    | 1906  (* vector     <- language   *)
    | 1910  (* vector     <- logical    *)
    | 1913  (* vector     <- integer    *)
    | 1914  (* vector     <- real       *)
    | 1915  (* vector     <- complex    *)
    | 1916  (* vector     <- character  *)
    | 1920  (* vector     <- expression  *)
    | 1921  (* vector     <- bytecode   *)
    | 1922  (* vector     <- external pointer *)
    | 1923  (* vector     <- weak reference *)
    | 1924  (* vector     <- raw *)
    | 1903 | 1907 | 1908 | 1999 => (* functions *)

       ifb level = 1 then
       (* Coerce the RHS into a list *)
           let%success y := coerceVector globals runs S x VecSxp using S in
           result_success S (which, x, y, redo_which)
       else
       (* Nothing to do here: duplicate when used (if needed) *)
	   result_success S (which, x, y, false)
	
    | 1925 => (* vector <- S4 *)
      result_not_implemented "1924 case (vector <- S4)"
	
    | 1019  (* logical    <- vector     *)
    | 1319  (* integer    <- vector     *)
    | 1419  (* real       <- vector     *)
    | 1519  (* complex    <- vector     *)
    | 1619  (* character  <- vector     *)
    | 2419 =>  (* raw        <- vector     *)
      let%success x := coerceVector globals runs S x VecSxp using S in
      result_success S (which, x, y, redo_which)

    | 1020  (* logical    <- expression *)
    | 1320  (* integer    <- expression *)
    | 1420  (* real       <- expression *)
    | 1520  (* complex    <- expression *)
    | 1620  (* character  <- expression *)
    | 2420 =>  (* raw        <- expression *)
      let%success x := coerceVector globals runs S x ExprSxp using S in
      result_success S (which, x, y, redo_which)

    | 2001	(* expression <- symbol	    *)
    | 2002  (* expression <- pairlist   *)
    | 2006	(* expression <- language   *)
    | 2010	(* expression <- logical    *)
    | 2013	(* expression <- integer    *)
    | 2014	(* expression <- real	    *)
    | 2015	(* expression <- complex    *)
    | 2016	(* expression <- character  *)
    | 2019 => (* expression <- vector     *)

      ifb level = 1 then
       (* Coerce the RHS into a list *)
           let%success y := coerceVector globals runs S x VecSxp using S in
           result_success S (which, x, y, redo_which)
       else
       (* Nothing to do here: duplicate when used (if needed) *)
	   result_success S (which, x, y, false)

    | 2025 => (* expression <- S4 *)
      result_not_implemented "case 2025 (expression <- S4)"

    | 1025 (* logical   <- S4 *)
    | 1325 (* integer   <- S4 *)
    | 1425 (* real      <- S4 *)
    | 1525 (* complex   <- S4 *)
    | 1625 (* character <- S4 *)
    | 2425 => (* raw       <- S4 *)
      result_not_implemented "case 2425 (raw <- S4)"

    | _ => result_error S "incompatible types in subassignment type fix"
    end
    using S in
    let%success x :=
    ifb stretch <> 0 then
        unimplemented_function "EnlargeVector"
    else result_success S x using S in
    run%success SET_OBJECT S x x_is_object using S in

    if redo_which then
        let%success x_type := TYPEOF S x using S in
        let%success y_type := TYPEOF S y using S in 
	result_success S (100 * (SExpType_to_nat x_type) + (SExpType_to_nat y_type), x, y)
    else
	result_success S (which, x, y) .


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
    let%success (indx, stretch) := makeSubscript globals runs S x s R_NilValue using S in
    let%success n := xlength using S in
    let%success y_xlength := xlength using S in
    run%success
    ifb then

    else
        result_skip S
    using S in

    let%success (which, x, y) := SubassignTypeFix



.

Definition MatrixAssign (S : state) (call rho x s y : SEXP) : result SEXP :=
  add%stack "MatrixAssign" in
    result_not_implemented "MatrixAssign".

Definition ArrayAssign (S : state) (call rho x s y : SEXP) : result SEXP :=
  add%stack "ArrayAssign" in
    result_not_implemented "ArrayAssign".

End Parameterised.
