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
From Lib Require Import Double.
From CoqR Require Import Loops.
Require Import CRinternals.
Require Import CRinlinedfuns.
Require Import CArithmetic.
Require Import CAttrib.
Require Import CDuplicate.
Require Import Conflicts.
Require Import CSubscript.
Require Import CCoerce.
Require Import CMemory.

Section Parameterised.

(** Global Variables **)

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

(** ** util.c **)

(** The following function correspond to the function name
  in the file src/util.c. **)

(** Included to remove circular dependency **)

Definition ncols s :=
  add%stack "ncols" in
    let%success s_vec := isVector s in
    let%success s_list := isList globals s in
    ifb s_vec \/ s_list then
      let%success t := getAttrib globals runs s R_DimSymbol in
      ifb t = R_NilValue then
        result_success 1%Z
      else
        let%success t_len := LENGTH globals t in
        ifb t_len >= 2 then
          read%Integer r := t at 1 in
          result_success r
        else result_success 1%Z
    else if%success isFrame globals runs s then
      let%success r := R_length globals runs s in
      result_success (r : int)
         else result_error "Object is not a matrix.".


Definition SubassignTypeFix (x y : SEXP) (stretch level : int) (call rho : SEXP) :=
  add%stack "SubassignTypeFix" in
    let redo_which := true in
    let%success x_type := TYPEOF x in
    let%success y_type := TYPEOF y in
    let which := 100 * (SExpType_to_nat x_type) + (SExpType_to_nat y_type) in
    let%success x_is_object := OBJECT x in
    let%success (which, x, y, redo_which) :=
    match which : int with
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
      result_success (which, x, y, false)
    | 1013 =>	(* logical    <- integer    *)
      let%success x := coerceVector globals runs x IntSxp in
      result_success (which, x, y, redo_which)

    | 1014	(* logical    <- real	    *)
    | 1314 =>	(* integer    <- real	    *)
      let%success x := coerceVector globals runs x RealSxp in
      result_success (which, x, y, redo_which)

    | 1015	(* logical    <- complex    *)
    | 1315	(* integer    <- complex    *)
    | 1415 =>	(* real	      <- complex    *)
      let%success x := coerceVector globals runs x CplxSxp in
      result_success (which, x, y, redo_which)

    | 1610	(* character  <- logical    *)
    | 1613	(* character  <- integer    *)
    | 1614	(* character  <- real	    *)
    | 1615 =>	(* character  <- complex    *)
      let%success y := coerceVector globals runs x StrSxp in
      result_success (which, x, y, redo_which)

    | 1016	(* logical    <- character  *)
    | 1316	(* integer    <- character  *)
    | 1416	(* real	      <- character  *)
    | 1516 =>	(* complex    <- character  *)
       let%success x := coerceVector globals runs x StrSxp in
       result_success (which, x, y, redo_which)

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
           let%success y := coerceVector globals runs x VecSxp in
           result_success (which, x, y, redo_which)
       else
       (* Nothing to do here: duplicate when used (if needed) *)
	   result_success (which, x, y, false)

    | 1925 => (* vector <- S4 *)
      result_not_implemented "1924 case (vector <- S4)"

    | 1019  (* logical    <- vector     *)
    | 1319  (* integer    <- vector     *)
    | 1419  (* real       <- vector     *)
    | 1519  (* complex    <- vector     *)
    | 1619  (* character  <- vector     *)
    | 2419 =>  (* raw        <- vector     *)
      let%success x := coerceVector globals runs x VecSxp in
      result_success (which, x, y, redo_which)

    | 1020  (* logical    <- expression *)
    | 1320  (* integer    <- expression *)
    | 1420  (* real       <- expression *)
    | 1520  (* complex    <- expression *)
    | 1620  (* character  <- expression *)
    | 2420 =>  (* raw        <- expression *)
      let%success x := coerceVector globals runs x ExprSxp in
      result_success (which, x, y, redo_which)

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
           let%success y := coerceVector globals runs x VecSxp in
           result_success (which, x, y, redo_which)
       else
       (* Nothing to do here: duplicate when used (if needed) *)
	   result_success (which, x, y, false)

    | 2025 => (* expression <- S4 *)
      result_not_implemented "case 2025 (expression <- S4)"

    | 1025 (* logical   <- S4 *)
    | 1325 (* integer   <- S4 *)
    | 1425 (* real      <- S4 *)
    | 1525 (* complex   <- S4 *)
    | 1625 (* character <- S4 *)
    | 2425 => (* raw       <- S4 *)
      result_not_implemented "case 2425 (raw <- S4)"

    | _ => result_error "incompatible types in subassignment type fix"
    end%Z
    in
    let%success x :=
    ifb stretch <> 0 then
        unimplemented_function "EnlargeVector"
    else result_success x in
    run%success SET_OBJECT x x_is_object in

    if redo_which then
        let%success x_type := TYPEOF x in
        let%success y_type := TYPEOF y in
	result_success (100 * (SExpType_to_nat x_type) + (SExpType_to_nat y_type), x, y)
    else
	result_success (which, x, y) .


Definition SubAssignArgs (args : SEXP) :=
  add%stack "SubAssignArgs" in
    read%list args_car, args_cdr, _ := args in
    ifb args_cdr = R_NilValue then
        result_error "SubAssignArgs: invalid number of arguments"
    else
    let x := args_car in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr in
    ifb args_cdr_cdr = R_NilValue then
        result_success (0, x, (R_NilValue : SEXP), args_cdr_car)
    else
        let nsubs := 1 in
        let s := args_cdr in
        do%success (p, nsubs) := (args_cdr, nsubs)
        while read%list _, p_cdr, _ := p in
              read%list _, p_cdr_cdr, _ := p_cdr in
              result_success (decide (p_cdr_cdr <> R_NilValue))
        do
            read%list _, p_cdr, _ := p in
            result_success (p_cdr, nsubs + 1)
        using runs in
        read%list _, p_cdr, _ := p in
        read%list p_cdr_car, _, _ := p_cdr in
        let y := p_cdr_car in
        set%cdr p := R_NilValue in
        result_success (nsubs, x, s, y).

Definition R_SHORT_LEN_MAX := INT_MAX.

Definition gi indx i :=
  add%stack "gi" in
    let%success indx_type := TYPEOF indx in
    ifb indx_type = RealSxp then
        let%success d := REAL_ELT indx i in
        ifb negb (R_FINITE d) \/ d < -R_SHORT_LEN_MAX \/ d > R_SHORT_LEN_MAX then
            result_success NA_INTEGER
        else
            result_success (Double.double_to_int_zero d)
    else
        let%success indx_i := INTEGER_ELT indx i in
        result_success indx_i.


Definition VECTOR_ASSIGN_LOOP indx n ny (CODE : nat -> nat -> result unit) :=
  add%stack "VECTOR_ASSIGN_LOOP" in
    let%success indx_type := TYPEOF indx in
    ifb indx_type = IntSxp then
        do%let iny := 0
        for i from 0 to n - 1 do
            read%Integer ii := indx at i in
            ifb ii = NA_INTEGER then
                result_success (ifb (iny + 1 = ny) then 0 else iny)
            else
            let ii := Z.to_nat ii - 1 in
            run%success CODE iny ii in
            result_success (ifb (iny + 1 = ny) then 0 else iny)

    else
        do%let iny := 0
        for i from 0 to n - 1 do
            let%success ii := gi indx i in
            ifb ii = NA_INTEGER then
                result_success (ifb (iny + 1 = ny) then 0 else iny)
            else
            let ii := Z.to_nat ii - 1 in
            run%success CODE iny ii in
            result_success (ifb (iny + 1 = ny) then 0 else iny).

Definition VectorAssign (call rho x s y : SEXP) :=
  add%stack "VectorAssign" in
    (* try for quick return for simple scalar case *)
    let%success s_attrib := ATTRIB s in

    run%exit
    ifb s_attrib = R_NilValue then
        let%success x_type := TYPEOF x in
        let%success y_isScalar := IS_SCALAR y RealSxp in

        ifb x_type = RealSxp /\ y_isScalar then
            let%success s_isScalar := IS_SCALAR s IntSxp in
            if s_isScalar then
                let%success ival := SCALAR_IVAL s in
                let%success x_xlength := XLENGTH x in
                ifb 1%Z <= ival /\ ival <= x_xlength then
                    let%success y_dval := SCALAR_DVAL y in
                    write%Real x at (Z.to_nat(ival) - 1) := y_dval in
                    result_rreturn x
                else
                    result_rskip
            else
                let%success s_isScalar := IS_SCALAR s RealSxp in
                if s_isScalar then
                    let%success dval := SCALAR_DVAL s in
                    if R_FINITE dval then
                        let ival := dval in
                        let%success x_xlength := XLENGTH x in
                        ifb 1%Z <= Double.double_to_int_zero ival /\ ival <= x_xlength then
                            let%success y_dval := SCALAR_DVAL y in
                            write%Real x at (Z.to_nat(Double.double_to_int_zero ival) - 1) := y_dval in
                                result_rreturn x
                        else
                            result_rskip
                    else
                        result_rskip
                else
                    result_rskip
        else
            result_rskip
    else
        result_rskip
    in

    let%success x_isNull := isNull x in
    let%success y_isNull := isNull y in
    ifb x_isNull /\ y_isNull then
        result_success (R_NilValue : SEXP)
    else


    (* Check to see if we have special matrix subscripting.
       If so, we manufacture a real subscript vector. *)

    let%success s :=
    ifb s_attrib <> R_NilValue then
        let%success dim := getAttrib globals runs x R_DimSymbol in
        let%success s_isMatrix := isMatrix globals runs s in
        let%success x_isArray := isArray globals runs x in

        ifb s_isMatrix /\ x_isArray then
          let%success s_ncols := ncols s in
          let%success dim_length := R_length globals runs dim in

          ifb s_ncols = dim_length then
              let%success s_isString := isString s in
              let%success s :=
              if s_isString then
                  let%success dnames := GetArrayDimnames globals runs x in
                  unimplemented_function "strmat2intmat"
              else result_success s
              in

              let%success s_isInteger := isInteger globals runs s in
              let%success s_isReal := isReal s in
              ifb s_isInteger \/ s_isReal then
                  unimplemented_function "mat2indsub"

              else
                  result_success s
          else
              result_success s

        else
            result_success s
    else
        result_success s
    in

    let stretch := 1 in
    let%success (indx, stretch) := makeSubscript globals runs x s stretch R_NilValue in
    let%success n := xlength globals runs indx in
    let%success y_xlength := xlength globals runs y in
    run%success
    ifb y_xlength > 1 then
        do%success
        for i from 0 to n - 1 do
            let%success indx_gi := gi indx i in
            ifb indx_gi = NA_INTEGER then
                result_error "NAs are not allowed in subscripted assignments"
            else
                result_skip
        in result_skip
    else
        result_skip
    in

    (* Here we make sure that the LHS has
       been coerced into a form which can
       accept elements from the RHS. *)
    let%success (which, x, y) := SubassignTypeFix x y stretch 1 call rho in
    (* which = 100 * TYPEOF(x) + TYPEOF(y) *)
    ifb n = 0 then
        result_success x
    else
    let%success ny := xlength globals runs y in
    let%success nx := xlength globals runs x in

    run%success
    let%success x_type := TYPEOF x in
    ifb (x_type <> VecSxp /\ x_type <> ExprSxp) \/ y <> R_NilValue then
        ifb n > 0 /\ ny = 0 then
            result_error "replacement has length zero"
        else
            (* Omitting warning *)
            result_skip
    else result_skip
    in

    let%success y :=
    ifb x = y then
        shallow_duplicate globals runs y
    else result_success y
    in

    run%success
    match which : int with
    | 1010 	(* logical   <- logical	  *)
    | 1310 	(* integer   <- logical	  *)
    (* case 1013:  logical   <- integer	  *)
    | 1313 =>	(* integer   <- integer	  *)
      run%success
      let code iny ii :=
          let%success y_iny := INTEGER_ELT y iny in
          write%Integer x at ii := y_iny in result_skip
      in
      VECTOR_ASSIGN_LOOP indx n ny code
      in result_skip
    | 1410 	(* real	     <- logical	  *)
    | 1413 =>	(* real	     <- integer	  *)
      run%success
      let code iny ii :=
          let%success iy := INTEGER_ELT y iny in
          ifb iy = NA_INTEGER then
              write%Real x at ii := NA_REAL in result_skip
          else
              write%Real x at ii := iy in result_skip
      in
      VECTOR_ASSIGN_LOOP indx n ny code
      in result_skip
    (* case 1014:  logical   <- real	  *)
    (* case 1314:  integer   <- real	  *)
    | 1414 =>	(* real	     <- real	  *)
      run%success
      let code iny ii :=
          let%success y_iny := REAL_ELT y iny in
          write%Real x at ii := y_iny in result_skip
      in
      VECTOR_ASSIGN_LOOP indx n ny code
      in result_skip


    | 1510	(* complex   <- logical	  *)
    | 1513 =>	(* complex   <- integer	  *)
      result_not_implemented "case 1513 (complex <- integer)"


    | 1514 =>	(* complex   <- real	  *)
      result_not_implemented "case 1514 (complex <- real)"
    (* case 1015:  logical   <- complex	  *)
    (* case 1315:  integer   <- complex	  *)
    (* case 1415:  real	     <- complex	  *)
    | 1515 => 	(* complex   <- complex	  *)
      result_not_implemented "case 1515 (complex <- complex)"
    | 1610 	(* character <- logical	  *)
    | 1613 	(* character <- integer	  *)
    | 1614 	(* character <- real	  *)
    | 1615 	(* character <- complex	  *)
    | 1616 =>	(* character <- character *)
    (* case 1016:  logical   <- character *)
    (* case 1316:  integer   <- character *)
    (* case 1416:  real	     <- character *)
    (* case 1516:  complex   <- character *)
      result_not_implemented "case 1616 (character <- character)"

    (* case 1019:  logial     <- vector   *)
    (* case 1319:  integer    <- vector   *)
    (* case 1419:  real       <- vector   *)
    (* case 1519:  complex    <- vector   *)
    (* case 1619:  character  <- vector   *)

    (* case 1910:  vector     <- logical    *)
    (* case 1913:  vector     <- integer    *)
    (* case 1914:  vector     <- real       *)
    (* case 1915:  vector     <- complex    *)
    (* case 1916:  vector     <- character  *)

    | 1919 =>  (* vector     <- vector     *)
      result_not_implemented "case 1919 (vector <- vector)"

    (* case 2001: *)
    (* case 2006:  expression <- language   *)
    (* case 2010:  expression <- logical    *)
    (* case 2013:  expression <- integer    *)
    (* case 2014:  expression <- real	    *)
    (* case 2015:  expression <- complex    *)
    (* case 2016:  expression <- character  *)
    | 2019 	(* expression <- vector, needed if we have promoted a
		   RHS  to a list *)
    | 2020 =>	(* expression <- expression *)
      result_not_implemented "case 2020 (expression <- expression)"
    | 1900   (* vector     <- null       *)
    | 2000 =>  (* expression <- null       *)
      result_not_implemented "case 2000 (expression <- null)"
    | 2424 =>	(* raw   <- raw	  *)
      result_not_implemented "case 2424 (raw <- raw)"
    | _ => result_skip

    end%Z
    in

    let%success newnames := getAttrib globals runs indx R_UseNamesSymbol in
    run%success
    ifb newnames <> R_NilValue then
        let%success oldnames := getAttrib globals runs x R_NamesSymbol in
        ifb oldnames <> R_NilValue then
            do%success
            for i from 0 to n - 1 do
                let%success newnames_i := VECTOR_ELT newnames i in
                ifb newnames_i <> R_NilValue then
                    let%success ii := gi indx i in
                    ifb ii = NA_INTEGER then
                        result_skip
                    else
                        SET_STRING_ELT oldnames (Z.to_nat ii) newnames_i
                else result_skip
            in result_skip
        else
            let%success oldnames := allocVector globals StrSxp nx in
            do%success
            for i from 0 to nx - 1 do
                SET_STRING_ELT oldnames i R_BlankString
            in

            do%success
            for i from 0 to n - 1 do
                let%success newnames_i := VECTOR_ELT newnames i in
                ifb newnames_i <> R_NilValue then
                    let%success ii := gi indx i in
                    ifb ii = NA_INTEGER then result_skip
                    else
                    let ii := (Z.to_nat ii) - 1 in
                    SET_STRING_ELT oldnames (Z.to_nat ii) newnames_i
                 else
                     result_skip
            in result_skip
    else result_skip
    in result_success x.

Definition MatrixAssign (call rho x s y : SEXP) : result_SEXP :=
  add%stack "MatrixAssign" in
    result_not_implemented "MatrixAssign".

Definition ArrayAssign (call rho x s y : SEXP) : result_SEXP :=
  add%stack "ArrayAssign" in
    result_not_implemented "ArrayAssign".

End Parameterised.
