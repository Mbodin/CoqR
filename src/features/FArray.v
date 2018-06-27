(** Features.FArray.
  The function names of this file correspond to the function names
  in the file main/array.c. **)

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
Require Import FUtil.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.



Definition xcopyWithRecycle {A B} (GETELT : state -> SEXP -> nat -> result B) (SETELT : state -> SEXP -> nat -> B -> result A) S (dst src : SEXP) (dstart n nsrc : int) :=
  add%stack "xcopyWithRecycle_1" in
    ifb nsrc >= n then
        do%success 
        for i from 0 to n - 1 do
            let%success src_i := GETELT S src i using S in                  
            run%success SETELT S dst (Z.to_nat dstart + i) src_i using S in result_skip S
        using S in result_skip S
    else
    ifb nsrc = 1 then
        let%success val := GETELT S src 0 using S in
        do%success 
        for i from 0 to n - 1 do
            run%success SETELT S dst (Z.to_nat dstart + i) val using S in result_skip S            
        using S in result_skip S    
    else
        let sidx := 0%Z in
        do%success sidx := sidx
        for i from 0 to n - 1 do                    
            let sidx := ifb sidx = nsrc then 0%Z else sidx in                  
            let%success src_sidx := GETELT S src (Z.to_nat sidx) using S in
            run%success SETELT S dst (Z.to_nat dstart + i) src_sidx using S in
            result_success S sidx
        using S in result_skip S.

    


Definition copyVector S (s t : SEXP) :=
  add%stack "copyVector" in
    let%success sT := TYPEOF S s using S in
    let%success tT := TYPEOF S t using S in
    ifb sT <> tT then
        result_error S "vector types do not match in copyVector"
    else
    let%success ns := XLENGTH S s using S in  
    let%success nt := XLENGTH S t using S in
    match sT with
    | StrSxp => xcopyWithRecycle STRING_ELT SET_STRING_ELT S s t 0 ns nt
    | LglSxp =>
      let GETELT S src i :=
          read%Logical src_i := src at i using S in
          result_success S src_i
      in
      let SETELT S dst i val :=
          write%Logical dst at i := val using S in
          result_skip S
      in
      xcopyWithRecycle GETELT SETELT S s t 0 ns nt
      
    | IntSxp =>
      let GETELT S src i :=
          read%Integer src_i := src at i using S in
          result_success S src_i
      in
      let SETELT S dst i val :=
          write%Integer dst at i := val using S in
          result_skip S
      in
      xcopyWithRecycle GETELT SETELT S s t 0 ns nt
    | RealSxp =>
      let GETELT S src i :=
          read%Real src_i := src at i using S in
          result_success S src_i
      in
      let SETELT S dst i val :=
          write%Real dst at i := val using S in
          result_skip S
      in
      xcopyWithRecycle GETELT SETELT S s t 0 ns nt
    | CplxSxp =>
      let GETELT S src i :=
          read%Complex src_i := src at i using S in
          result_success S src_i
      in
      let SETELT S dst i val :=
          write%Complex dst at i := val using S in
          result_skip S
      in
      xcopyWithRecycle GETELT SETELT S s t 0 ns nt
    | ExprSxp
    | VecSxp => xcopyWithRecycle VECTOR_ELT SET_VECTOR_ELT S s t 0 ns nt
    | RawSxp => result_not_implemented "Raw case"
    | _ => result_error S "unimplemented type for copyVector"
    end.

    
    
Definition copyMatrix S (s t : SEXP) byrow :=
  add%stack "copyMatrix" in
    let%success nr := nrows globals runs S s using S in
    let%success nc := ncols globals runs S s using S in
    let%success nt := XLENGTH S t using S in

    ifb byrow <> 0 then
      let%success s_type := TYPEOF S s using S in
      match s_type with
      | StrSxp =>
        do%success sidx := 0
        for i from 0 to nr - 1 do
            do%success (sidx, didx) := (sidx, i)                     
            for j from 0 to nc - 1 do
                let%success t_sidx := STRING_ELT S t sidx using S in                   
                run%success SET_STRING_ELT S s didx t_sidx using S in
                let sidx := ifb sidx >= nt then sidx + 1 - nt else sidx + 1 in
            result_success S (sidx, didx +  nr)
            using S in               
            result_success S sidx
        using S in result_skip S                   
    | LglSxp =>
      do%success sidx := 0
        for i from 0 to nr - 1 do
            do%success (sidx, didx) := (sidx, i)                     
            for j from 0 to nc - 1 do
                read%Logical t_sidx := t at sidx using S in                   
                write%Logical s at didx := t_sidx using S in
                let sidx := ifb sidx >= nt then sidx + 1 - nt else sidx + 1 in
            result_success S (sidx, didx +  nr)
            using S in               
            result_success S sidx
      using S in result_skip S                     
    | IntSxp =>
      do%success sidx := 0
        for i from 0 to nr - 1 do
            do%success (sidx, didx) := (sidx, i)                     
            for j from 0 to nc - 1 do
                read%Integer t_sidx := t at sidx using S in                   
                write%Integer s at didx := t_sidx using S in
                let sidx := ifb sidx >= nt then sidx + 1 - nt else sidx + 1 in
            result_success S (sidx, didx +  nr)
            using S in               
            result_success S sidx
      using S in result_skip S                     
    | RealSxp =>
      do%success sidx := 0
        for i from 0 to nr - 1 do
            do%success (sidx, didx) := (sidx, i)                     
            for j from 0 to nc - 1 do
                read%Real t_sidx := t at sidx using S in                   
                write%Real s at didx := t_sidx using S in
                let sidx := ifb sidx >= nt then sidx + 1 - nt else sidx + 1 in
            result_success S (sidx, didx +  nr)
            using S in               
            result_success S sidx
      using S in result_skip S                     
    | CplxSxp =>
      do%success sidx := 0
        for i from 0 to nr - 1 do
            do%success (sidx, didx) := (sidx, i)                     
            for j from 0 to nc - 1 do
                read%Complex t_sidx := t at sidx using S in                   
                write%Complex s at didx := t_sidx using S in
                let sidx := ifb sidx >= nt then sidx + 1 - nt else sidx + 1 in
            result_success S (sidx, didx +  nr)
            using S in               
            result_success S sidx
      using S in result_skip S                     
    | ExprSxp
    | VecSxp =>
      do%success sidx := 0
        for i from 0 to nr - 1 do
            do%success (sidx, didx) := (sidx, i)                     
            for j from 0 to nc - 1 do
                let%success t_sidx := VECTOR_ELT S t sidx using S in                   
                run%success SET_VECTOR_ELT S s didx t_sidx using S in
                let sidx := ifb sidx >= nt then sidx + 1 - nt else sidx + 1 in
            result_success S (sidx, didx +  nr)
            using S in               
            result_success S sidx  
      using S in result_skip S                     
    | RawSxp => result_not_implemented "Raw case"
    | _ => result_error S "unimplemented type in copyMatrix"
      end
       
    else
        copyVector S s t.  
    
  
Definition do_matrix S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_matrix" in
    let nr := 1%Z in
    let nc := 1%Z in
    run%success Rf_checkArityCall globals runs S op args call using S in
    read%list args_car, args_cdr, _ := args using S in
    let vals := args_car in
    let args := args_cdr in
    let%success vals_type := TYPEOF S vals using S in
    run%success
    match vals_type with
    | LglSxp
    | IntSxp
    | RealSxp
    | CplxSxp
    | StrSxp
    | RawSxp
    | ExprSxp
    | VecSxp => result_skip S
    | _ => result_error S "'data' must be of a vector type"
    end
    using S in
    let%success lendat := XLENGTH S vals using S in
    read%list args_car, args_cdr, _ := args using S in
    let snr := args_car in
    let args := args_cdr in
    read%list args_car, args_cdr, _ := args using S in
    let snc := args_car in
    let args := args_cdr in
    read%list args_car, args_cdr, _ := args using S in
    let%success byrow := asLogical globals S args_car using S in
    let args := args_cdr in
    ifb byrow = NA_INTEGER then
        result_error S "invalid 'byrow' argument"
    else
    read%list args_car, args_cdr, _ := args using S in
    let dimnames := args_car in
    let args := args_cdr in
    read%list args_car, args_cdr, _ := args using S in
    let%success miss_nr := asLogical globals S args_car using S in
    let args := args_cdr in
    read%list args_car, _, _ := args using S in
    let%success miss_nc := asLogical globals S args_car using S in                                        
    let%success nr :=
    ifb miss_nr = 0 then
        let%success snr_isNumeric := isNumeric globals runs S snr using S in
        if negb snr_isNumeric then
            result_error S "non-numeric matrix extent"
        else
        let%success nr := asInteger globals S snr using S in  
        ifb nr = NA_INTEGER then 
            result_error S "invalid 'nrow' value (too large or NA)"
        else
        ifb nr < 0 then
            result_error S "invalid 'nrow' value (< 0)"
        else
            result_success S (nr : int)
    else
        result_success S (nr : int)
    using S in

    let%success nc :=
    ifb miss_nc = 0 then
        let%success snc_isNumeric := isNumeric globals runs S snc using S in
        if negb snc_isNumeric then
            result_error S "non-numeric matrix extent"
        else
        let%success nc := asInteger globals S snc using S in  
        ifb nc = NA_INTEGER then 
            result_error S "invalid 'ncol' value (too large or NA)"
        else
        ifb nc < 0 then
            result_error S "invalid 'ncol' value (< 0)"
        else
            result_success S nc
    else
        result_success S (nc : int)
    using S in

    let%success (nr, nc) :=
    ifb miss_nr <> 0 /\ miss_nc <> 0 then
        ifb (lendat : int) > INT_MAX then
            result_error S "data is too long"
        else
            result_success S (lendat : int, nc : int)
    else ifb miss_nr <> 0 then
        ifb (lendat : double) > Double.mult (nc : double) (INT_MAX : double) then
            result_error S "data is too long"
        else
        ifb nc = 0 then
            ifb lendat <> 0 then 
                result_error S "nc = 0 for non-null data"
            else
                result_success S (0%Z, nc)
        else
            result_success S (Double.double_to_int_zero (Double.ceil (Double.div (lendat : double) (nc : double))), nc)
    else ifb miss_nc <> 0 then
        ifb (lendat : double) > Double.mult (nr : double) (INT_MAX : double) then
            result_error S "data is too long"
        else
        ifb nr = 0 then
            ifb lendat <> 0 then 
                result_error S "nc = 0 for non-null data"
            else
                result_success S (nr, 0%Z)
        else
            result_success S (nr, (Double.double_to_int_zero (Double.ceil (Double.div (lendat : double) (nr : double)))))
    else
        result_success S (nr, nc)
    using S in

    (* Omitting warnings *)
    let%success ans := allocMatrix globals runs S vals_type (Z.to_nat nr) (Z.to_nat nc) using S in 
    run%success
    let%success vals_isVector := isVector S vals using S in
    ifb lendat <> 0 then
        if vals_isVector then
            copyMatrix S ans vals (Z.to_nat byrow)
        else
            unimplemented_function "copyListMatrix"
    else if vals_isVector then (* fill with NAs *) 
        let N := (Z.to_nat nr) * (Z.to_nat nc) in
        match vals_type with
        | StrSxp =>
          do%success
          for i from 0 to N - 1 do
              SET_STRING_ELT S ans i NA_STRING     
          using S in result_skip S                             

        | LglSxp =>
          do%success
          for i from 0 to N - 1 do
              write%Logical ans at i := NA_LOGICAL using S in result_skip S     
          using S in result_skip S
        | IntSxp =>
          do%success
          for i from 0 to N - 1 do
              write%Integer ans at i := NA_INTEGER using S in result_skip S     
          using S in result_skip S
        | RealSxp =>
          do%success
          for i from 0 to N - 1 do
              write%Real ans at i := NA_REAL using S in result_skip S     
          using S in result_skip S
        | CplxSxp => result_not_implemented "Complex case"
        | RawSxp => result_not_implemented "Raw case"
        | _ => result_skip S
        end
        
    else
        result_skip S
    using S in
    let%success dimnames_isNull := isNull S dimnames using S in
    let%success ans :=
    ifb negb dimnames_isNull then
        let%success dimnames_length := R_length globals runs S dimnames using S in
        ifb dimnames_length > 0 then
            unimplemented_function "dimnames"
        else
            result_success S ans
    else
        result_success S ans
    using S in
    result_success S ans.

Definition do_length S (call op args env : SEXP) : result SEXP :=
  add%stack "do_length" in
    run%success Rf_checkArityCall globals runs S op args call using S in
    run%success Rf_check1arg globals S args call "x" using S in
    read%list args_car, _, _ := args using S in
    let x := args_car in
    let%success x_obj := isObject S x using S in
    let%success (disp, ans) := DispatchOrEval globals runs S call op "length" args env false true using S in
    if x_obj && disp then
        let%success ans_length := R_length globals runs S ans using S in
        let%success ans_type := TYPEOF S ans using S in
        ifb ans_length = 1 /\ ans_type = RealSxp then
            read%Real d := ans at 0 using S in
            ifb R_FINITE d /\ d >= 0 /\ d <= INT_MAX /\ Double.floor d = d then
                let%success ans := coerceVector globals runs S ans IntSxp using S in
                    result_success S ans
            else
                result_success S ans
        else
            result_success S ans
    else
    (** Assuming LONG_VECTOR_SUPPORT is false **)
        let%success x_length := R_length globals runs S x using S in
        let (S, s_x) := ScalarInteger globals S x_length in
            result_success S s_x.

End Parameters.
