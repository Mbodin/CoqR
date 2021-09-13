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
From CoqR Require Import Rcore.
Require Import FUtil.

Section Parameters.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.



Definition xcopyWithRecycle {A B} (GETELT : SEXP -> nat -> result B) (SETELT : SEXP -> nat -> B -> result A) (dst src : SEXP) (dstart n nsrc : int) :=
  add%stack "xcopyWithRecycle_1" in
  ifb nsrc >= n then
    do%success
    for i from 0 to n - 1 do
      let%success src_i := GETELT src i in
      run%success SETELT dst (Z.to_nat dstart + i) src_i in
      result_skip
    in result_skip
  else
  ifb nsrc = 1 then
    let%success val := GETELT src 0 in
    do%success
    for i from 0 to n - 1 do
      run%success SETELT dst (Z.to_nat dstart + i) val in
      result_skip
    in result_skip
  else
    let sidx := 0%Z in
    do%success sidx := sidx
    for i from 0 to n - 1 do
     let sidx := ifb sidx = nsrc then 0%Z else sidx in
     let%success src_sidx := GETELT src (Z.to_nat sidx) in
     run%success SETELT dst (Z.to_nat dstart + i) src_sidx in
     result_success sidx
    in result_skip.


Definition copyVector (s t : SEXP) :=
  add%stack "copyVector" in
  let%success sT := TYPEOF s in
  let%success tT := TYPEOF t in
  ifb sT <> tT then
    result_error "vector types do not match in copyVector"
  else
  let%success ns := XLENGTH s in
  let%success nt := XLENGTH t in
  match sT with
  | StrSxp => xcopyWithRecycle STRING_ELT SET_STRING_ELT s t 0 ns nt
  | LglSxp =>
    let GETELT src i :=
      read%Logical src_i := src at i in
      result_success src_i
    in
    let SETELT dst i val :=
      write%Logical dst at i := val in
      result_skip
    in
    xcopyWithRecycle GETELT SETELT s t 0 ns nt

  | IntSxp =>
    let GETELT src i :=
      read%Integer src_i := src at i in
      result_success src_i
    in
    let SETELT dst i val :=
      write%Integer dst at i := val in
      result_skip
    in
    xcopyWithRecycle GETELT SETELT s t 0 ns nt
  | RealSxp =>
    let GETELT src i :=
      read%Real src_i := src at i in
      result_success src_i
    in
    let SETELT dst i val :=
      write%Real dst at i := val in
      result_skip
    in
    xcopyWithRecycle GETELT SETELT s t 0 ns nt
  | CplxSxp =>
    let GETELT src i :=
      read%Complex src_i := src at i in
      result_success src_i
    in
    let SETELT dst i val :=
      write%Complex dst at i := val in
      result_skip
    in
    xcopyWithRecycle GETELT SETELT s t 0 ns nt
  | ExprSxp
  | VecSxp => xcopyWithRecycle VECTOR_ELT SET_VECTOR_ELT s t 0 ns nt
  | RawSxp => result_not_implemented "Raw case"
  | _ => result_error "unimplemented type for copyVector"
  end.



Definition copyMatrix (s t : SEXP) byrow :=
  add%stack "copyMatrix" in
  let%success nr := nrows globals runs s in
  let%success nc := ncols globals runs s in
  let%success nt := XLENGTH t in

  ifb byrow <> 0 then
    let%success s_type := TYPEOF s in
    match s_type with
    | StrSxp =>
      do%success sidx := 0
      for i from 0 to nr - 1 do
        do%success (sidx, didx) := (sidx, i)
        for j from 0 to nc - 1 do
          let%success t_sidx := STRING_ELT t sidx in
          run%success SET_STRING_ELT s didx t_sidx in
          let sidx := sidx + 1 in
          let sidx := ifb sidx >= nt then sidx - nt else sidx in
        result_success (sidx, didx +  nr)
        in
        result_success sidx
      in result_skip
  | LglSxp =>
    do%success sidx := 0
      for i from 0 to nr - 1 do
        do%success (sidx, didx) := (sidx, i)
        for j from 0 to nc - 1 do
          read%Logical t_sidx := t at sidx in
          write%Logical s at didx := t_sidx in
          let sidx := sidx + 1 in
          let sidx := ifb sidx >= nt then sidx - nt else sidx in
        result_success (sidx, didx +  nr)
        in
        result_success sidx
    in result_skip
  | IntSxp =>
    do%success sidx := 0
      for i from 0 to nr - 1 do
        do%success (sidx, didx) := (sidx, i)
        for j from 0 to nc - 1 do
          read%Integer t_sidx := t at sidx in
          write%Integer s at didx := t_sidx in
          let sidx := sidx + 1 in
          let sidx := ifb sidx >= nt then sidx - nt else sidx in
        result_success (sidx, didx +  nr)
        in
        result_success sidx
    in result_skip
  | RealSxp =>
    do%success sidx := 0
      for i from 0 to nr - 1 do
        do%success (sidx, didx) := (sidx, i)
        for j from 0 to nc - 1 do
          read%Real t_sidx := t at sidx in
          write%Real s at didx := t_sidx in
          let sidx := sidx + 1 in
          let sidx := ifb sidx >= nt then sidx - nt else sidx in
        result_success (sidx, didx +  nr)
        in
        result_success sidx
    in result_skip
  | CplxSxp =>
    do%success sidx := 0
      for i from 0 to nr - 1 do
        do%success (sidx, didx) := (sidx, i)
        for j from 0 to nc - 1 do
          read%Complex t_sidx := t at sidx in
          write%Complex s at didx := t_sidx in
          let sidx := sidx + 1 in
          let sidx := ifb sidx >= nt then sidx - nt else sidx in
        result_success (sidx, didx +  nr)
        in
        result_success sidx
    in result_skip
  | ExprSxp
  | VecSxp =>
    do%success sidx := 0
      for i from 0 to nr - 1 do
        do%success (sidx, didx) := (sidx, i)
        for j from 0 to nc - 1 do
          let%success t_sidx := VECTOR_ELT t sidx in
          run%success SET_VECTOR_ELT s didx t_sidx in
          let sidx := sidx + 1 in
          let sidx := ifb sidx >= nt then sidx - nt else sidx in
        result_success (sidx, didx +  nr)
        in
        result_success sidx
    in result_skip
  | RawSxp => result_not_implemented "Raw case"
  | _ => result_error "unimplemented type in copyMatrix"
    end

  else
    copyVector s t.


Definition do_matrix (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_matrix" in
  let nr := 1%Z in
  let nc := 1%Z in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, args_cdr, _ := args in
  let vals := args_car in
  let args := args_cdr in
  let%success vals_type := TYPEOF vals in
  run%success
    match vals_type with
    | LglSxp
    | IntSxp
    | RealSxp
    | CplxSxp
    | StrSxp
    | RawSxp
    | ExprSxp
    | VecSxp => result_skip
    | _ => result_error "'data' must be of a vector type"
    end
  in
  let%success lendat := XLENGTH vals in
  read%list args_car, args_cdr, _ := args in
  let snr := args_car in
  let args := args_cdr in
  read%list args_car, args_cdr, _ := args in
  let snc := args_car in
  let args := args_cdr in
  read%list args_car, args_cdr, _ := args in
  let%success byrow := asLogical globals args_car in
  let args := args_cdr in
  ifb byrow = NA_INTEGER then
    result_error "invalid 'byrow' argument"
  else
    read%list args_car, args_cdr, _ := args in
    let dimnames := args_car in
    let args := args_cdr in
    read%list args_car, args_cdr, _ := args in
    let%success miss_nr := asLogical globals args_car in
    let args := args_cdr in
    read%list args_car, _, _ := args in
    let%success miss_nc := asLogical globals args_car in
    let%success nr :=
    ifb miss_nr = 0 then
      let%success snr_isNumeric := isNumeric globals runs snr in
      if negb snr_isNumeric then
        result_error "non-numeric matrix extent"
      else
      let%success nr := asInteger globals snr in
      ifb nr = NA_INTEGER then
        result_error "invalid 'nrow' value (too large or NA)"
      else
      ifb nr < 0 then
        result_error "invalid 'nrow' value (< 0)"
      else
        result_success (nr : int)
    else
      result_success (nr : int)
    in

    let%success nc :=
    ifb miss_nc = 0 then
      let%success snc_isNumeric := isNumeric globals runs snc in
      if negb snc_isNumeric then
        result_error "non-numeric matrix extent"
      else
      let%success nc := asInteger globals snc in
      ifb nc = NA_INTEGER then
        result_error "invalid 'ncol' value (too large or NA)"
      else
      ifb nc < 0 then
        result_error "invalid 'ncol' value (< 0)"
      else
        result_success nc
    else
      result_success (nc : int)
    in

    let%success (nr, nc) :=
    ifb miss_nr <> 0 /\ miss_nc <> 0 then
      ifb (lendat : int) > INT_MAX then
        result_error "data is too long"
      else
        result_success (lendat : int, nc : int)
    else ifb miss_nr <> 0 then
      ifb (lendat : double) > Double.mult (nc : double) (INT_MAX : double) then
        result_error "data is too long"
      else
      ifb nc = 0 then
        ifb lendat <> 0 then
          result_error "nc = 0 for non-null data"
        else
          result_success (0%Z, nc)
      else
        result_success (Double.double_to_int_zero (Double.ceil (Double.div (lendat : double) (nc : double))), nc)
    else ifb miss_nc <> 0 then
      ifb (lendat : double) > Double.mult (nr : double) (INT_MAX : double) then
        result_error "data is too long"
      else
      ifb nr = 0 then
        ifb lendat <> 0 then
          result_error "nc = 0 for non-null data"
        else
          result_success (nr, 0%Z)
      else
        result_success (nr, (Double.double_to_int_zero (Double.ceil (Double.div (lendat : double) (nr : double)))))
    else
      result_success (nr, nc)
    in

    (* Omitting warnings *)
    let%success ans := allocMatrix globals runs vals_type (Z.to_nat nr) (Z.to_nat nc) in
    run%success
    let%success vals_isVector := isVector vals in
    ifb lendat <> 0 then
      if vals_isVector then
        copyMatrix ans vals (Z.to_nat byrow)
      else
        unimplemented_function "copyListMatrix"
    else if vals_isVector then (* fill with NAs *)
      let N := (Z.to_nat nr) * (Z.to_nat nc) in
      match vals_type with
      | StrSxp =>
        do%success
        for i from 0 to N - 1 do
          SET_STRING_ELT ans i NA_STRING
        in result_skip

      | LglSxp =>
        do%success
        for i from 0 to N - 1 do
          write%Logical ans at i := NA_LOGICAL in result_skip
        in result_skip
      | IntSxp =>
        do%success
        for i from 0 to N - 1 do
          write%Integer ans at i := NA_INTEGER in result_skip
        in result_skip
      | RealSxp =>
        do%success
        for i from 0 to N - 1 do
          write%Real ans at i := NA_REAL in result_skip
        in result_skip
      | CplxSxp => result_not_implemented "Complex case"
      | RawSxp => result_not_implemented "Raw case"
      | _ => result_skip
      end

    else
      result_skip
    in
    let%success dimnames_isNull := isNull dimnames in
    let%success ans :=
    ifb negb dimnames_isNull then
      let%success dimnames_length := R_length globals runs dimnames in
      ifb dimnames_length > 0 then
        unimplemented_function "dimnames"
      else
        result_success ans
    else
      result_success ans
    in
    result_success ans.

Definition do_length (call op args env : SEXP) : result_SEXP :=
  add%stack "do_length" in
    run%success Rf_checkArityCall globals runs op args call in
    run%success Rf_check1arg globals args call "x" in
    read%list args_car, _, _ := args in
    let x := args_car in
    let%success x_obj := isObject x in
    let%success (disp, ans) := DispatchOrEval globals runs call op "length" args env false true in
    if x_obj && disp then
      let%success ans_length := R_length globals runs ans in
      let%success ans_type := TYPEOF ans in
      ifb ans_length = 1 /\ ans_type = RealSxp then
        read%Real d := ans at 0 in
        ifb R_FINITE d /\ d >= 0 /\ d <= INT_MAX /\ Double.floor d = d then
          let%success ans := coerceVector globals runs ans IntSxp in
          result_success ans
        else
          result_success ans
      else
        result_success ans
    else
    (** Assuming LONG_VECTOR_SUPPORT is false **)
      let%success x_length := R_length globals runs x in
      let%success s_x := ScalarInteger globals x_length in
      result_success s_x.

End Parameters.

