(** Features.FSeq.
  The function names of this file correspond to the function names
  in the file main/seq.c. **)

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

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition cross_colon (S : state) (call s t : SEXP) : result SEXP :=
  unimplemented_function "cross_colon".

Definition seq_colon S n1 n2 (call : SEXP) : result SEXP :=
  add%stack "seq_colon" in
  let r := Double.fabs (Double.sub n2 n1) in
  ifb r >= (R_XLEN_T_MAX : double) then
    result_error S "Result would be too large a vector."
  else
    let n := Z.to_nat (Double.double_to_int_zero (Double.add (Double.add r (1 : double)) (Double.FLT_EPSILON))) in
    let useInt := decide (n1 <= (INT_MAX : double) /\ n1 = ((Double.double_to_int_zero n1) : double)) in
    let useInt :=
      ifb n1 <= (INT_MIN : double) \/ n1 > (INT_MAX : double) then false
      else
        let dn := n : double in
        let r :=
          Double.add n1
            (ifb n1 <= n2 then Double.sub dn (1 : double) else Double.opp (Double.sub dn (1 : double))) in
        decide (r <= (INT_MIN : double) \/ r > (INT_MAX : double)) in
    let%success ans :=
      if useInt then
        let in1 := Double.double_to_int_zero n1 in
        let%success ans := allocVector globals S IntSxp n using S in
        run%success
          ifb n1 <= n2 then
            do%let for i from 0 to n - 1 do
              write%Integer ans at i := in1 + i using S in
              result_skip S using S
          else
            do%let for i from 0 to n - 1 do
              write%Integer ans at i := in1 - i using S in
              result_skip S using S using S in
        result_success S ans
      else
        let%success ans := allocVector globals S RealSxp n using S in
        run%success
          ifb n1 <= n2 then
            do%let for i from 0 to n - 1 do
              write%Real ans at i := Double.add n1 (i : double) using S in
              result_skip S using S
          else
            do%let for i from 0 to n - 1 do
              write%Real ans at i := Double.sub n1 (i : double) using S in
              result_skip S using S using S in
        result_success S ans
      using S in
    result_success S ans.

Definition do_colon S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_colon" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let%success args_car_in := inherits globals runs S args_car "factor" using S in
  let%success args_cdr_car_in := inherits globals runs S args_cdr_car "factor" using S in
  ifb args_car_in /\ args_cdr_car_in then
    cross_colon S call args_car args_cdr_car
  else
    let s1 := args_car in
    let s2 := args_cdr_car in
    let%success n1 := R_length globals runs S s1 using S in
    let%success n2 := R_length globals runs S s2 using S in
    ifb n1 = 0 \/ n2 = 0 then
      result_error S "Argument of length 0."
    else
      (* Warnings have been formalised out here. *)
      let%success n1 := asReal globals S s1 using S in
      let%success n2 := asReal globals S s2 using S in
      ifb ISNAN n1 \/ ISNAN n2 then
        result_error S "NA or NaN argument."
      else seq_colon S n1 n2 call.

Definition do_rep_int S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_rep_int" in
    run%success Rf_checkArityCall globals runs S op args call using S in
    read%list args_car, args_cdr, _ := args using S in
    let s := args_car in
    read%list args_cdr_car, _, _ := args_cdr using S in
    let ncopy := args_cdr_car in
    
    let%success ncopy_isVector := isVector ncopy using S in
    if negb ncopy_isVector then
        result_error S "invalid type for times (must be a vector)"
    else

    let%success s_isVector := isVector s using S in
    ifb negb s_isVector /\ s <> R_NilValue then
        result_error S "attempt to replicate an object of type"
    else
    let%success nc := xlength globals runs S ncopy using S in
    let%success s_xlength := xlength globals runs S s using S in
    let%success a :=
    ifb nc = s_xlength then
        rep2 S s ncopy
    else
        ifb nc <> 1 then
            result_error S "invalid 'times' value"
        else
        let ns := s_xlength in
        let%success ncopy_type := TYPEOF S ncopy using S in
        let%success nc :=
        ifb ncopy_type <> IntSxp then
            let%success snc := asReal globals S ncopy using S in
            ifb negb (R_FINITE snc) \/ snc <= (-1)%Z \/ (ns > 0 /\ snc >= R_XLEN_T_MAX + 1) then
                result_error S "invalid 'times' value"
            else
                result_success S (ifb ns = 0 then 1 else snc) 
        else
            let%success nc := asInteger globals S ncopy using S in
            ifb nc = NA_INTEGER \/ nc < 0 then
                result_error S "invalid 'times' value"
            else  
                result_success S nc
        using S in
        ifb nc * ns > R_XLEN_T_MAX then
            result_error S "invalid 'times' value"
        else
            rep3 S s ns (nc * ns)
    using S in

    (** Considering _S4_rep_keepClass not defined **)
    let%success s_inherits := inherits globals runs S s "factor" using S in
    if s_inherits then
        let%success tmp :=
        let%success s_inherits := inherits globals runs S s "ordered" using S in
        if s_inherits then
            let%success tmp := allocVector globals S StrSxp 2 using S in
            let (S, ordered_mkChar) := mkChar globals S "ordered" in
            run%success SET_STRING_ELT S tmp 0 ordered_mkChar using S in
            let (S, factor_mkChar) := mkChar globals S "factor" in
            run%success SET_STRING_ELT S tmp 1 factor_mkChar using S in
            result_success S tmp
        else
            let (S, factor_mkString) := mkString globals S "factor" in
            result_success S factor_mkString
        using S in

        run%success setAttrib globals runs S a R_ClassSymbol tmp using S in
        let%success s_attrib := getAttrib globals runs S s R_LevelsSymbol using S in
        run%success setAttrib globals runs S a R_LevelsSymbol s_attrib using S in
        result_success S a
    else
        result_success S a.
                
End Parameters.

