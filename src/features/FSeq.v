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

End Parameters.

