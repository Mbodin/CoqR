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
