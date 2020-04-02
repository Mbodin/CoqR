(** Features.FPrint.
  The function names of this file correspond to the function names
  in the file main/print.c. **)

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

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.
Local Coercion int_to_double : Z >-> double.

Definition do_invisible (call op args env : SEXP) : result_SEXP :=
  add%stack "do_invisible" in
  let%success args_length := R_length globals runs args in
  match args_length with
  | 0 => result_success (R_NilValue : SEXP)
  | 1 => run%success Rf_check1arg globals args call "x" in
         read%list args_car, _, _ := args in
         result_success args_car
         | _ => run%success Rf_checkArityCall globals runs op args call in
                result_success call
  end.

End Parameters.
