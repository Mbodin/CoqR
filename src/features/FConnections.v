(** Features.FConnections.
  The function names of this file correspond to the function names
  in the file main/connections.c. **)

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
Require Import Util.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition getConnection S (n : int) :=
  add%stack "getConnection" in
  ifb n < 0 \/ n >= length (R_Connections S) \/ n = NA_INTEGER then
    result_error S "Invalid connection."
  else
    let%defined c := nth_option (Z.to_nat n) (R_Connections S) using S in
    result_success S c.

(** The following six functions execute the interpretation function
  for each action, then replaces the corresponding connection in the
  global state.  These functions are not in the original C code of R.
  They correspond to a non-pure call to the corresponding methods of
  the given connection. **)

Definition putConnection S (n : int) c :=
  add%stack "putConnection" in
  ifb n < 0 \/ n >= length (R_Connections S) \/ n = NA_INTEGER then
    result_error S "Invalid connection."
  else
    let S := update_R_Connections S (update (Z.to_nat n) c (R_Connections S)) in
    result_skip S.

Definition run_open S n :=
  add%stack "run_open" in
  let%success con := getConnection S n using S in
  let%defined (c, r) := interpret_open (Rconnection_open con) con using S in
  run%success putConnection S n c using S in
  result_success S r.

Definition run_close S n :=
  add%stack "run_close" in
  let%success con := getConnection S n using S in
  let%defined c := interpret_close (Rconnection_close con) con using S in
  run%success putConnection S n c using S in
  result_skip S.

Definition run_destroy S n :=
  add%stack "run_destroy" in
  let%success con := getConnection S n using S in
  let%defined c := interpret_destroy (Rconnection_destroy con) con using S in
  run%success putConnection S n c using S in
  result_skip S.

Definition run_print S n str :=
  add%stack "run_print" in
  let%success con := getConnection S n using S in
  let%defined c := interpret_print (Rconnection_print con) con str using S in
  run%success putConnection S n c using S in
  result_skip S.

Definition run_flush S n :=
  add%stack "run_flush" in
  let%success con := getConnection S n using S in
  let%defined c := interpret_flush (Rconnection_fflush con) con using S in
  run%success putConnection S n c using S in
  result_skip S.

(** We now continue with functions translated from main/connections.c. **)

Definition do_getconnection S (call op args env : SEXP) : result SEXP :=
  add%stack "do_getconnection" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, _, _ := args using S in
  let%success what := asInteger globals S args_car using S in
  ifb what = NA_INTEGER then
    result_error S "There is no connection NA."
  else ifb what < 0 \/ what >= length (R_Connections S) then
    result_error S "There is no such connection."
  else
    let%defined con := nth_option (Z.to_nat what) (R_Connections S) using S in
    let (S, ans) := ScalarInteger globals S what in
    let%success class := allocVector globals S StrSxp 2 using S in
    let (S, class0) := mkChar globals S (Rconnection_class con) in
    write%Pointer class at 0 := class0 using S in
    let (S, class1) := mkChar globals S "connection" in
    write%Pointer class at 1 := class1 using S in
    run%success classgets globals runs S ans class using S in
    run%success
      ifb what > 2 then
        let%success ex_ptr := result_not_implemented "External pointer." using S in
        run%success setAttrib globals runs S ans R_ConnIdSymbol ex_ptr using S in
        result_skip S
      else result_skip S using S in
    result_success S ans.

End Parameters.

