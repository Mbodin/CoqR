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
From CoqR Require Import Rcore.
Require Import FUtil.

Section Parameters.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition getConnection (n : int) :=
  add%stack "getConnection" in
  read%state Connections := R_Connections in
  ifb n < 0 \/ n >= length Connections \/ n = NA_INTEGER then
    result_error "Invalid connection."
  else
    let%defined c := nth_option (Z.to_nat n) Connections in
    result_success c.

(** The following six functions execute the interpretation function
  for each action, then replaces the corresponding connection in the
  global state.  These functions are not in the original C code of R.
  They correspond to a non-pure call to the corresponding methods of
  the given connection. **)

Definition putConnection (n : int) c :=
  add%stack "putConnection" in
  read%state Connections := R_Connections in
  ifb n < 0 \/ n >= length Connections \/ n = NA_INTEGER then
    result_error "Invalid connection."
  else
    map%state update_R_Connections (update (Z.to_nat n) c Connections) in
    result_skip.

Definition run_open n :=
  add%stack "run_open" in
  let%success con := getConnection n in
  let%defined (c, r) := interpret_open (Rconnection_open con) con in
  run%success putConnection n c in
  result_success r.

Definition run_close n :=
  add%stack "run_close" in
  let%success con := getConnection n in
  let%defined c := interpret_close (Rconnection_close con) con in
  run%success putConnection n c in
  result_skip.

Definition run_destroy n :=
  add%stack "run_destroy" in
  let%success con := getConnection n in
  let%defined c := interpret_destroy (Rconnection_destroy con) con in
  run%success putConnection n c in
  result_skip.

Definition run_print n str :=
  add%stack "run_print" in
  let%success con := getConnection n in
  let%defined c := interpret_print (Rconnection_print con) con str in
  run%success putConnection n c in
  result_skip.

Definition run_flush n :=
  add%stack "run_flush" in
  let%success con := getConnection n in
  let%defined c := interpret_flush (Rconnection_fflush con) con in
  run%success putConnection n c in
  result_skip.

(** We now continue with functions translated from main/connections.c. **)

Definition do_getconnection (call op args env : SEXP) : result_SEXP :=
  add%stack "do_getconnection" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, _, _ := args in
  let%success what := asInteger globals args_car in
  read%state Connections := R_Connections in
  ifb what = NA_INTEGER then
    result_error "There is no connection NA."
  else ifb what < 0 \/ what >= length Connections then
    result_error "There is no such connection."
  else
    let%defined con := nth_option (Z.to_nat what) Connections in
    let%success ans := ScalarInteger globals what in
    let%success class := allocVector globals StrSxp 2 in
    let%success class0 := mkChar globals (Rconnection_class con) in
    write%Pointer class at 0 := class0 in
    let%success class1 := mkChar globals "connection" in
    write%Pointer class at 1 := class1 in
    run%success classgets globals runs ans class in
    run%success
      ifb what > 2 then
        let%success ex_ptr := result_not_implemented "External pointer." in
        run%success setAttrib globals runs ans R_ConnIdSymbol ex_ptr in
        result_skip
      else result_skip in
    result_success ans.

End Parameters.

