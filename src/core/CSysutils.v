(** Core.CSysutils.
  The function names in this file correspond to the function names
  in the file main/sysutils.c. **)

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
Require Import CNames.


Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition get_R_FunTab S :=
  add%stack "get_R_FunTab" in
  match runs_R_FunTab runs with
  | None => result_bottom S
  | Some t => result_success S t
  end.

Definition read_R_FunTab S n :=
  add%stack "read_R_FunTab" in
  let%success t := get_R_FunTab S using S in
  ifb n >= ArrayList.length t then
    result_impossible S "Out of bounds."
  else
    let c := ArrayList.read t n in
    result_success S c.


Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition translateChar S x :=
  add%stack "translateChar" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> CharSxp then
    result_error S "Must be called on a CharSxp."
  else
    (** The original C program deals with encoding here. **)
    CHAR S x.

Definition installTrChar S x :=
  add%stack "installTrChar" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> CharSxp then
    result_error S "Must be called on a CharSxp."
  else
    (** The original C program deals with encoding here. **)
    installChar globals runs S x.

End Parameterised.

