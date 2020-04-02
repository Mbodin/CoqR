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

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition translateChar x :=
  add%stack "translateChar" in
  let%success x_type := TYPEOF x in
  ifb x_type <> CharSxp then
    result_error "Must be called on a CharSxp."
  else
    (** The original C program deals with encoding here. **)
    CHAR x.

Definition installTrChar x :=
  add%stack "installTrChar" in
  let%success x_type := TYPEOF x in
  ifb x_type <> CharSxp then
    result_error "Must be called on a CharSxp."
  else
    (** The original C program deals with encoding here. **)
    installChar runs x.

End Parameterised.

