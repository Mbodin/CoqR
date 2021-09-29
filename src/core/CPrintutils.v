(** Core.CPrintutils.
  The function names in this file correspond to the function names
  in the file main/printutils.c. **)

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
From Lib Require Import Double.
From CoqR Require Import Loops.
From CoqR.core Require Import CArithmetic.

Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.
Local Coercion int_to_double : Z >-> double.


Definition EncodeLogical x :=
  ifb x = NA_LOGICAL then "NA"%string
  else ifb x <> 0 then "TRUE"%string
  else "FALSE"%string.

Definition StringFromReal x : result_SEXP :=
  add%stack "StringFromReal" in
  if R_IsNA x then
    (NA_STRING : result_SEXP)
  else unimplemented_function "EncodeRealDrop0".

End Parameterised.

