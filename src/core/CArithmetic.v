(** Core.CArithmetic.
  The function names in this file correspond to the function names
  in the file main/arithmetic.c. **)

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
From CoqR.core Require Import CRinternals CRinlinedfuns.

Section Parameterised.

(** Global Variables **)

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

(* We may want to make [INT_MIN] and [INT_MAX] a parameter of the formalisation,
  as it depends on the C compiler options. *)
Definition INT_MIN : int := - 2 ^ 31.
Definition INT_MAX : int := 2 ^ 31 - 1.

Definition R_INT_MAX := INT_MAX.
Definition R_INT_MIN := INT_MIN.

Definition R_NaInt := INT_MIN.
Definition NA_INTEGER := R_NaInt.
Definition NA_LOGICAL := R_NaInt.
Definition R_PosInf : double := Double.posInf.
Definition R_NegInf : double := Double.negInf.
Definition R_NaN : double := Double.NaN.
Definition R_NaReal : double := Double.NaN1954.
Definition NA_REAL : double := R_NaReal.

Definition R_NaString := NA_STRING.

Definition R_XLEN_T_MAX : int := Zpos 4503599627370496.

Definition PLUSOP := 1.
Definition MINUSOP := 2.
Definition TIMESOP := 3.
Definition DIVOP := 4.
Definition POWOP := 5.
Definition MODOP := 6.
Definition IDIVOP := 7.

Definition EQOP := 1.
Definition NEOP := 2.
Definition LTOP := 3.
Definition LEOP := 4.
Definition GEOP := 5.
Definition GTOP := 6.

(** End of Global Variables **)

Definition R_IsNA (x : double) :=
  decide (Double.getNaNData x = Some 1954)%positive.

Definition R_IsNaN x :=
  match Double.getNaNData x with
  | Some i => decide (i <> 1954)%positive
  | None => false
  end.

Definition R_finite (x : double) :=
  decide (~ Double.isNaN x /\ x <> R_PosInf /\ x <> R_NegInf).

Definition R_FINITE := R_finite.

Definition ScalarValue1 x : result_SEXP :=
  add%stack "ScalarValue1" in
  if%success NO_REFERENCES x then
    (x : result_SEXP)
  else
    let%success x_type := TYPEOF x in
    allocVector x_type 1.

Definition ScalarValue2 x y : result_SEXP :=
  add%stack "ScalarValue2" in
  if%success NO_REFERENCES x then
    (x : result_SEXP)
  else
    if%success NO_REFERENCES y then
      (y : result_SEXP)
    else
      let%success x_type := TYPEOF x in
      allocVector x_type 1.

End Parameterised.

