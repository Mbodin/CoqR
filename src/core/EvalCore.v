(** ** eval.c **)

(** The function names of this section correspond to the function
  names in the file main/eval.c. The most important functions of
  eval.c are however only shown in a later section. **)

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
Require Import Ascii Double.
Require Import Loops.
Require Import RinternalsCore.
Require Import Memory.
Require Import Rinlinedfuns.

Section Parameterised.

(** * Global Variables **)

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

Definition BCCONSTS S e :=
  add%stack "BCCONSTS" in
  BCODE_CONSTS S e.

Definition bytecodeExpr S e :=
  add%stack "bytecodeExpr" in
  if%success isByteCode S e using S then
    let%success e := BCCONSTS S e using S in
    let%success e_len := LENGTH globals S e using S in
    ifb e_len > 0 then
      VECTOR_ELT S e 0
    else result_success S (R_NilValue : SEXP)
  else result_success S e.

Definition R_PromiseExpr S p :=
  add%stack "R_PromiseExpr" in
  read%prom _, p_prom := p using S in
  bytecodeExpr S (prom_expr p_prom).

Definition PREXPR S e :=
  add%stack "PREXPR" in
  R_PromiseExpr S e.


End Parameterised.
