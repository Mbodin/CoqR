(** Core.CObjects.
  The function names in this file correspond to the function names
  in the file main/objects.c. **)

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
Require Import CDuplicate.

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


Definition R_has_methods S (op : SEXP) :=
  add%stack "R_has_methods" in
  (** This definition is oversimplified.  The final value of the
    original function depends on the value of the global variable
    [R_standardGeneric].  The way this variable is initialised is not
    simple.  It is updated in [R_initMethodDispatch] from
    library/methods/src/methods_list_dispatch.c. **)
  result_success S false.

Definition isS4 S s :=
  add%stack "isS4" in
  IS_S4_OBJECT S s.

Definition asS4 S s (flag : bool) (complete : int) :=
  add%stack "asS4" in
  let%success s_s4 := IS_S4_OBJECT S s using S in
  ifb flag = s_s4 then
    result_success S s
  else
    let%success s :=
      if%success MAYBE_SHARED S s using S then
        shallow_duplicate globals runs S s
      else result_success S s using S in
    run%exit
      if flag then
        run%success SET_S4_OBJECT S s using S in
        result_rskip S
      else
        run%return
          ifb complete <> 0 then
            unimplemented_function "R_getS4DataSlot"
          else result_rskip S using S in
        run%success UNSET_S4_OBJECT S s using S in
        result_rskip S using S in
    result_success S s.

Definition R_possible_dispatch (S : state) (call op args rho : SEXP) (promisedArgs : bool) : result SEXP :=
  unimplemented_function "R_possible_dispatch".


End Parameterised.
