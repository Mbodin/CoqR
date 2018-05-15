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

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


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

