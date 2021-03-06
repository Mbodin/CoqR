(** Core.CDefn.
  The function names in this file correspond to the function names
  in the file include/Defn.h. **)

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


Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition SPECIAL_SYMBOL_BIT := 12.

Definition IS_SPECIAL_SYMBOL b :=
  add%stack "IS_SPECIAL_SYMBOL" in
  read%defined b_ := b in
  result_success (nth_bit SPECIAL_SYMBOL_BIT (gp b_) ltac:(nbits_ok)).

(** This macro definition was already redundant in C. **)
Definition NO_SPECIAL_SYMBOLS x :=
  add%stack "NO_SPECIAL_SYMBOLS" in
  read%defined x_ := x in
  result_success (nth_bit SPECIAL_SYMBOL_BIT (gp x_) ltac:(nbits_ok)).

Definition SET_SPECIAL_SYMBOL x v :=
  add%stack "SET_SPECIAL_SYMBOL" in
  map%gp x with @write_nbit 16 SPECIAL_SYMBOL_BIT ltac:(nbits_ok) v in
  result_skip.

Definition SET_NO_SPECIAL_SYMBOLS x :=
  add%stack "SET_NO_SPECIAL_SYMBOLS" in
  SET_SPECIAL_SYMBOL x true.

Definition UNSET_NO_SPECIAL_SYMBOLS x :=
  add%stack "UNSET_NO_SPECIAL_SYMBOLS" in
  SET_SPECIAL_SYMBOL x false.

Definition ACTIVE_BINDING_BIT := 15.

Definition IS_ACTIVE_BINDING symbol :=
  add%stack "IS_ACTIVE_BINDING" in
  read%defined symbol_ := symbol in
  result_success (nth_bit ACTIVE_BINDING_BIT (gp symbol_) ltac:(nbits_ok)).

Definition BINDING_LOCK_BIT := 14.

Definition BINDING_IS_LOCKED symbol :=
  add%stack "BINDING_IS_LOCKED" in
  read%defined symbol_ := symbol in
  result_success (nth_bit BINDING_LOCK_BIT (gp symbol_) ltac:(nbits_ok)).

Definition LOCK_BINDING x :=
  add%stack "LOCK_BINDING" in
  map%gp x with @write_nbit 16 BINDING_LOCK_BIT ltac:(nbits_ok) true in
  result_skip.

Definition CACHED_BIT := 5.

Definition SET_CACHED x v :=
  add%stack "SET_CACHED" in
  map%gp x with @write_nbit 16 CACHED_BIT ltac:(nbits_ok) v in
  result_skip.

Definition IS_CACHED x :=
  add%stack "IS_CACHED" in
  read%defined x_ := x in
  result_success (nth_bit CACHED_BIT (gp x_) ltac:(nbits_ok)).

Definition PRSEEN x :=
  add%stack "PRSEEN" in
  read%defined x_ := x in
  result_success (nbits_to_nat (gp x_)).

Definition SET_PRSEEN x v I :=
  add%stack "SET_PRSEEN" in
  set%gp x with @nat_to_nbits 16 v I in
  result_skip.
Arguments SET_PRSEEN : clear implicits.

Definition PRSEEN_direct x :=
  add%stack "PRSEEN_direct" in
  read%defined x_ := x in
  result_success (gp x_).

Definition SET_PRSEEN_direct x v :=
  add%stack "SET_PRSEEN_direct" in
  set%gp x with v in
  result_skip.

Definition PRENV p :=
  add%stack "PRENV" in
  read%prom _, p_prom := p in
  result_success (prom_env p_prom).

Definition PRVALUE p :=
  add%stack "PRVALUE" in
  read%prom _, p_prom := p in
  result_success (prom_value p_prom).

Definition R_VARLOC_IS_NULL loc :=
  decide (loc = NULL).

End Parameterised.

Arguments SET_PRSEEN : clear implicits.

