(** Core.CArray.
  The function names in this file correspond to the function names
  in the file main/attrib.c. **)

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
Require Import CRinlinedfuns.
Require Import CAttrib.
Require Import CDuplicate.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.
Local Coercion int_to_double : Z >-> double.

Definition allocMatrix S mode nrow ncol :=
  add%stack "allocMatrix" in
    ifb nrow < 0 \/ ncol < 0 then
        result_error S "negative extents to matrix"
    else
    let n := nrow * ncol in
    let%success s := allocVector globals S mode n using S in
    let%success t := allocVector globals S IntSxp 2 using S in
    write%Integer t at 0 := nrow using S in
    write%Integer t at 1 := ncol using S in
    run%success setAttrib globals runs S s R_DimSymbol t using S in
    result_success S s.                             
                     
Definition allocArray S mode dims :=
  add%stack "allocArray" in
  let%success dims_len := LENGTH globals S dims using S in
  do%success (dn, n) := (1 : double, 1 : nat)
  for i from 0 to dims_len - 1 do
    read%Integer dims_i := dims at i using S in
    let dn := Double.mult dn (dims_i : double) in
    ifb dn > (INT_MAX : double) then
      result_error S "Too many element specified by ‘dims’."
    else
      result_success S (dn, n * Z.to_nat dims_i) using S in
  let%success dims := duplicate globals runs S dims using S in
  let%success array := allocVector globals S mode n using S in
  run%success setAttrib globals runs S array R_DimSymbol dims using S in
  result_success S array.

End Parameterised.

