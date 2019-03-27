(** Core.CGram.
  The function names in this file correspond to the function names
  in the file main/gram.y. **)

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
Require Import CMemory.
Require Import CRinlinedfuns.
Require Import CSysutils.


Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition mkTrue :=
  alloc_vector_lgl globals (ArrayList.from_list [1 : int]).

Definition mkFalse :=
  alloc_vector_lgl globals (ArrayList.from_list [0 : int]).

Definition mkNA :=
  alloc_vector_lgl globals (ArrayList.from_list [NA_LOGICAL : int]).


Definition NewList :=
  add%stack "NewList" in
  let (S, s) := CONS globals R_NilValue R_NilValue in
  set%car s := s in
  result_success s.

Definition GrowList l s :=
  add%stack "GrowList" in
  let (S, tmp) := CONS globals s R_NilValue in
  read%list l_car, _, _ := l in
  set%cdr l_car := tmp in
  set%car l := tmp in
  result_success l.

Definition TagArg arg tag :=
  add%stack "TagArg" in
  let%success tag_type := TYPEOF tag in
  match tag_type with
  | StrSxp =>
    let%success tag_ := STRING_ELT tag 0 in
    let%success tag := installTrChar globals runs tag_ in
    lang2 globals arg tag
  | NilSxp
  | SymSxp =>
    lang2 globals arg tag
  | _ =>
    result_error "Incorrect tag type."
  end.

Definition FirstArg s tag :=
  add%stack "FirstArg" in
  let%success tmp := NewList in
  let%success tmp := GrowList tmp s in
  read%list tmp_car, _, _ := tmp in
  set%tag tmp_car := tag in
  result_success tmp.

Definition NextArg l s tag :=
  add%stack "NextArg" in
  let%success l := GrowList l s in
  read%list l_car, _, _ := l in
  set%tag l_car := tag in
  result_success l.

Definition CheckFormalArgs formlist new :=
  add%stack "CheckFormalArgs" in
  fold%success
  along formlist
  as _, formlist_tag do
    ifb formlist_tag = new then
      result_error "Repeated formal argument."
    else result_skip using runs, globals in
  result_skip.

End Parameterised.

