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


Definition mkTrue S :=
  alloc_vector_lgl globals S (ArrayList.from_list [1 : int]).

Definition mkFalse S :=
  alloc_vector_lgl globals S (ArrayList.from_list [0 : int]).

Definition mkNA S :=
  alloc_vector_lgl globals S (ArrayList.from_list [NA_LOGICAL : int]).


Definition NewList S :=
  add%stack "NewList" in
  let (S, s) := CONS globals S R_NilValue R_NilValue in
  set%car s := s using S in
  result_success S s.

Definition GrowList S l s :=
  add%stack "GrowList" in
  let (S, tmp) := CONS globals S s R_NilValue in
  read%list l_car, _, _ := l using S in
  set%cdr l_car := tmp using S in
  set%car l := tmp using S in
  result_success S l.

Definition TagArg S arg tag :=
  add%stack "TagArg" in
  let%success tag_type := TYPEOF S tag using S in
  match tag_type with
  | StrSxp =>
    let%success tag_ := STRING_ELT S tag 0 using S in
    let%success tag := installTrChar globals runs S tag_ using S in
    lang2 globals S arg tag
  | NilSxp
  | SymSxp =>
    lang2 globals S arg tag
  | _ =>
    result_error S "Incorrect tag type."
  end.

Definition FirstArg S s tag :=
  add%stack "FirstArg" in
  let%success tmp := NewList S using S in
  let%success tmp := GrowList S tmp s using S in
  read%list tmp_car, _, _ := tmp using S in
  set%tag tmp_car := tag using S in
  result_success S tmp.

Definition NextArg S l s tag :=
  add%stack "NextArg" in
  let%success l := GrowList S l s using S in
  read%list l_car, _, _ := l using S in
  set%tag l_car := tag using S in
  result_success S l.

Definition CheckFormalArgs S formlist new :=
  add%stack "CheckFormalArgs" in
  fold%success
  along formlist
  as _, formlist_tag do
    ifb formlist_tag = new then
      result_error S "Repeated formal argument."
    else result_skip S using S, runs, globals in
  result_skip S.

End Parameterised.

