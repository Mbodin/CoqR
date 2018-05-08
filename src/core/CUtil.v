(** Core.CUtil.
  The function names in this file correspond to the function names
  in the file main/util.c. **)

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
Require Import CRinternals.
Require Import CRinlinedfuns.

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


Definition truenames : list string :=
  ["T"; "True"; "TRUE"; "true"]%string.

Definition StringTrue name :=
  decide (Mem name truenames).

Definition falsenames : list string :=
  ["F"; "False"; "FALSE"; "false"]%string.

Definition StringFalse name :=
  decide (Mem name falsenames).

Definition isspace c :=
  decide (Mem c [" " ; "009" (** '\t' **) ; "010" (** '\n' **) ; "011" (** '\v' **) ; "012" (** '\f' **) ; "013" (** '\r' **)]%char).

Definition isBlankString s :=
  decide (Forall (fun c => isspace c) (string_to_list s)).

End Parameterised.

