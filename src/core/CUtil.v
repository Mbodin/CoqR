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
Require Import Double.
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


Definition type2rstr S (t : SExpType) :=
  add%stack "type2rstr" in
  let res := Type2Table_rstrName (ArrayList.read (global_Type2Table globals) t) in
  ifb res <> NULL then result_success S res
  else result_success S (R_NilValue : SEXP).

Definition nthcdr S s n :=
  add%stack "nthcdr" in
  let%success s_li := isList globals S s using S in
  let%success s_la := isLanguage globals S s using S in
  let%success s_fr := isFrame globals runs S s using S in
  let%success s_t := TYPEOF S s using S in
  ifb s_li \/ s_la \/ s_fr \/ s_t = DotSxp then
    do%success (s, n) := (s, n)
    whileb n > 0 do
      ifb s = R_NilValue then
        result_error S "List too short."
      else
        read%list _, s_cdr, _ := s using S in
        result_success S (s, n - 1) using S, runs in
    result_success S s
  else result_error S "No CDR.".

End Parameterised.

