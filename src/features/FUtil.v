(** Features.FUtil.
  The function names of this file correspond to the function names
  in the file main/util.c. **)

(* Copyright © 2018 Martin Bodin, Tomás Díaz

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
Require Import Rcore.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

(** There is a macro replacing every call to [checkArity (a, b)] to
  [Rf_checkArityCall (a, b, call)]. This macro is not convertible in
  Coq as the [call] argument is not available in scope. We thus unfold
  this macro during the translation. **)
Definition Rf_checkArityCall S (op args call : SEXP) :=
  add%stack "Rf_checkArityCall" in
  let%success arity := PRIMARITY runs S op using S in
  let%success len := R_length globals runs S args using S in
  ifb arity >= 0 /\ arity <> len then
    if%success PRIMINTERNAL runs S op using S then
      result_error S "An argument has been passed to an element of .Internal without its requirements."
    else result_error S "An argument has been passed to something without its requirements."
  else result_skip S.

Definition Rf_check1arg S (arg call : SEXP) formal :=
  add%stack "Rf_check1arg" in
  read%list _, _, arg_tag := arg using S in
  ifb arg_tag = R_NilValue then
    result_skip S
  else
    let%success printname := PRINTNAME S arg_tag using S in
    let%success supplied := CHAR S printname using S in
    ifb supplied <> formal then
     result_error S "Supplied argument name does not match expected name."
    else result_skip S.

Definition ncols S s :=
  add%stack "ncols" in
    let%success s_vec := isVector S s using S in
    let%success s_list := isList globals S s using S in
    ifb s_vec \/ s_list then
      let%success t := getAttrib globals runs S s R_DimSymbol using S in
      ifb t = R_NilValue then
        result_success S 1%Z
      else
        let%success t_len := LENGTH globals S t using S in
        ifb t_len >= 2 then
          read%Integer r := t at 1 using S in
          result_success S r
        else result_success S 1%Z
    else if%success isFrame globals runs S s using S then
      let%success r := R_length globals runs S s using S in
      result_success S (r : int)
    else result_error S "Object is not a matrix.".

End Parameters.

