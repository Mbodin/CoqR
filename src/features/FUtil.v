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

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.
Local Coercion int_to_double : Z >-> double.

(** There is a macro replacing every call to [checkArity (a, b)] to
  [Rf_checkArityCall (a, b, call)]. This macro is not convertible in
  Coq as the [call] argument is not available in scope. We thus unfold
  this macro during the translation. **)
Definition Rf_checkArityCall (op args call : SEXP) :=
  add%stack "Rf_checkArityCall" in
  let%success arity := PRIMARITY runs op in
  let%success len := R_length globals runs args in
  ifb arity >= 0 /\ arity <> len then
    if%success PRIMINTERNAL runs op then
      result_error "An argument has been passed to an element of .Internal without its requirements."
    else result_error "An argument has been passed to something without its requirements."
  else result_skip.

Definition Rf_check1arg (arg call : SEXP) formal :=
  add%stack "Rf_check1arg" in
  read%list _, _, arg_tag := arg in
  ifb arg_tag = R_NilValue then
    result_skip
  else
    let%success printname := PRINTNAME arg_tag in
    let%success supplied := CHAR printname in
    ifb supplied <> formal then
     result_error "Supplied argument name does not match expected name."
    else result_skip.

Definition ncols s :=
  add%stack "ncols" in
    let%success s_vec := isVector s in
    let%success s_list := isList globals s in
    ifb s_vec \/ s_list then
      let%success t := getAttrib globals runs s R_DimSymbol in
      ifb t = R_NilValue then
        result_success 1%Z
      else
        let%success t_len := LENGTH globals t in
        ifb t_len >= 2 then
          read%Integer r := t at 1 in
          result_success r
        else result_success 1%Z
    else if%success isFrame globals runs s then
      let%success r := R_length globals runs s in
      result_success (r : int)
    else result_error "Object is not a matrix.".

Definition nrows s :=
  add%stack "nrows" in
    let%success s_isVector := isVector s in
    let%success s_isList := isList globals s in

    ifb s_isVector \/ s_isList then
        let%success t := getAttrib globals runs s R_DimSymbol in
        ifb t = R_NilValue then
            LENGTH globals s
        else
            read%Integer t_0 := t at 0 in
            result_success (Z.to_nat t_0)
    else
        let%success s_isFrame := isFrame globals runs s in
        if s_isFrame then
            result_not_implemented "isFrame(s)"
        else
            result_error "object is not a matrix".

End Parameters.

