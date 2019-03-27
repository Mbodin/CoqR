(** Features.FEnvir.
  The function names of this file correspond to the function names
  in the file main/envir.c. **)

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
Require Import FUtil.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition do_missing (call op args rho : SEXP) : result SEXP :=
  add%stack "do_missing" in
  run%success Rf_checkArityCall globals runs op args call in
  run%success Rf_check1arg globals args call "x" in
  read%list args_car, _, _ := args in
  let%success sym :=
    let sym := args_car in
    let%success sym_str := isString sym in
    let%success sym_len := R_length globals runs sym in
    ifb sym_str /\ sym_len = 1 then
      read%Pointer args_car_0 := args_car at 0 in
      installTrChar globals runs args_car_0
    else result_success sym in
  let s := sym in
  let%success sym_sym := isSymbol sym in
  if negb sym_sym then
    result_error "Invalid use."
  else
    let%success (ddv, sym) :=
      if%success DDVAL sym then
        let%success ddv := ddVal sym in
        result_success (ddv, R_DotsSymbol : SEXP)
      else result_success (0, sym) in
    let%success t := findVarLocInFrame globals runs rho sym in
    let%success rval := allocVector globals LglSxp 1 in
    ifb t <> R_NilValue then
      read%list t_car, _, _ := t in
      let%exit t :=
        if%success DDVAL s then
          let%success t_car_len := R_length globals runs t_car in
          ifb t_car_len < ddv \/ t_car = R_MissingArg then
            write%Logical rval at 0 := 1 in
            result_rreturn rval
          else
            let%success t := nthcdr globals runs t_car (ddv - 1) in
            result_rsuccess t
        else result_rsuccess t in
      run%exit
        let%success t_mis := MISSING t in
        ifb t_mis <> 0 \/ t_car = R_MissingArg then
          write%Logical rval at 0 := 1 in
          result_rreturn rval
        else result_rskip in
      (** This is the translation of the [havebinding] label. **)
      let t := t_car in
      let%success t_type := TYPEOF t in
      ifb t_type <> PromSxp then
        write%Logical rval at 0 := 0 in
        result_success rval
      else
        let%success t := findRootPromise globals runs t in
        let%success t_is :=
          let%success t := PREXPR globals t in
          isSymbol t in
        if negb t_is then
          write%Logical rval at 0 := 0 in
          result_success rval
        else
          let%success t_expr := PREXPR globals t in
          let%success t_env :=
             read%prom _, t_prom := t in
             result_success (prom_env t_prom) in
          let%success ism := R_isMissing globals runs t_expr t_env in
          write%Logical rval at 0 := ism in
          result_success rval
    else result_error "It can only be used for arguments.".

Definition do_get (S : state) (call op args rho : SEXP) : result SEXP :=
  add%stack "do_get" in
  run%success Rf_checkArityCall globals runs op args call in
  unimplemented_function "do_get".

Definition do_assign (call op args rho : SEXP) : result SEXP :=
  add%stack "do_assign" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, args_cdr, _ := args in
  let%success args_car_str := isString args_car in
  let%success args_car_len := R_length globals runs args_car in
  ifb ~ args_car_str \/ args_car_len = 0 then
    result_error "Invalid first argument"
  else
    (** A potential warning has been formalised out here. **)
    let%success args_car_0 := STRING_ELT args_car 0 in
    let%success name := installTrChar globals runs args_car_0 in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr in
    let val := args_cdr_car in
    read%list args_cdr_cdr_car, args_cdr_cdr_cdr, _ := args_cdr_cdr in
    let aenv := args_cdr_cdr_car in
    let%success aenv_type := TYPEOF aenv in
    ifb aenv_type = NilSxp then
      result_error "Use of NULL environment is defunct."
    else
      let%success aenv :=
        ifb aenv_type = EnvSxp then
          result_success aenv
        else
          simple_as_environment globals aenv in
      let%success aenv_type := TYPEOF aenv in
      ifb aenv_type <> EnvSxp then
        result_error "Invalid ‘envir’ argument."
      else
        read%list args_cdr_cdr_cdr_car, _, _ := args_cdr_cdr_cdr in
        let%success ginherits := asLogical globals args_cdr_cdr_cdr_car in
        ifb ginherits = NA_LOGICAL then
          result_error "Invalid ‘inherits’ argument."
        else
          run%success
            ifb ginherits <> 0 then
              setVar globals runs name val aenv
            else defineVar globals runs name val aenv in
          result_success val.

Definition do_emptyenv (call op args rho : SEXP) : result SEXP :=
  add%stack "do_emptyenv" in
  run%success Rf_checkArityCall globals runs op args call in
  result_success (R_EmptyEnv : SEXP).

Definition do_baseenv (call op args rho : SEXP) : result SEXP :=
  add%stack "do_baseenv" in
  run%success Rf_checkArityCall globals runs op args call in
  result_success (R_BaseEnv : SEXP).

Definition do_globalenv (call op args rho : SEXP) : result SEXP :=
  add%stack "do_globalenv" in
  run%success Rf_checkArityCall globals runs op args call in
  result_success (R_GlobalEnv : SEXP).

End Parameters.

