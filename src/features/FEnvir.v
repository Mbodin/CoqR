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


Definition do_missing S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_missing" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  run%success Rf_check1arg globals S args call "x" using S in
  read%list args_car, _, _ := args using S in
  let%success sym :=
    let sym := args_car in
    let%success sym_str := isString S sym using S in
    let%success sym_len := R_length globals runs S sym using S in
    ifb sym_str /\ sym_len = 1 then
      read%Pointer args_car_0 := args_car at 0 using S in
      installTrChar globals runs S args_car_0
    else result_success S sym using S in
  let s := sym in
  let%success sym_sym := isSymbol S sym using S in
  if negb sym_sym then
    result_error S "Invalid use."
  else
    let%success (ddv, sym) :=
      if%success DDVAL S sym using S then
        let%success ddv := ddVal S sym using S in
        result_success S (ddv, R_DotsSymbol : SEXP)
      else result_success S (0, sym) using S in
    let%success t := findVarLocInFrame globals runs S rho sym using S in
    let%success rval := allocVector globals S LglSxp 1 using S in
    ifb t <> R_NilValue then
      read%list t_car, _, _ := t using S in
      let%exit t :=
        if%success DDVAL S s using S then
          let%success t_car_len := R_length globals runs S t_car using S in
          ifb t_car_len < ddv \/ t_car = R_MissingArg then
            write%Logical rval at 0 := 1 using S in
            result_rreturn S rval
          else
            let%success t := nthcdr globals runs S t_car (ddv - 1) using S in
            result_rsuccess S t
        else result_rsuccess S t using S in
      run%exit
        let%success t_mis := MISSING S t using S in
        ifb t_mis <> 0 \/ t_car = R_MissingArg then
          write%Logical rval at 0 := 1 using S in
          result_rreturn S rval
        else result_rskip S using S in
      (** This is the translation of the [havebinding] label. **)
      let t := t_car in
      let%success t_type := TYPEOF S t using S in
      ifb t_type <> PromSxp then
        write%Logical rval at 0 := 0 using S in
        result_success S rval
      else
        let%success t := findRootPromise globals runs S t using S in
        let%success t_is :=
          let%success t := PREXPR globals S t using S in
          isSymbol S t using S in
        if negb t_is then
          write%Logical rval at 0 := 0 using S in
          result_success S rval
        else
          let%success t_expr := PREXPR globals S t using S in
          let%success t_env :=
             read%prom _, t_prom := t using S in
             result_success S (prom_env t_prom) using S in
          let%success ism := R_isMissing globals runs S t_expr t_env using S in
          write%Logical rval at 0 := ism using S in
          result_success S rval
    else result_error S "It can only be used for arguments.".

Definition do_get (S : state) (call op args rho : SEXP) : result SEXP :=
  add%stack "do_get" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  unimplemented_function "do_get".

Definition do_assign S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_assign" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  let%success args_car_str := isString S args_car using S in
  let%success args_car_len := R_length globals runs S args_car using S in
  ifb ~ args_car_str \/ args_car_len = 0 then
    result_error S "Invalid first argument"
  else
    (** A potential warning has been formalised out here. **)
    let%success args_car_0 := STRING_ELT S args_car 0 using S in
    let%success name := installTrChar globals runs S args_car_0 using S in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
    let val := args_cdr_car in
    read%list args_cdr_cdr_car, args_cdr_cdr_cdr, _ := args_cdr_cdr using S in
    let aenv := args_cdr_cdr_car in
    let%success aenv_type := TYPEOF S aenv using S in
    ifb aenv_type = NilSxp then
      result_error S "Use of NULL environment is defunct."
    else
      let%success aenv :=
        ifb aenv_type <> EnvSxp then
          result_success S aenv
        else
          simple_as_environment globals S aenv using S in
      let%success aenv_type := TYPEOF S aenv using S in
      ifb aenv_type <> EnvSxp then
        result_error S "Invalid ‘envir’ argument."
      else
        read%list args_cdr_cdr_cdr_car, _, _ := args_cdr_cdr_cdr using S in
        let%success ginherits := asLogical globals S args_cdr_cdr_cdr_car using S in
        ifb ginherits = NA_LOGICAL then
          result_error S "Invalid ‘inherits’ argument."
        else
          run%success
            ifb ginherits <> 0 then
              setVar globals runs S name val aenv
            else defineVar globals runs S name val aenv using S in
          result_success S val.

Definition do_emptyenv S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_emptyenv" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  result_success S (R_EmptyEnv : SEXP).

Definition do_baseenv S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_baseenv" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  result_success S (R_BaseEnv : SEXP).

Definition do_globalenv S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_globalenv" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  result_success S (R_GlobalEnv : SEXP).

End Parameters.

