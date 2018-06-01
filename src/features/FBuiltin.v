(** Features.FBuiltin.
  The function names of this file correspond to the function names
  in the file main/builtin.c. **)

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
Require Import Ascii.
Require Import Rcore.
Require Import FUtil.
Require Import FPrintutils.
Require Import FConnections.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition do_body S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_body" in
    run%success Rf_checkArityCall globals runs S op args call using S in
    read%list args_car, _, _ := args using S in
    let%success args_car_type := TYPEOF S args_car using S in
    ifb args_car_type = CloSxp then
        let%success b := BODY_EXPR globals S args_car using S in
        let%success args_car_named := NAMED S args_car using S in
        set%named b := args_car_named using S in
        result_success S b
    else
        (** A warning message has been left out **)
        result_success S (R_NilValue : SEXP).

Definition do_makelist S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_makelist" in
  fold%success (n, havenames) := (0, false)
  along args
  as _, args_tag do
    ifb args_tag <> R_NilValue then
      result_success S (1 + n, true)
    else result_success S (1 + n, havenames) using S, runs, globals in
  let%success list := allocVector globals S VecSxp n using S in
  let%success names :=
    if havenames then
      allocVector globals S StrSxp n
    else result_success S (R_NilValue : SEXP) using S in
  do%success args := args
  for i from 0 to n - 1 do
    read%list args_car, args_cdr, args_tag := args using S in
    run%success
      if havenames then
        ifb args_tag <> R_NilValue then
          let%success str := PRINTNAME S args_tag using S in
          SET_STRING_ELT S names i str
        else SET_STRING_ELT S names i R_BlankString
      else result_skip S using S in
    run%success
      let%success args_car_named := NAMED S args_car using S in
      ifb args_car_named <> named_temporary then
        set%named op := named_plural using S in
        result_skip S
      else result_skip S using S in
    run%success SET_VECTOR_ELT S list i args_car using S in
    result_success S args_cdr using S in
  run%success
    if havenames then
      run%success setAttrib globals runs S list R_NamesSymbol names using S in
      result_skip S
    else result_skip S using S in
  result_success S list.

Definition trChar S x :=
  add%stack "trChar" in
  (** We ignore any encoding issue here. **)
  CHAR S x.

Definition cat_printsep S sep ntot :=
  add%stack "cat_printsep" in
  let%success len := LENGTH globals S sep using S in
  ifb sep = R_NilValue \/ len = 0 then
    result_skip S
  else
    let%success str := STRING_ELT S sep (ntot mod len) using S in
    let%success sepchar := trChar S str using S in
    Rprint S sepchar.

Definition cat_cleanup S con_num :=
  add%stack "cat_cleanup" in
  run_flush S con_num.

Definition do_cat S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_cat" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  (* Call to [PrintDefaults] formalised out. *)
  read%list args_car, args_cdr, _ := args using S in
  let objs := args_car in
  let args := args_cdr in
  read%list args_car, args_cdr, _ := args using S in
  let file := args_car in
  let%success ifile := asInteger globals S file using S in
  let%success con := getConnection S ifile using S in
  if negb (Rconnection_canwrite con) then
    result_error S "Cannot write to this connection."
  else
    let args := args_cdr in
    read%list args_car, args_cdr, _ := args using S in
    let sepr := args_car in
    let%success sepr_is := isString S sepr using S in
    if negb sepr_is then
      result_error S "Invalid sep specification."
    else
      let%success seprlen := LENGTH globals S sepr using S in
      do%success nlsep := false
      for i from 0 to seprlen - 1 do
        let%success sepri := STRING_ELT S sepr i using S in
        let%success sepristr := CHAR S sepri using S in
        result_success S (decide (nlsep \/ sepristr = ("010"%char)%string (** '\n' **))) using S in
      let args := args_cdr in
      read%list args_car, args_cdr, _ := args using S in
      let fill := args_car in
      let%success isNum := isNumeric globals runs S fill using S in
      let%success isLog := isLogical S fill using S in
      let%success len := LENGTH globals S fill using S in
      ifb ~ isNum /\ ~ isLog /\ len <> 1 then
        result_error S "Invalid fill argument."
      else
        let%success pwidth :=
          if%success isLogical S fill using S then
            let%success asLog := asLogical globals S fill using S in
            ifb asLog = 1 then
              result_success S INT_MAX (* [R_print.width] formalised out. *)
            else result_success S INT_MAX
          else asInteger globals S fill using S in
        let pwidth :=
          ifb pwidth <= 0 then
            (* A warning has been formalised out here. *)
            INT_MAX
          else pwidth in
        let args := args_cdr in
        read%list args_car, args_cdr, _ := args using S in
        let labs := args_car in
        let%success isStr := isString S labs using S in
        ifb ~ isStr /\ labs <> R_NilValue then
          result_error S "Invalid labels argument."
        else
          let%success lablen := R_length globals runs S labs using S in
          let args := args_cdr in
          read%list args_car, args_cdr, _ := args using S in
          let%success append := asLogical globals S args_car using S in
          ifb append = NA_LOGICAL then
            result_error S "Invalid append specification."
          else
            let%success cntxt :=
              begincontext globals S Ctxt_CCode R_NilValue R_BaseEnv R_BaseEnv R_NilValue R_NilValue using S in
            let%success nobjs := R_length globals runs S objs using S in
            do%success (ntot, nlines) := (0, 0)
            for iobj from 0 to nobjs - 1 do
              read%Pointer s := objs at iobj using S in
              let%success isn := isNull S s using S in
              let%success ntot :=
                ifb iobj <> 0 /\ ~ isn then
                  run%success cat_printsep S sepr ntot using S in
                  result_success S (1 + ntot)
                else result_success S ntot using S in
              let%success n := R_length globals runs S s using S in
              ifb n > 0 then
                let%success fill_in := asInteger globals S fill using S in
                let%success nlines :=
                  ifb labs <> R_NilValue /\ iobj = 0 /\ fill_in > 0 then
                    let%success str := STRING_ELT S labs (nlines mod lablen) using S in
                    let%success str := trChar S str using S in
                    run%success Rprint S str using S in
                    result_success S (1 + nlines)
                  else result_success S nlines using S in
                let%success p :=
                  if%success isString S s using S then
                    let%success str := STRING_ELT S s 0 using S in
                    trChar S str
                  else if%success isSymbol S s using S then
                    let%success str := PRINTNAME S s using S in
                    CHAR S str
                  else if%success isVectorAtomic S s using S then
                    unimplemented_function "EncodeElement0"
                  else if%success isVectorList S s using S then
                    result_success S ""%string
                  else result_error S "Argument can not be handled by cat." using S in
                do%success (ntot, nlines, p) := (ntot, nlines, p)
                for i from 0 to n - 1 do
                  run%success Rprint S p using S in
                  ifb i < n - 1 then
                    run%success cat_printsep S sepr ntot using S in
                    let%success p :=
                      if%success isString S s using S then
                        let%success str := STRING_ELT S s (1 + i) using S in
                        trChar S str
                      else
                        unimplemented_function "EncodeElement0"
                      using S in
                    result_success S (ntot, nlines, p)
                  else result_success S (ntot - 1, nlines, p) using S in
                result_success S (ntot, nlines)
              else result_success S (ntot, nlines) using S in
            run%success
              ifb pwidth <> INT_MAX \/ nlsep then
                Rprint S ("010"%char (** '\n' **))
              else result_skip S using S in
            run%success endcontext globals runs S cntxt using S in
            run%success cat_cleanup S ifile using S in
            result_success S (R_NilValue : SEXP).

Definition do_newenv S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_newenv" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  let%success hash := asInteger globals S args_car using S in
  let args := args_cdr in
  read%list args_car, args_cdr, _ := args using S in
  let enclos := args_car in
  if%success isNull S enclos using S then
    result_error S "Use of NULL environment is defunct."
  else
    let%success enclos :=
      let%success enclos_env := isEnvironment S enclos using S in
      if enclos_env then
        result_success S enclos
      else
        simple_as_environment globals S enclos using S in
    let%success enclos_env := isEnvironment S enclos using S in
    if negb enclos_env then
      result_error S "‘enclos’ must be an environment."
    else
      let%success ans :=
        ifb hash <> 0 then
          let args := args_cdr in
          read%list args_car, _, _ := args using S in
          let%success size := coerceVector globals runs S args_car IntSxp using S in
          read%Integer size_0 := size at 0 using S in
          run%success
            ifb size_0 = NA_INTEGER then
              write%Integer size at 0 := 0 using S in
              result_skip S
            else result_skip S using S in
          R_NewHashedEnv globals runs S enclos size
        else NewEnvironment globals runs S R_NilValue R_NilValue enclos using S in
      result_success S ans.

Definition do_parentenv S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_parentenv" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, _, _ := args using S in
  let arg := args_car in
  let%success arg :=
    let%success arg_env := isEnvironment S arg using S in
    if arg_env then
      result_success S arg
    else
      simple_as_environment globals S arg using S in
  let%success arg_env := isEnvironment S arg using S in
  if negb arg_env then
    result_error S "The argument is not an environment."
  else
    ifb arg = R_EmptyEnv then
      result_error S "The empty environment has no parent."
    else
      read%env _, arg_env := arg using S in
      result_success S (env_enclos arg_env).

Definition do_parentenvgets S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_parentenvgets" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  let env := args_car in
  if%success isNull S env using S then
    result_error S "Use of NULL environment is defunct."
  else
    let%success env :=
      let%success env_env := isEnvironment S env using S in
      if env_env then
        result_success S env
      else
        simple_as_environment globals S env using S in
    let%success env_env := isEnvironment S env using S in
    if negb env_env then
      result_error S "The argument is not an environment."
    else
      ifb env = R_EmptyEnv then
        result_error S "Can not set the parent of the empty environment."
      else
        run%success
          if%success R_EnvironmentIsLocked globals S env using S then
            if%success R_IsNamespaceEnv globals runs S env using S then
              result_error S "Can not set the parent environment of a namespace."
            else if%success R_IsImportsEnv globals runs S env using S then
              result_error S "Can not set the parent environment of package imports."
            else result_skip S
          else result_skip S using S in
        read%list args_cdr_car, _, _ := args_cdr using S in
        let parent := args_cdr_car in
        if%success isNull S parent using S then
          result_error S "Use of NULL environment is defunct."
        else
          let%success parent :=
            let%success parent_env := isEnvironment S parent using S in
            if parent_env then
              result_success S parent
            else
              simple_as_environment globals S parent using S in
          let%success parent_env := isEnvironment S parent using S in
          if negb parent_env then
            result_error S "‘parent’ is not an environment."
          else
            run%success SET_ENCLOS S env parent using S in
            result_success S args_car.

Definition do_envir S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_envir" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, _, _ := args using S in
  let%success args_car_type := TYPEOF S args_car using S in
  ifb args_car_type = CloSxp then
    read%clo _, args_car_clo := args_car using S in
    result_success S (clo_env args_car_clo)
  else ifb args_car = R_NilValue then
    result_success S (context_sysparent (R_GlobalContext S))
  else getAttrib globals runs S args_car R_DotEnvSymbol.


Definition do_makevector S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_makevector" in
    run%success Rf_checkArityCall globals runs S op args call using S in
    read%list args_car, args_cdr, _ := args using S in
    read%list args_cdr_car, _, _ := args_cdr using S in
    let%success args_cdr_car_length = R_length globals runs S args_cdr_car using S in
    ifb args_cdr_car_length <> 1 then
        result_error S "invalid 'length' argument"
    else
    let%success len := asVecSize S args_cdr_car using S in
    ifb len < 0 then
        result_error S "invalid 'length' argument"
    else
    let%success s := coerceVector globals runs S args_car StrSxp using S in
    let%success s_length := R_length globals runs S s using S in
    ifb s_length <> 1 then
        result_error S "invalid 'mode' argument"
    else
    let%success s_0 := STRING_ELT S s 0 using S in
    let%success s_0_char := CHAR S s_0 using S in
    let%success mode := str2type S s_0_char using S in
    let%success mode := ifb mode = NilSxp /\ s_0_char = "double" then
                           result_success S RealSxp
                       else result_success S mode
    let%success s :=
    match mode with
    | LglSxp
    | IntSxp
    | RealSxp
    | CplxSxp
    | StrSxp
    | ExprSxp
    | VecSxp
    | RawSxp => allocVector globals S mode len 
    | ListSxp => if len > INT_MAX then 
                    result_error S "too long for a pairlist"
                else
                    let%success (S, s) := allocList globals S len using S in
                    result_success S s                 
    | _ => result_error S ("vector: cannot make a vector of mode given.")
    end using S in
    run%success 
    ifb mode = IntSxp \/ mode = LglSxp then
        (** Memzero **)
    else ifb mode = RealSxp then
        (** Memzero **)
    else ifb mode = CplxSxp then
        (** Memzero **)
    else ifb mode = RawSxp then
        (** Memzero **)
    using S in 
    result S s.
    
End Parameters.

