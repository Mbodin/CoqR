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


Definition do_body (call op args rho : SEXP) : result SEXP :=
  add%stack "do_body" in
    run%success Rf_checkArityCall globals runs op args call in
    read%list args_car, _, _ := args in
    let%success args_car_type := TYPEOF args_car in
    ifb args_car_type = CloSxp then
        let%success b := BODY_EXPR globals args_car in
        let%success args_car_named := NAMED args_car in
        set%named b := args_car_named in
        result_success b
    else
        (** A warning message has been left out **)
        result_success (R_NilValue : SEXP).

Definition do_makelist (call op args rho : SEXP) : result SEXP :=
  add%stack "do_makelist" in
  fold%success (n, havenames) := (0, false)
  along args
  as _, args_tag do
    ifb args_tag <> R_NilValue then
      result_success (1 + n, true)
    else result_success (1 + n, havenames) using S, runs, globals in
  let%success list := allocVector globals VecSxp n in
  let%success names :=
    if havenames then
      allocVector globals StrSxp n
    else result_success (R_NilValue : SEXP) in
  do%success args := args
  for i from 0 to n - 1 do
    read%list args_car, args_cdr, args_tag := args in
    run%success
      if havenames then
        ifb args_tag <> R_NilValue then
          let%success str := PRINTNAME args_tag in
          SET_STRING_ELT names i str
        else SET_STRING_ELT names i R_BlankString
      else result_skip in
    run%success
      let%success args_car_named := NAMED args_car in
      ifb args_car_named <> named_temporary then
        set%named op := named_plural in
        result_skip
      else result_skip in
    run%success SET_VECTOR_ELT list i args_car in
    result_success args_cdr in
  run%success
    if havenames then
      run%success setAttrib globals runs list R_NamesSymbol names in
      result_skip
    else result_skip in
  result_success list.

Definition trChar x :=
  add%stack "trChar" in
  (** We ignore any encoding issue here. **)
  CHAR x.

Definition cat_printsep sep ntot :=
  add%stack "cat_printsep" in
  let%success len := LENGTH globals sep in
  ifb sep = R_NilValue \/ len = 0 then
    result_skip
  else
    let%success str := STRING_ELT sep (ntot mod len) in
    let%success sepchar := trChar str in
    Rprint sepchar.

Definition cat_cleanup con_num :=
  add%stack "cat_cleanup" in
  run_flush con_num.

Definition do_cat (call op args rho : SEXP) : result SEXP :=
  add%stack "do_cat" in
  run%success Rf_checkArityCall globals runs op args call in
  (* Call to [PrintDefaults] formalised out. *)
  read%list args_car, args_cdr, _ := args in
  let objs := args_car in
  let args := args_cdr in
  read%list args_car, args_cdr, _ := args in
  let file := args_car in
  let%success ifile := asInteger globals file in
  let%success con := getConnection ifile in
  if negb (Rconnection_canwrite con) then
    result_error "Cannot write to this connection."
  else
    let args := args_cdr in
    read%list args_car, args_cdr, _ := args in
    let sepr := args_car in
    let%success sepr_is := isString sepr in
    if negb sepr_is then
      result_error "Invalid sep specification."
    else
      let%success seprlen := LENGTH globals sepr in
      do%success nlsep := false
      for i from 0 to seprlen - 1 do
        let%success sepri := STRING_ELT sepr i in
        let%success sepristr := CHAR sepri in
        result_success (decide (nlsep \/ sepristr = ("010"%char)%string (** '\n' **))) in
      let args := args_cdr in
      read%list args_car, args_cdr, _ := args in
      let fill := args_car in
      let%success isNum := isNumeric globals runs fill in
      let%success isLog := isLogical fill in
      let%success len := LENGTH globals fill in
      ifb ~ isNum /\ ~ isLog /\ len <> 1 then
        result_error "Invalid fill argument."
      else
        let%success pwidth :=
          if%success isLogical fill then
            let%success asLog := asLogical globals fill in
            ifb asLog = 1 then
              result_success INT_MAX (* [R_print.width] formalised out. *)
            else result_success INT_MAX
          else asInteger globals fill in
        let pwidth :=
          ifb pwidth <= 0 then
            (* A warning has been formalised out here. *)
            INT_MAX
          else pwidth in
        let args := args_cdr in
        read%list args_car, args_cdr, _ := args in
        let labs := args_car in
        let%success isStr := isString labs in
        ifb ~ isStr /\ labs <> R_NilValue then
          result_error "Invalid labels argument."
        else
          let%success lablen := R_length globals runs labs in
          let args := args_cdr in
          read%list args_car, args_cdr, _ := args in
          let%success append := asLogical globals args_car in
          ifb append = NA_LOGICAL then
            result_error "Invalid append specification."
          else
            let%success cntxt :=
              begincontext globals Ctxt_CCode R_NilValue R_BaseEnv R_BaseEnv R_NilValue R_NilValue in
            let%success nobjs := R_length globals runs objs in
            do%success (ntot, nlines) := (0, 0)
            for iobj from 0 to nobjs - 1 do
              read%Pointer s := objs at iobj in
              let%success isn := isNull s in
              let%success ntot :=
                ifb iobj <> 0 /\ ~ isn then
                  run%success cat_printsep sepr ntot in
                  result_success (1 + ntot)
                else result_success ntot in
              let%success n := R_length globals runs s in
              ifb n > 0 then
                let%success fill_in := asInteger globals fill in
                let%success nlines :=
                  ifb labs <> R_NilValue /\ iobj = 0 /\ fill_in > 0 then
                    let%success str := STRING_ELT labs (nlines mod lablen) in
                    let%success str := trChar str in
                    run%success Rprint str in
                    result_success (1 + nlines)
                  else result_success nlines in
                let%success p :=
                  if%success isString s then
                    let%success str := STRING_ELT s 0 in
                    trChar str
                  else if%success isSymbol s then
                    let%success str := PRINTNAME s in
                    CHAR str
                  else if%success isVectorAtomic s then
                    unimplemented_function "EncodeElement0"
                  else if%success isVectorList s then
                    result_success ""%string
                  else result_error "Argument can not be handled by cat." in
                do%success (ntot, nlines, p) := (ntot, nlines, p)
                for i from 0 to n - 1 do
                  run%success Rprint p in
                  ifb i < n - 1 then
                    run%success cat_printsep sepr ntot in
                    let%success p :=
                      if%success isString s then
                        let%success str := STRING_ELT s (1 + i) in
                        trChar str
                      else
                        unimplemented_function "EncodeElement0"
                      in
                    result_success (ntot, nlines, p)
                  else result_success (ntot - 1, nlines, p) in
                result_success (ntot, nlines)
              else result_success (ntot, nlines) in
            run%success
              ifb pwidth <> INT_MAX \/ nlsep then
                Rprint ("010"%char (** '\n' **))
              else result_skip in
            run%success endcontext globals runs cntxt in
            run%success cat_cleanup ifile in
            result_success (R_NilValue : SEXP).

Definition do_newenv (call op args rho : SEXP) : result SEXP :=
  add%stack "do_newenv" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, args_cdr, _ := args in
  let%success hash := asInteger globals args_car in
  let args := args_cdr in
  read%list args_car, args_cdr, _ := args in
  let enclos := args_car in
  if%success isNull enclos then
    result_error "Use of NULL environment is defunct."
  else
    let%success enclos :=
      let%success enclos_env := isEnvironment enclos in
      if enclos_env then
        result_success enclos
      else
        simple_as_environment globals enclos in
    let%success enclos_env := isEnvironment enclos in
    if negb enclos_env then
      result_error "‘enclos’ must be an environment."
    else
      let%success ans :=
        ifb hash <> 0 then
          let args := args_cdr in
          read%list args_car, _, _ := args in
          let%success size := coerceVector globals runs args_car IntSxp in
          read%Integer size_0 := size at 0 in
          run%success
            ifb size_0 = NA_INTEGER then
              write%Integer size at 0 := 0 in
              result_skip
            else result_skip in
          R_NewHashedEnv globals runs enclos size
        else NewEnvironment globals runs R_NilValue R_NilValue enclos in
      result_success ans.

Definition do_parentenv (call op args rho : SEXP) : result SEXP :=
  add%stack "do_parentenv" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, _, _ := args in
  let arg := args_car in
  let%success arg :=
    let%success arg_env := isEnvironment arg in
    if arg_env then
      result_success arg
    else
      simple_as_environment globals arg in
  let%success arg_env := isEnvironment arg in
  if negb arg_env then
    result_error "The argument is not an environment."
  else
    ifb arg = R_EmptyEnv then
      result_error "The empty environment has no parent."
    else
      read%env _, arg_env := arg in
      result_success (env_enclos arg_env).

Definition do_parentenvgets (call op args rho : SEXP) : result SEXP :=
  add%stack "do_parentenvgets" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, args_cdr, _ := args in
  let env := args_car in
  if%success isNull env then
    result_error "Use of NULL environment is defunct."
  else
    let%success env :=
      let%success env_env := isEnvironment env in
      if env_env then
        result_success env
      else
        simple_as_environment globals env in
    let%success env_env := isEnvironment env in
    if negb env_env then
      result_error "The argument is not an environment."
    else
      ifb env = R_EmptyEnv then
        result_error "Can not set the parent of the empty environment."
      else
        run%success
          if%success R_EnvironmentIsLocked globals env then
            if%success R_IsNamespaceEnv globals runs env then
              result_error "Can not set the parent environment of a namespace."
            else if%success R_IsImportsEnv globals runs env then
              result_error "Can not set the parent environment of package imports."
            else result_skip
          else result_skip in
        read%list args_cdr_car, _, _ := args_cdr in
        let parent := args_cdr_car in
        if%success isNull parent then
          result_error "Use of NULL environment is defunct."
        else
          let%success parent :=
            let%success parent_env := isEnvironment parent in
            if parent_env then
              result_success parent
            else
              simple_as_environment globals parent in
          let%success parent_env := isEnvironment parent in
          if negb parent_env then
            result_error "‘parent’ is not an environment."
          else
            run%success SET_ENCLOS env parent in
            result_success args_car.

Definition do_envir (call op args rho : SEXP) : result SEXP :=
  add%stack "do_envir" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, _, _ := args in
  let%success args_car_type := TYPEOF args_car in
  ifb args_car_type = CloSxp then
    read%clo _, args_car_clo := args_car in
    result_success (clo_env args_car_clo)
  else ifb args_car = R_NilValue then
    result_success (context_sysparent (R_GlobalContext S))
  else getAttrib globals runs args_car R_DotEnvSymbol.


Definition do_makevector (call op args rho : SEXP) : result SEXP :=
  add%stack "do_makevector" in
    run%success Rf_checkArityCall globals runs op args call in
    read%list args_car, args_cdr, _ := args in
    read%list args_cdr_car, _, _ := args_cdr in
    let%success args_cdr_car_length := R_length globals runs args_cdr_car in
    ifb args_cdr_car_length <> 1 then
        result_error "invalid 'length' argument"
    else
    let%success len := asVecSize globals args_cdr_car in
    ifb len < 0 then
        result_error "invalid 'length' argument"
    else
    let len := Z.to_nat len in
    let%success s := coerceVector globals runs args_car StrSxp in
    let%success s_length := R_length globals runs s in
    ifb s_length <> 1 then
        result_error "invalid 'mode' argument"
    else
    let%success s_0 := STRING_ELT s 0 in
    let%success s_0_char := CHAR s_0 in
    let mode := str2type s_0_char in
    let%success mode :=
       ifb (** The original C code compared [mode] to [-1] of type [SEXPTYPE],
             which is stored on 5 bits and thus equivalent to [31], that is,
             to [FreeSxp]. **)
           mode = FreeSxp
           /\ s_0_char = "double"%string then
         result_success RealSxp
       else result_success mode in
    let%success s :=
    match mode with
    | LglSxp
    | IntSxp
    | RealSxp
    | CplxSxp
    | StrSxp
    | ExprSxp
    | VecSxp
    | RawSxp => allocVector globals mode len 
    | ListSxp =>
      ifb (len : int) > INT_MAX then 
        result_error "too long for a pairlist"
      else
        let (S, s) := allocList globals len in
        result_success s                 
    | _ => result_error ("vector: cannot make a vector of mode given.")
    end in
    run%success 
    ifb mode = IntSxp \/ mode = LglSxp then
      write%VectorInteger s := ArrayList.from_list (repeat (0 : int) len) in
      result_skip
    else ifb mode = RealSxp then
      write%VectorReal s := ArrayList.from_list (repeat (0 : double) len) in
      result_skip
    else ifb mode = CplxSxp then
      write%VectorComplex s := ArrayList.from_list (repeat (make_Rcomplex 0 0) len) in
      result_skip
    else ifb mode = RawSxp then
      result_not_implemented "Raw case"
    else result_skip in 
    result_success s.
    
End Parameters.

