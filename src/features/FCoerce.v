(** Features.FCoerce.
  The function names of this file correspond to the function names
  in the file main/coerce.c. **)

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


Definition do_typeof S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_typeof" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, _, _ := args using S in
  let%success t := TYPEOF S args_car using S in
  type2rstr globals S t.

Definition do_is S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_is" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  run%success Rf_check1arg globals S args call "x" using S in
  let%success op_val := PRIMVAL runs S op using S in
  read%list args_car, _, _ := args using S in
  let%success args_car_obj := isObject S args_car using S in
  run%exit
    ifb op_val >= 100 /\ op_val < 200 /\ args_car_obj then
      let nm :=
        (ifb op_val = 100 then "is.numeric"
        else ifb op_val = 101 then "is.matrix"
        else ifb op_val = 102 then "is.array"
        else "")%string in
      let%success (disp, ans) :=
        DispatchOrEval globals runs S call op nm args rho false true using S in
      if disp then
        result_rreturn S ans
      else result_rskip S
    else result_rskip S using S in
  let%success ans := allocVector globals S LglSxp 1 using S in
  run%success
    ifb op_val = NilSxp then
      let%success isn := isNull S args_car using S in
      write%Logical ans at 0 := isn using S in
      result_skip S
    else ifb op_val = LglSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = LglSxp) using S in
      result_skip S
    else ifb op_val = IntSxp then
      let%success t := TYPEOF S args_car using S in
      let%success inh := inherits globals runs S args_car "factor" using S in
      write%Logical ans at 0 := decide (t = IntSxp /\ ~ inh) using S in
      result_skip S
    else ifb op_val = RealSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = RealSxp) using S in
      result_skip S
    else ifb op_val = CplxSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = CplxSxp) using S in
      result_skip S
    else ifb op_val = StrSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = StrSxp) using S in
      result_skip S
    else ifb op_val = SymSxp then
      let%success s4 := IS_S4_OBJECT S args_car using S in
      let%success t := TYPEOF S args_car using S in
      ifb s4 /\ t = S4Sxp then
        unimplemented_function "R_getS4DataSlot"
      else
        write%Logical ans at 0 := decide (t = SymSxp) using S in
        result_skip S
    else ifb op_val = EnvSxp then
      let%success s4 := IS_S4_OBJECT S args_car using S in
      let%success t := TYPEOF S args_car using S in
      ifb s4 /\ t = S4Sxp then
        unimplemented_function "R_getS4DataSlot"
      else
        write%Logical ans at 0 := decide (t = EnvSxp) using S in
        result_skip S
    else ifb op_val = VecSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = VecSxp \/ t = ListSxp) using S in
      result_skip S
    else ifb op_val = ListSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = ListSxp \/ t = NilSxp) using S in
      result_skip S
    else ifb op_val = ExprSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = ExprSxp) using S in
      result_skip S
    else ifb op_val = RawSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = RawSxp) using S in
      result_skip S
    else ifb op_val = 50 then
      let%success obj := OBJECT S args_car using S in
      write%Logical ans at 0 := obj using S in
      result_skip S
    else ifb op_val = 51 then
      let%success s4 := IS_S4_OBJECT S args_car using S in
      write%Logical ans at 0 := s4 using S in
      result_skip S
    else ifb op_val = 100 then
      let%success isn := isNumeric globals runs S args_car using S in
      let%success isl := isLogical S args_car using S in
      write%Logical ans at 0 := decide (isn /\ ~ isl) using S in
      result_skip S
    else ifb op_val = 101 then
      result_not_implemented "is.matrix."
    else ifb op_val = 102 then
      let%success ia := isArray globals runs S args_car using S in
      write%Logical ans at 0 := ia using S in
      result_skip S
    else ifb op_val = 200 then
      let%success t := TYPEOF S args_car using S in
      match t with
        | NilSxp
        | CharSxp
        | LglSxp
        | IntSxp
        | RealSxp
        | CplxSxp
        | StrSxp
        | RawSxp =>
          write%Logical ans at 0 := true using S in
          result_skip S
        | _ =>
          write%Logical ans at 0 := false using S in
          result_skip S
      end
    else ifb op_val = 201 then
      let%success t := TYPEOF S args_car using S in
      match t with
        | VecSxp
        | ListSxp
        | CloSxp
        | EnvSxp
        | PromSxp
        | LangSxp
        | SpecialSxp
        | BuiltinSxp
        | DotSxp
        | AnySxp
        | ExprSxp =>
          write%Logical ans at 0 := true using S in
          result_skip S
        | _ =>
          write%Logical ans at 0 := false using S in
          result_skip S
      end
    else ifb op_val = 300 then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = LangSxp) using S in
      result_skip S
    else ifb op_val = 301 then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = SymSxp \/ t = LangSxp \/ t = ExprSxp) using S in
      result_skip S
    else ifb op_val = 302 then
      result_not_implemented "is.function."
    else ifb op_val = 999 then
      result_error S "Unimplemented type single."
    else result_error S "Unimplemented predicate." using S in
  result_success S ans.

Definition do_isna S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_isna" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  run%success Rf_check1arg globals S args call "x" using S in
  let%success (disp, ans) :=
    DispatchOrEval globals runs S call op "is.na" args rho true true using S in
  if disp then
    result_success S ans
  else
    let args := ans in
    read%list args_car, _, _ := args using S in
    let x := args_car in
    let%success n := xlength globals runs S x using S in
    let%success ans := allocVector globals S LglSxp n using S in
    let%success x_type := TYPEOF S x using S in
    run%success
      let LIST_VEC_NA S s i :=
        let%success s_vec := isVector S s using S in
        let%success s_len := R_length globals runs S s using S in
        ifb ~ s_vec \/ s_len <> 1 then
          write%Logical ans at i := false using S in
          result_skip S
        else
          let%success s_type := TYPEOF S s using S in
          match s_type with
          | LglSxp
          | IntSxp =>
            let%success s_0 := INTEGER_ELT S s 0 using S in
            write%Logical ans at i := decide (s_0 = NA_INTEGER) using S in
            result_skip S
          | RealSxp =>
            let%success s_0 := REAL_ELT S s 0 using S in
            write%Logical ans at i := ISNAN s_0 using S in
            result_skip S
          | StrSxp =>
            let%success s_0 := STRING_ELT S s 0 using S in
            write%Logical ans at i := decide (s_0 = NA_STRING) using S in
            result_skip S
          | CplxSxp =>
            let%success v := COMPLEX_ELT S s 0 using S in
            write%Logical ans at i := ISNAN (Rcomplex_r v) || ISNAN (Rcomplex_i v) using S in
            result_skip S
          | _ =>
            write%Logical ans at i := false using S in
            result_skip S
          end in
      match x_type with
      | LglSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := LOGICAL_ELT S x i using S in
          write%Logical ans at i := decide (x_i = NA_LOGICAL) using S in
          result_skip S using S
      | IntSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := INTEGER_ELT S x i using S in
          write%Logical ans at i := decide (x_i = NA_INTEGER) using S in
          result_skip S using S
      | RealSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := REAL_ELT S x i using S in
          write%Logical ans at i := ISNAN x_i using S in
          result_skip S using S
      | CplxSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := COMPLEX_ELT S x i using S in
          write%Logical ans at i := ISNAN (Rcomplex_r x_i) || ISNAN (Rcomplex_i x_i) using S in
          result_skip S using S
      | StrSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := STRING_ELT S x i using S in
          write%Logical ans at i := decide (x_i = NA_STRING) using S in
          result_skip S using S
      | ListSxp =>
        do%success x := x
        for i from 0 to n - 1 do
          read%list x_car, x_cdr, _ := x using S in
          run%success LIST_VEC_NA S x_car i using S in
          result_success S x_cdr using S in
        result_skip S
      | VecSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success s := VECTOR_ELT S x i using S in
          LIST_VEC_NA S s i using S
      | RawSxp =>
        do%let
        for i from 0 to n - 1 do
          write%Logical ans at i := false using S in
          result_skip S using S
      | NilSxp => result_skip S
      | _ => result_error S "Non-(list or vector)."
      end using S in
    run%success copyDimAndNames globals runs S x ans using S in
    result_success S ans.


Definition do_isnan S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_isnan" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  run%success Rf_check1arg globals S args call "x" using S in
  let%success (disp, ans) :=
    DispatchOrEval globals runs S call op "is.na" args rho true true using S in
  if disp then
    result_success S ans
  else
    let args := ans in
    read%list args_car, _, _ := args using S in
    let x := args_car in
    let%success n := xlength globals runs S x using S in
    let%success ans := allocVector globals S LglSxp n using S in
    let%success x_type := TYPEOF S x using S in
    run%success
      match x_type with
      | StrSxp
      | RawSxp
      | NilSxp
      | LglSxp
      | IntSxp =>
        do%let
        for i from 0 to n - 1 do
          write%Logical ans at i := false using S in
          result_skip S using S
      | RealSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := REAL_ELT S x i using S in
          write%Logical ans at i := R_IsNaN x_i using S in
          result_skip S using S
      | CplxSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := COMPLEX_ELT S x i using S in
          write%Logical ans at i := R_IsNaN (Rcomplex_r x_i) || R_IsNaN (Rcomplex_i x_i) using S in
          result_skip S using S
      | _ => result_error S "Default method not implemented for this type."
      end using S in
    run%success copyDimAndNames globals runs S x ans using S in
    result_success S ans.

Definition do_isvector S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_isvector" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  let x := args_car in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let%success args_cdr_car_str := isString S args_cdr_car using S in
  let%success args_cdr_car_len := LENGTH globals S args_cdr_car using S in
  ifb ~ args_cdr_car_str \/ args_cdr_car_len <> 1 then
    result_error S "Invalid ‘mode’ argument."
  else
    let%success args_cdr_car_0 := STRING_ELT S args_cdr_car 0 using S in
    let%success stype := CHAR S args_cdr_car_0 using S in
    let stype := ifb stype = "name"%string then "symbol"%string else stype in
    let%success ans := allocVector globals S LglSxp 1 using S in
    run%success
      ifb stype = "any"%string then
        let%success x_vec := isVector S x using S in
        write%Logical ans at 0 := x_vec using S in
        result_skip S
      else ifb stype = "numeric"%string then
        let%success x_vec := isVector S x using S in
        let%success x_lgl := isLogical S x using S in
        write%Logical ans at 0 := x_vec && negb x_lgl using S in
        result_skip S
      else unimplemented_function "type2char" using S in
    run%success
      read%Logical ans_0 := ans at 0 using S in
      let%success args_car_attr := ATTRIB S args_car using S in
      ifb ans_0 <> 0 /\ args_car_attr <> R_NilValue then
        let a := args_car_attr in
        fold%let
        along a
        as _, a_tag do
          ifb a_tag <> R_NamesSymbol then
            write%Logical ans at 0 := false using S in
            result_skip S
          else result_skip S using S, runs, globals
      else result_skip S using S in
    result_success S ans.

Definition do_substitute S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_substitute" in
    (** argument matching **)
    let%success argList := matchArgs globals runs S do_substitute_do_substitute_formals  args call using S in

    read%list argList_car, argList_cdr, _ := argList using S in
    read%list argList_cdr_car, _, _ := argList_cdr using S in
    let%success env :=
        (** set up the environment for substitution **)
        ifb argList_cdr_car = R_MissingArg then
            result_success S rho
        else  
            eval globals runs S argList_cdr_car rho
    using S in 
    let%success env :=
        (** For historical reasons, don't substitute in R_GlobalEnv **)
        ifb env = R_GlobalEnv then
            result_success S (R_NilValue : SEXP)
        else
            let%success env_type := TYPEOF S env using S in
            ifb env_type = VecSxp then
                let%success env_vecToPairList := VectorToPairList globals runs S env using S in
                NewEnvironment globals runs S R_NilValue env_vecToPairList R_BaseEnv
        else ifb env_type = ListSxp then
            let%success env_duplicate := duplicate globals runs S env using S in
            NewEnvironment globals runs S R_NilValue env_duplicate R_BaseEnv
        else
            result_success S env
    using S in
    let%success env_type := TYPEOF S env using S in
    ifb env <> R_NilValue /\ env_type <> EnvSxp then
        result_error S "invalid environment specified"
    else
        let%success argList_car_duplicate := duplicate globals runs S argList_car using S in
        let (S, t) := CONS globals S argList_car_duplicate R_NilValue in
        let%success s := substituteList globals runs S t env using S in
        read%list s_car, _, _ := s using S in
        result_success S s_car
.

End Parameters.

