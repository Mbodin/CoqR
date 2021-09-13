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
From CoqR Require Import Rcore.
Require Import FUtil.

Section Parameters.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

Definition isMatrix s :=
  add%stack "isMatrix" in
  if%success isVector s then
    let%success t := getAttrib globals runs s R_DimSymbol in
    let%success t_type := TYPEOF t in
    let%success t_length := LENGTH globals t in
    ifb t_type = IntSxp /\ t_length = 2 then
      result_success true
    else
      result_success false
  else
    result_success false.

Definition do_asCharacterFactor (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_asCharacterfactor" in
  run%success Rf_checkArityCall globals runs op args call in
  run%success Rf_check1arg globals args call "x" in
  read%list args_car, _, _ := args in
  let x := args_car in
  asCharacterFactor globals runs x
.

Definition do_typeof (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_typeof" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, _, _ := args in
  let%success t := TYPEOF args_car in
  type2rstr globals t.

Definition do_is (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_is" in
  run%success Rf_checkArityCall globals runs op args call in
  run%success Rf_check1arg globals args call "x" in
  let%success op_val := PRIMVAL runs op in
  read%list args_car, _, _ := args in
  let%success args_car_obj := isObject args_car in
  run%exit
    ifb op_val >= 100 /\ op_val < 200 /\ args_car_obj then
      let nm :=
        (ifb op_val = 100 then "is.numeric"
        else ifb op_val = 101 then "is.matrix"
        else ifb op_val = 102 then "is.array"
        else "")%string in
      let%success (disp, ans) :=
        DispatchOrEval globals runs call op nm args rho false true in
      if disp then
        result_rreturn ans
      else result_rskip
    else result_rskip in
  let%success ans := allocVector globals LglSxp 1 in
  run%success
    ifb op_val = NilSxp then  (* is.null *)
      let%success isn := isNull args_car in
      write%Logical ans at 0 := isn in
      result_skip
    else ifb op_val = LglSxp then  (* is.logical *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = LglSxp) in
      result_skip
    else ifb op_val = IntSxp then  (* is.integer *)
      let%success t := TYPEOF args_car in
      let%success inh := inherits globals runs args_car "factor" in
      write%Logical ans at 0 := decide (t = IntSxp /\ ~ inh) in
      result_skip
    else ifb op_val = RealSxp then  (* is.double *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = RealSxp) in
      result_skip
    else ifb op_val = CplxSxp then  (* is.complex *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = CplxSxp) in
      result_skip
    else ifb op_val = StrSxp then  (* is.character *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = StrSxp) in
      result_skip
    else ifb op_val = SymSxp then  (* is.symbol === is.name *)
      let%success s4 := IS_S4_OBJECT args_car in
      let%success t := TYPEOF args_car in
      ifb s4 /\ t = S4Sxp then
        unimplemented_function "R_getS4DataSlot"
      else
        write%Logical ans at 0 := decide (t = SymSxp) in
        result_skip
    else ifb op_val = EnvSxp then  (* is.environment *)
      let%success s4 := IS_S4_OBJECT args_car in
      let%success t := TYPEOF args_car in
      ifb s4 /\ t = S4Sxp then
        unimplemented_function "R_getS4DataSlot"
      else
        write%Logical ans at 0 := decide (t = EnvSxp) in
        result_skip
    else ifb op_val = VecSxp then  (* is.list *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = VecSxp \/ t = ListSxp) in
      result_skip
    else ifb op_val = ListSxp then  (* is.pairlist *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = ListSxp \/ t = NilSxp) in
      result_skip
    else ifb op_val = ExprSxp then  (* is.expression *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = ExprSxp) in
      result_skip
    else ifb op_val = RawSxp then  (* is.raw *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = RawSxp) in
      result_skip
    else ifb op_val = 50 then  (* is.object *)
      let%success obj := OBJECT args_car in
      write%Logical ans at 0 := obj in
      result_skip
    else ifb op_val = 51 then  (* isS4 *)
      let%success s4 := IS_S4_OBJECT args_car in
      write%Logical ans at 0 := s4 in
      result_skip
    else ifb op_val = 100 then  (* is.numeric *)
      let%success isn := isNumeric globals runs args_car in
      let%success isl := isLogical args_car in
      write%Logical ans at 0 := decide (isn /\ ~ isl) in
      result_skip
    else ifb op_val = 101 then  (* is.matrix *)
      let%success args_car_isMatrix := isMatrix args_car in
      write%Logical ans at 0 := args_car_isMatrix in
      result_skip
    else ifb op_val = 102 then  (* is.array *)
      let%success ia := isArray globals runs args_car in
      write%Logical ans at 0 := ia in
      result_skip
    else ifb op_val = 200 then  (* is.atomic *)
      let%success t := TYPEOF args_car in
      match t with
        | NilSxp
        | CharSxp
        | LglSxp
        | IntSxp
        | RealSxp
        | CplxSxp
        | StrSxp
        | RawSxp =>
          write%Logical ans at 0 := true in
          result_skip
        | _ =>
          write%Logical ans at 0 := false in
          result_skip
      end
    else ifb op_val = 201 then  (* is.recursive *)
      let%success t := TYPEOF args_car in
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
          write%Logical ans at 0 := true in
          result_skip
        | _ =>
          write%Logical ans at 0 := false in
          result_skip
      end
    else ifb op_val = 300 then  (* is.call *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = LangSxp) in
      result_skip
    else ifb op_val = 301 then  (* is.language *)
      let%success t := TYPEOF args_car in
      write%Logical ans at 0 := decide (t = SymSxp \/ t = LangSxp \/ t = ExprSxp) in
      result_skip
    else ifb op_val = 302 then  (* is.function *)
      let%success args_car_isFunction := isFunction args_car in
      write%Logical ans at 0 := args_car_isFunction in
      result_skip
    else ifb op_val = 999 then  (* is.single *)
      result_error "Unimplemented type single."
    else result_error "Unimplemented predicate." in
  result_success ans.

Definition do_isna (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_isna" in
  run%success Rf_checkArityCall globals runs op args call in
  run%success Rf_check1arg globals args call "x" in
  let%success (disp, ans) :=
    DispatchOrEval globals runs call op "is.na" args rho true true in
  if disp then
    result_success ans
  else
    let args := ans in
    read%list args_car, _, _ := args in
    let x := args_car in
    let%success n := xlength globals runs x in
    let%success ans := allocVector globals LglSxp n in
    let%success x_type := TYPEOF x in
    run%success
      let LIST_VEC_NA s i :=
        let%success s_vec := isVector s in
        let%success s_len := R_length globals runs s in
        ifb ~ s_vec \/ s_len <> 1 then
          write%Logical ans at i := false in
          result_skip
        else
          let%success s_type := TYPEOF s in
          match s_type with
          | LglSxp
          | IntSxp =>
            let%success s_0 := INTEGER_ELT s 0 in
            write%Logical ans at i := decide (s_0 = NA_INTEGER) in
            result_skip
          | RealSxp =>
            let%success s_0 := REAL_ELT s 0 in
            write%Logical ans at i := ISNAN s_0 in
            result_skip
          | StrSxp =>
            let%success s_0 := STRING_ELT s 0 in
            write%Logical ans at i := decide (s_0 = NA_STRING) in
            result_skip
          | CplxSxp =>
            let%success v := COMPLEX_ELT s 0 in
            write%Logical ans at i := ISNAN (Rcomplex_r v) || ISNAN (Rcomplex_i v) in
            result_skip
          | _ =>
            write%Logical ans at i := false in
            result_skip
          end in
      match x_type with
      | LglSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := LOGICAL_ELT x i in
          write%Logical ans at i := decide (x_i = NA_LOGICAL) in
          result_skip
      | IntSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := INTEGER_ELT x i in
          write%Logical ans at i := decide (x_i = NA_INTEGER) in
          result_skip
      | RealSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := REAL_ELT x i in
          write%Logical ans at i := ISNAN x_i in
          result_skip
      | CplxSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := COMPLEX_ELT x i in
          write%Logical ans at i := ISNAN (Rcomplex_r x_i) || ISNAN (Rcomplex_i x_i) in
          result_skip
      | StrSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := STRING_ELT x i in
          write%Logical ans at i := decide (x_i = NA_STRING) in
          result_skip
      | ListSxp =>
        do%success x := x
        for i from 0 to n - 1 do
          read%list x_car, x_cdr, _ := x in
          run%success LIST_VEC_NA x_car i in
          result_success x_cdr in
        result_skip
      | VecSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success s := VECTOR_ELT x i in
          LIST_VEC_NA s i
      | RawSxp =>
        do%let
        for i from 0 to n - 1 do
          write%Logical ans at i := false in
          result_skip
      | NilSxp => result_skip
      | _ => result_error "Non-(list or vector)."
      end in
    run%success copyDimAndNames globals runs x ans in
    result_success ans.


Definition do_isnan (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_isnan" in
  run%success Rf_checkArityCall globals runs op args call in
  run%success Rf_check1arg globals args call "x" in
  let%success (disp, ans) :=
    DispatchOrEval globals runs call op "is.na" args rho true true in
  if disp then
    result_success ans
  else
    let args := ans in
    read%list args_car, _, _ := args in
    let x := args_car in
    let%success n := xlength globals runs x in
    let%success ans := allocVector globals LglSxp n in
    let%success x_type := TYPEOF x in
    run%success
      match x_type with
      | StrSxp
      | RawSxp
      | NilSxp
      | LglSxp
      | IntSxp =>
        do%let
        for i from 0 to n - 1 do
          write%Logical ans at i := false in
          result_skip
      | RealSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := REAL_ELT x i in
          write%Logical ans at i := R_IsNaN x_i in
          result_skip
      | CplxSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := COMPLEX_ELT x i in
          write%Logical ans at i := R_IsNaN (Rcomplex_r x_i) || R_IsNaN (Rcomplex_i x_i) in
          result_skip
      | _ => result_error "Default method not implemented for this type."
      end in
    run%success copyDimAndNames globals runs x ans in
    result_success ans.

Definition do_isvector (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_isvector" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, args_cdr, _ := args in
  let x := args_car in
  read%list args_cdr_car, _, _ := args_cdr in
  let%success args_cdr_car_str := isString args_cdr_car in
  let%success args_cdr_car_len := LENGTH globals args_cdr_car in
  ifb ~ args_cdr_car_str \/ args_cdr_car_len <> 1 then
    result_error "Invalid ‘mode’ argument."
  else
    let%success args_cdr_car_0 := STRING_ELT args_cdr_car 0 in
    let%success stype := CHAR args_cdr_car_0 in
    let stype := ifb stype = "name"%string then "symbol"%string else stype in
    let%success ans := allocVector globals LglSxp 1 in
    run%success
      ifb stype = "any"%string then
        let%success x_vec := isVector x in
        write%Logical ans at 0 := x_vec in
        result_skip
      else ifb stype = "numeric"%string then
        let%success x_vec := isVector x in
        let%success x_lgl := isLogical x in
        write%Logical ans at 0 := x_vec && negb x_lgl in
        result_skip
      else unimplemented_function "type2char" in
    run%success
      read%Logical ans_0 := ans at 0 in
      let%success args_car_attr := ATTRIB args_car in
      ifb ans_0 <> 0 /\ args_car_attr <> R_NilValue then
        let a := args_car_attr in
        fold%let
        along a
        as _, a_tag do
          ifb a_tag <> R_NamesSymbol then
            write%Logical ans at 0 := false in
            result_skip
          else result_skip using runs
      else result_skip in
    result_success ans.

Definition do_substitute (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_substitute" in
  (** argument matching **)
  let%success argList := matchArgs globals runs do_substitute_do_substitute_formals  args call in

  read%list argList_car, argList_cdr, _ := argList in
  read%list argList_cdr_car, _, _ := argList_cdr in
  let%success env :=
    (** set up the environment for substitution **)
    ifb argList_cdr_car = R_MissingArg then
      result_success rho
    else
      eval globals runs argList_cdr_car rho
  in
  let%success env :=
    (** For historical reasons, don't substitute in R_GlobalEnv **)
    ifb env = R_GlobalEnv then
      result_success (R_NilValue : SEXP)
    else
    let%success env_type := TYPEOF env in
    ifb env_type = VecSxp then
      let%success env_vecToPairList := VectorToPairList globals runs env in
      NewEnvironment globals runs R_NilValue env_vecToPairList R_BaseEnv
    else ifb env_type = ListSxp then
      let%success env_duplicate := duplicate globals runs env in
      NewEnvironment globals runs R_NilValue env_duplicate R_BaseEnv
    else
      result_success env
  in
  let%success env_type := TYPEOF env in
  ifb env <> R_NilValue /\ env_type <> EnvSxp then
    result_error "invalid environment specified"
  else
    let%success argList_car_duplicate := duplicate globals runs argList_car in
    let%success t := CONS globals argList_car_duplicate R_NilValue in
    let%success s := substituteList globals runs t env in
    read%list s_car, _, _ := s in
    result_success s_car
.

Definition do_quote (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_quote" in
  run%success Rf_checkArityCall globals runs op args call in
  run%success Rf_check1arg globals args call "x" in
  read%list args_car, _, _ := args in
  let val := args_car in
  set%named val := named_plural in
  result_success val
.

Definition CLEAR_ATTRIB x :=
  add%stack "CLEAR_ATTRIB" in
  let%success x_attrib := ATTRIB x in

  ifb x_attrib <> R_NilValue then
    run%success SET_ATTRIB x R_NilValue in
    if%success OBJECT x then
      SET_OBJECT x false
    in
    if%success IS_S4_OBJECT x then
      UNSET_S4_OBJECT x
    in result_skip
  else
    result_skip.

Definition ascommon (call u : SEXP) type :=
  add%stack "ascommon" in
  ifb type = CloSxp then
    unimplemented_function "asFunction"
  else
    let%success u_isVector := isVector u in
    let%success u_isList := isList globals u in
    let%success u_isLanguage := isLanguage globals u in
    let%success u_isSymbol := isSymbol u in
    ifb u_isVector \/ u_isList \/ u_isLanguage \/ (u_isSymbol /\ type = ExprSxp) then
      let%success v :=
      let%success u_type := TYPEOF u in
      ifb type <> AnySxp /\ u_type <> type then
        coerceVector globals runs u type
      else
        result_success u
      in

      let%success u_type := TYPEOF u in
      run%success
      ifb type = ListSxp /\ ~ (u_type = LangSxp \/ u_type = ListSxp \/ u_type = ExprSxp \/ u_type = VecSxp) then
        let%success v_mbr := MAYBE_REFERENCED v in
        let%success v := if v_mbr then shallow_duplicate globals runs v else result_success v in
        CLEAR_ATTRIB v
      else result_skip
      in
      result_success v
    else ifb u_isSymbol /\ type = StrSxp then
      let%success u_printname := PRINTNAME u in
      ScalarString globals u_printname
    else ifb u_isSymbol /\ type = SymSxp then
      result_success u
    else ifb u_isSymbol /\ type = VecSxp then
      let%success v := allocVector globals VecSxp 1 in
      run%success SET_VECTOR_ELT v 0 u in
      result_success v
    else result_error "Coercing error".

Definition do_asatomic (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_asatomic" in
  let type := StrSxp in
  let%success op0 := PRIMVAL runs op in

  run%success Rf_check1arg globals args call "x" in

  let%success (name, type) :=
  match op0 : int with
  | 0 => result_success ("as.character"%string, type)
  | 1 => result_success ("as.integer"%string, IntSxp)
  | 2 => result_success ("as.double"%string, RealSxp)
  | 3 => result_success ("as.complex"%string, CplxSxp)
  | 4 => result_success ("as.logical"%string, LglSxp)
  | 5 => result_success ("as.raw"%string, RawSxp)
  | _ => result_impossible "invalid operand"
  end%Z
  in
  let%success (disp, ans) := DispatchOrEval globals runs call op name args rho false true in
  if disp then
    result_success ans
  else

  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, _, _ := args in
  let x := args_car in
  let%success x_type := TYPEOF x in
  ifb x_type = type then
    let%success x_attrib := ATTRIB x in
    ifb x_attrib = R_NilValue then
      result_success x
    else
      let%success ans := if%success MAYBE_REFERENCED x then duplicate globals runs x else result_success x
      in
      run%success CLEAR_ATTRIB ans in
      result_success ans
  else
    let%success ans := ascommon call args_car type in
    run%success CLEAR_ATTRIB ans in
    result_success ans.

End Parameters.

