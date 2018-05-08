(** Rcore.
  Describes how R evaluates expressions.
  The content of this file is the Coq equivalent of functions from R source code.
  Note that only relevant definitions are translated here. Some are just
  reinterpreted in Coq without following the original algorithm of the
  C source. See report for more details. **)

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
Require Export Loops.


Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

(** * Interpreter functions **)

(** We recall from RinternalsAux.v that we write [p_] for the object
  referenced by the pointer [p], and [p_f] for the field [f] of it. **)

Require Export CRmath.
Require Export CRinternals.
Arguments SET_MISSING : clear implicits.

Require Export CDefn.
Arguments SET_PRSEEN : clear implicits.

Require Export CMemory.
Require Export CRinlinedfuns.
Require Export CBuiltin.
Require Export CDuplicate.
Require Export CDstruct.

(** ** Rinlinedfuns.c **)

(** The function names of this section correspond to the function
  names in the file include/Rinlinedfuns.c.  The most important
  functions of eval.c are however only shown in a previous section.**)

Definition R_FixupRHS S x y :=
  add%stack "R_FixupRHS" in
  let%success y_named := NAMED S y using S in
  ifb y <> R_NilValue /\ y_named <> named_temporary then
    if%success R_cycle_detected globals runs S x y using S then
      duplicate globals runs S y
    else
      map%pointer y with set_named_plural using S in
      result_success S y
  else result_success S y.

Definition isVectorizable S (s : SEXP) :=
  add%stack "isVectorizable" in
  ifb s = R_NilValue then
    result_success S true
  else if%success isNewList globals S s using S then
    let%success n := XLENGTH S s using S in
    do%exit
    for i from 0 to n - 1 do
      let%success s_i := VECTOR_ELT S s i using S in
      let%success s_i_iv := isVector S s_i using S in
      let%success s_i_len := LENGTH globals S s_i using S in
      ifb ~ s_i_iv \/ s_i_len > 1 then
        result_rreturn S false
      else result_rskip S using S in
    result_success S true
  else if%success isList globals S s using S then
    fold%return
    along s
    as s_car, _ do
      let%success s_car_iv := isVector S s_car using S in
      let%success s_car_len := LENGTH globals S s_car using S in
      ifb ~ s_car_iv \/ s_car_len > 1 then
        result_rreturn S false
      else result_rskip S using S, runs, globals in
    result_success S true
  else result_success S false.

Definition isArray S s :=
  add%stack "isArray" in
  if%success isVector S s using S then
    let%success t := runs_getAttrib runs S s R_DimSymbol using S in
    let%success t_type := TYPEOF S t using S in
    let%success t_len := LENGTH globals S t using S in
    ifb t_type = IntSxp /\ t_len > 0 then
      result_success S true
    else result_success S false
  else result_success S false.

Definition isTs S s :=
  add%stack "isTs" in
  if%success isVector S s using S then
    let%success a := runs_getAttrib runs S s R_TspSymbol using S in
    result_success S (decide (a <> R_NilValue))
  else result_success S false.

Definition conformable S x y :=
  add%stack "conformable" in
  let%success x := runs_getAttrib runs S x R_DimSymbol using S in
  let%success y := runs_getAttrib runs S y R_DimSymbol using S in
  let%success x_len := R_length globals runs S x using S in
  let%success y_len := R_length globals runs S y using S in
  ifb x_len <> y_len then
    result_success S false
  else
    let n := x_len in
    do%exit
    for i from 0 to n - 1 do
      read%Integer x_i := x at i using S in
      read%Integer y_i := y at i using S in
      ifb x_i <> y_i then
        result_rreturn S false
      else result_rskip S using S in
    result_success S true.

Definition isValidString S x :=
  add%stack "isValidString" in
  let%success x_type := TYPEOF S x using S in
  let%success x_len := LENGTH globals S x using S in
  let%success x_0 := STRING_ELT S x 0 using S in
  let%success x_0_type := TYPEOF S x_0 using S in
  result_success S (decide (x_type = StrSxp /\ x_len > 0 /\ x_0_type <> NilSxp)).



Require Export CEval.
Require Export CArithmetic.
Require Export CUtil.
Require Export CPrintutils.
Require Export CEnvir.

(** ** dstruct.c **)

(** The function names of this section correspond to the function names
  in the file main/dstruct.c. **)

Definition iSDDName S (name : SEXP) :=
  add%stack "iSDDName" in
  let%success buf := CHAR S name using S in
  ifb String.substring 0 2 buf = ".."%string /\ String.length buf > 2 then
    let buf := String.substring 2 (String.length buf) buf in
    (** I am simplifying the C code here. **)
    result_success S (decide (Forall (fun c : Ascii.ascii =>
        Mem c (["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"])%char)
      (string_to_list buf)))
  else
  result_success S false.

Definition mkSYMSXP S (name value : SEXP) :=
  add%stack "mkSYMSXP" in
  let%success i := iSDDName S name using S in
  let (S, c) := alloc_SExp S (make_SExpRec_sym R_NilValue name value R_NilValue) in
  run%success SET_DDVAL S c i using S in
  result_success S c.


Require Export CNames.
Require Export CSysutils.
Require Export CGram.
Require Export CContext.
Require Export CMatch.


(** ** envir.c **)

(** The function names of this section correspond to the function names
  in the file main/envir.c. **)

Definition R_NewHashedEnv S (enclos size : SEXP) :=
  add%stack "R_NewHashedEnv" in
  let%success s := NewEnvironment globals runs S R_NilValue R_NilValue enclos using S in
  (** As we do not model hashtabs, we are here skipping the most
    important part of this function.  This is thus only a
    simplification of the original function. **)
  result_success S s.

Definition R_envHasNoSpecialSymbols S (env : SEXP) :=
  add%stack "R_envHasNoSpecialSymbols" in
  read%env env_, env_env := env using S in
  (** A note about hashtabs has been commented out. **)
  fold%let b := true
  along env_frame env_env
  as frame_car, frame_tag do
    if%success IS_SPECIAL_SYMBOL S frame_tag using S then
      result_success S false
    else result_success S b using S, runs, globals.

Definition SET_FRAME S x v :=
  add%stack "SET_FRAME" in
  read%env x_, x_env := x using S in
  let x_env := {|
      env_frame := v ;
      env_enclos := env_enclos x_env
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_env
    |} in
  write%defined x := x_ using S in
  result_skip S.

Definition SET_ENCLOS S x v :=
  add%stack "SET_ENCLOS" in
  read%env x_, x_env := x using S in
  let x_env := {|
      env_frame := env_frame x_env ;
      env_enclos := v
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_env
    |} in
  write%defined x := x_ using S in
  result_skip S.

Definition addMissingVarsToNewEnv S (env addVars : SEXP) :=
  add%stack "addMissingVarsToNewEnv" in
  ifb addVars = R_NilValue then
    result_skip S
  else
    let%success addVars_type := TYPEOF S addVars using S in
    ifb addVars_type = EnvSxp then
      result_error S "Additional variables should be passed as a list."
    else
      read%list addVars_car, addVars_cdr, _ := addVars using S in
      fold%success aprev := addVars
      along addVars_cdr
      as a, _, _ do
        result_success S a using S, runs, globals in
      read%env _, env_env := env using S in
      set%cdr aprev := env_frame env_env using S in
      run%success SET_FRAME S env addVars using S in
      fold%let
      along addVars_cdr
      as endp, _, endp_list do
        let endTag := list_tagval endp_list in
        do%success (addVars, s, sprev) := (addVars, addVars, R_NilValue : SEXP)
        whileb s <> endp do
          read%list _, s_cdr, s_tag := s using S in
            ifb s_tag = endTag then
              ifb sprev = R_NilValue then
                let addVars := s_cdr in
                run%success SET_FRAME S env addVars using S in
                result_success S (addVars, s_cdr, sprev)
              else
                set_cdr S s_cdr sprev (fun S =>
                  result_success S (addVars, s_cdr, sprev))
            else result_success S (addVars, s_cdr, s) using S, runs in
        result_skip S using S, runs, globals.

Definition FRAME_LOCK_BIT := 14.

Definition FRAME_IS_LOCKED S rho :=
  add%stack "FRAME_IS_LOCKED" in
  read%defined rho_ := rho using S in
  result_success S (nth_bit FRAME_LOCK_BIT (gp rho_) ltac:(nbits_ok)).

Definition getActiveValue S f :=
  add%stack "getActiveValue" in
  let%success expr := lcons globals S f R_NilValue using S in
  runs_eval runs S expr R_GlobalEnv.

Definition SYMBOL_BINDING_VALUE S s :=
  add%stack "SYMBOL_BINDING_VALUE" in
  read%sym _, s_sym := s using S in
  if%success IS_ACTIVE_BINDING S s using S then
    getActiveValue S (sym_value s_sym)
  else result_success S (sym_value s_sym).

Definition setActiveValue S (vfun val : SEXP) :=
  add%stack "setActiveValue" in
  let%success arg_tail := lcons globals S val R_NilValue using S in
  let%success arg := lcons globals S R_QuoteSymbol arg_tail using S in
  let%success expr_tail := lcons globals S arg R_NilValue using S in
  let%success expr := lcons globals S vfun expr_tail using S in
  run%success runs_eval runs S expr R_GlobalEnv using S in
  result_skip S.

Definition SET_BINDING_VALUE S b val :=
  add%stack "SET_BINDING_VALUE" in
  if%success BINDING_IS_LOCKED S b using S then
    result_error S "Can not change value of locked binding."
  else
    if%success IS_ACTIVE_BINDING S b using S then
      read%list b_car, _, _ := b using S in
      setActiveValue S b_car val
    else
      set%car b := val using S in
      result_skip S.

Definition R_SetVarLocValue S vl value :=
  add%stack "R_SetVarLocValue" in
  SET_BINDING_VALUE S vl value.

Definition R_GetVarLocSymbol S vl :=
  add%stack "R_GetVarLocSymbol" in
  read%list _, _, vl_tag := vl using S in
  result_success S vl_tag.

Definition BINDING_VALUE S b :=
  add%stack "BINDING_VALUE" in
  read%list b_car, _, _ := b using S in
  if%success IS_ACTIVE_BINDING S b using S then
    getActiveValue S b_car
  else result_success S b_car.

Definition IS_USER_DATABASE S rho :=
  add%stack "IS_USER_DATABASE" in
  read%defined rho_ := rho using S in
  let%success inh := inherits globals runs S rho "UserDefinedDatabase" using S in
  result_success S (obj rho_ && inh).

Definition SET_SYMBOL_BINDING_VALUE S sym val :=
  add%stack "SET_SYMBOL_BINDING_VALUE" in
  if%success BINDING_IS_LOCKED S sym using S then
    result_error S "Cannot change value of locked binding."
  else if%success IS_ACTIVE_BINDING S sym using S then
    read%sym _, sym_sym := sym using S in
    setActiveValue S (sym_value sym_sym) val
  else SET_SYMVALUE S sym val.

Definition simple_as_environment S arg :=
  add%stack "simple_as_environment" in
  let%success arg_s4 := IS_S4_OBJECT S arg using S in
  let%success arg_type := TYPEOF S arg using S in
  ifb arg_s4 /\ arg_type = S4Sxp then
    unimplemented_function "R_getS4DataSlot"
  else result_success S (R_NilValue : SEXP).

Definition R_EnvironmentIsLocked S env :=
  add%stack "R_EnvironmentIsLocked" in
  let%success env_type := TYPEOF S env using S in
  ifb env_type = NilSxp then
    result_error S "Use of NULL environment is defunct."
  else
    let%success env :=
      ifb env_type <> EnvSxp then
        simple_as_environment S env
      else result_success S env using S in
    let%success env_type := TYPEOF S env using S in
    ifb env_type <> EnvSxp then
      result_error S "Not an environment."
    else
      FRAME_IS_LOCKED S env.

Definition gsetVar S (symbol value rho : SEXP) : result unit :=
  add%stack "gsetVar" in
  if%success FRAME_IS_LOCKED S rho using S then
    read%sym symbol_, symbol_sym := symbol using S in
    ifb sym_value symbol_sym = R_UnboundValue then
      result_error S "Can not add such a binding to the base environment."
    else result_skip S in
  SET_SYMBOL_BINDING_VALUE S symbol value.

Definition defineVar S (symbol value rho : SEXP) : result unit :=
  add%stack "defineVar" in
  ifb rho = R_EmptyEnv then
    result_error S "Can not assign values in the empty environment."
  else if%success IS_USER_DATABASE S rho using S then
    result_not_implemented "R_ObjectTable"
  else ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
    gsetVar S symbol value rho
  else
    if%success IS_SPECIAL_SYMBOL S symbol using S then
      run%success SET_SPECIAL_SYMBOL S rho false using S in
      result_skip S in
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho using S in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifb list_tagval frame_list = symbol then
        run%success SET_BINDING_VALUE S frame value using S in
        run%success SET_MISSING S frame 0 ltac:(nbits_ok) using S in
        result_rreturn S tt
      else result_rskip S using S, runs, globals in
    if%success FRAME_IS_LOCKED S rho using S then
      result_error S "Can not add a binding to a locked environment."
    else
      let (S, l) := CONS globals S value (env_frame rho_env) in
      run%success SET_FRAME S rho l using S in
      set%tag l := symbol using S in
      result_skip S.

Definition setVarInFrame S (rho symbol value : SEXP) :=
  add%stack "setVarInFrame" in
  ifb rho = R_EmptyEnv then
    result_success S (R_NilValue : SEXP)
  else if%success IS_USER_DATABASE S rho using S then
    result_not_implemented "R_ObjectTable"
  else ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
    read%sym _, symbol_sym := symbol using S in
    ifb sym_value symbol_sym = R_UnboundValue then
      result_success S (R_NilValue : SEXP)
    else
      run%success SET_SYMBOL_BINDING_VALUE S symbol value using S in
      result_success S symbol
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho using S in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifb list_tagval frame_list = symbol then
        run%success SET_BINDING_VALUE S frame value using S in
        run%success SET_MISSING S frame 0 ltac:(nbits_ok) using S in
        result_rreturn S symbol
      else result_rskip S using S, runs, globals in
      result_success S (R_NilValue : SEXP).

Definition setVar S (symbol value rho : SEXP) :=
  add%stack "setVar" in
  do%return rho := rho
  whileb rho <> R_EmptyEnv do
    let%success vl :=
      setVarInFrame S rho symbol value using S in
    ifb vl <> R_NilValue then
      result_rreturn S tt
    else
      read%env rho_, rho_env := rho using S in
      result_rsuccess S (env_enclos rho_env)
  using S, runs in
  defineVar S symbol value R_GlobalEnv.

Definition findVarInFrame3 S rho symbol (doGet : bool) :=
  add%stack "findVarInFrame3" in
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type = NilSxp then
    result_error S "Use of NULL environment is defunct."
  else ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
    SYMBOL_BINDING_VALUE S symbol
  else ifb rho = R_EmptyEnv then
    result_success S (R_UnboundValue : SEXP)
  else
    if%success IS_USER_DATABASE S rho using S then
      result_not_implemented "R_ObjectTable"
    else
      (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
      read%defined rho_ := rho using S in
      let%env _, rho_env := rho_ using S in
      fold%return
      along env_frame rho_env
      as frame, _, frame_list do
        ifb list_tagval frame_list = symbol then
          let%success r := BINDING_VALUE S frame using S in
          result_rreturn S r
        else result_rskip S using S, runs, globals in
      result_success S (R_UnboundValue : SEXP).

Definition findVarInFrame S rho symbol :=
  add%stack "findVarInFrame" in
  findVarInFrame3 S rho symbol true.

Definition R_IsNamespaceEnv S (rho : SEXP) :=
  add%stack "R_IsNamespaceEnv" in
  ifb rho = R_BaseNamespace then
    result_success S true
  else
    let%success rho_type := TYPEOF S rho using S in
    ifb rho_type = EnvSxp then
      let%success info := findVarInFrame3 S rho R_NamespaceSymbol true using S in
      let%success info_type := TYPEOF S info using S in
      ifb info <> R_UnboundValue /\ info_type = EnvSxp then
        let%success spec_install := install globals runs S "spec" using S in
        let%success spec := findVarInFrame3 S info spec_install true using S in
        let%success spec_type := TYPEOF S spec using S in
        ifb spec <> R_UnboundValue /\ spec_type = StrSxp then
          let%success spec_len := LENGTH globals S spec using S in
          result_success S (decide (spec_len > 0))
        else result_success S false
      else result_success S false
    else result_success S false.

Definition EnsureLocal S symbol rho :=
  add%stack "EnsureLocal" in
  let%success vl := findVarInFrame3 S rho symbol true using S in
  ifb vl <> R_UnboundValue then
    let%success vl := runs_eval runs S symbol rho using S in
    let%success vl :=
      if%success MAYBE_SHARED S vl using S then
        let%success vl := shallow_duplicate globals runs S vl using S in
        run%success defineVar S symbol vl rho using S in
        run%success INCREMENT_NAMED S vl using S in
        result_success S vl
      else result_success S vl using S in
    result_success S vl
  else
    read%env _, rho_env := rho using S in
    let%success vl := runs_eval runs S symbol (env_enclos rho_env) using S in
    ifb vl = R_UnboundValue then
      result_error S "Object not found."
    else
      let%success vl := shallow_duplicate globals runs S vl using S in
      run%success defineVar S symbol vl rho using S in
      run%success INCREMENT_NAMED S vl using S in
      result_success S vl.

Definition findVar S symbol rho :=
  add%stack "findVar" in
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type = NilSxp then
    result_error S "Use of NULL environment is defunct."
  else ifb rho_type <> EnvSxp then
    result_error S "Argument ‘rho’ is not an environment."
  else
    do%return rho := rho
    whileb rho <> R_EmptyEnv do
      let%success vl := findVarInFrame3 S rho symbol true using S in
      ifb vl <> R_UnboundValue then
        result_rreturn S vl
      else
        read%env _, rho_env := rho using S in
        result_rsuccess S (env_enclos rho_env) using S, runs in
    result_success S (R_UnboundValue : SEXP).

Definition findVarLocInFrame S (rho symbol : SEXP) :=
  add%stack "findVarLocInFrame" in
  ifb rho = R_BaseEnv \/ rho = R_BaseNamespace then
    result_error S "It can’t be used in the base environment."
  else ifb rho = R_EmptyEnv then
    result_success S (R_NilValue : SEXP)
  else if%success IS_USER_DATABASE S rho using S then
    unimplemented_function "R_ExternalPtrAddr"
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho using S in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifb list_tagval frame_list = symbol then
        result_rreturn S frame
      else result_rskip S using S, runs, globals in
    result_success S (R_NilValue : SEXP).

Definition R_findVarLocInFrame S rho symbol :=
  add%stack "R_findVarLocInFrame" in
  let%success binding := findVarLocInFrame S rho symbol using S in
  ifb binding = R_NilValue then
    result_success S NULL
  else result_success S binding.

Definition RemoveFromList S (thing list : SEXP) :=
  add%stack "RemoveFromList" in
  ifb list = R_NilValue then
    result_success S None
  else
    read%list _, list_cdr, list_tag := list using S in
    ifb list_tag = thing then
      set%car list := R_UnboundValue using S in
      run%success LOCK_BINDING S list using S in
      let rest := list_cdr in
      set%cdr list := R_NilValue using S in
      result_success S (Some rest)
    else
      let next := list_cdr in
      fold%return last := list
      along next
      as next, _, next_list do
        ifb list_tagval next_list = thing then
          set%car next := R_UnboundValue using S in
          run%success LOCK_BINDING S next using S in
          set%cdr last := list_cdrval next_list using S in
          set%cdr next := R_NilValue using S in
          result_rreturn S (Some list)
        else result_rsuccess S next using S, runs, globals in
      result_success S None.


Definition unbindVar S (symbol rho : SEXP) :=
  add%stack "unbindVar" in
  ifb rho = R_BaseNamespace then
    result_error S "Can’t unbind in the base namespace."
  else ifb rho = R_BaseEnv then
    result_error S "Unbinding in the base environment is unimplemented."
  else if%success FRAME_IS_LOCKED S rho using S then
    result_error S "Can’t remove bindings from a locked environment."
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho using S in
    if%defined list := RemoveFromList S symbol (env_frame rho_env) using S then
      SET_FRAME S rho list
    else result_skip S.

Definition ddVal S symbol :=
  add%stack "ddVal" in
  let%success symbol_name := PRINTNAME S symbol using S in
  let%success buf := CHAR S symbol_name using S in
  ifb String.substring 0 2 buf = ".."%string /\ String.length buf > 2 then
    let buf := String.substring 2 (String.length buf - 2) in
    unimplemented_function "strtol"
  else result_success S 0.

Definition ddfindVar (S : state) (symbol rho : SEXP) : result SEXP :=
  unimplemented_function "ddfindVar".


Definition findFun3 S symbol rho (call : SEXP) : result SEXP :=
  add%stack "findFun3" in
  let%success rho :=
    if%success IS_SPECIAL_SYMBOL S symbol using S then
      do%success rho := rho
      while let%success special := NO_SPECIAL_SYMBOLS S rho using S in
            result_success S (decide (rho <> R_EmptyEnv /\ special)) do
        read%env _, rho_env := rho using S in
        result_success S (env_enclos rho_env)
      using S, runs in
      result_success S rho
    else result_success S rho using S in
  do%return rho := rho
  whileb rho <> R_EmptyEnv do
    let%success vl := findVarInFrame3 S rho symbol true using S in
    run%return
      ifb vl <> R_UnboundValue then
        let%success vl_type := TYPEOF S vl using S in
        let%success vl :=
          ifb vl_type = PromSxp then
            runs_eval runs S vl rho
          else result_success S vl using S in
        let%success vl_type := TYPEOF S vl using S in
        ifb vl_type = CloSxp \/ vl_type = BuiltinSxp \/ vl_type = SpecialSxp then
          result_rreturn S vl
        else ifb vl = R_MissingArg then
          let%success str_symbol := PRINTNAME S symbol using S in
          let%success str_symbol_ := CHAR S str_symbol using S in
          result_error S ("Argument “" ++ str_symbol_ ++ "” is missing, with no default.")
        else result_rskip S
      else result_rskip S using S in
    read%env _, rho_env := rho using S in
    result_rsuccess S (env_enclos rho_env)
  using S, runs in
  let%success str_symbol := PRINTNAME S symbol using S in
  let%success str_symbol_ := CHAR S str_symbol using S in
  result_error S ("Could not find function “" ++ str_symbol_ ++ "”.").

Definition findRootPromise S p :=
  add%stack "findRootPromise" in
  let%success p_type := TYPEOF S p using S in
  ifb p_type = PromSxp then
    do%success p := p
    while
      let%success p := PREXPR globals S p using S in
      let%success p_type := TYPEOF S p using S in
      result_success S (decide (p_type = PromSxp))
    do
      PREXPR globals S p using S, runs in
    result_success S p
  else result_success S p.

Definition R_isMissing S (symbol rho : SEXP) :=
  add%stack "R_isMissing" in
  ifb symbol = R_MissingArg then
    result_success S true
  else
    let%success (s, ddv) :=
      if%success DDVAL S symbol using S then
        let%success d := ddVal S symbol using S in
        result_success S (R_DotsSymbol : SEXP, d)
      else result_success S (symbol, 0) using S in
    ifb rho = R_BaseEnv \/ rho = R_BaseNamespace then
      result_success S false
    else
      let%success vl := findVarLocInFrame S rho s using S in
      ifb vl <> R_NilValue then
        let%exit vl :=
          if%success DDVAL S symbol using S then
            read%list vl_car, _, _ := vl using S in
            let%success vl_car_len := R_length globals runs S vl_car using S in
            ifb vl_car_len < ddv \/ vl_car = R_MissingArg then
              result_rreturn S true
            else
              let%success n := nthcdr globals runs S vl_car (ddv - 1) using S in
              result_rsuccess S n
          else result_rsuccess S vl using S in
        let%success vl_mis := MISSING S vl using S in
        read%list vl_car, _, _ := vl using S in
        ifb vl_mis = true \/ vl_car = R_MissingArg then
          result_success S true
        else if%success IS_ACTIVE_BINDING S vl using S then
          result_success S false
        else
          let%success vl_car_rp := findRootPromise S vl_car using S in
          set%car vl := vl_car_rp using S in
          let vl_cat := vl_car_rp in
          let%success vl_car_type := TYPEOF S vl_car using S in
          ifb vl_car_type = PromSxp then
            read%prom _, vl_car_prom := vl_car using S in
            let%success vl_car_expr := PREXPR globals S vl_car using S in
            let%success vl_car_expr_type := TYPEOF S vl_car_expr using S in
            ifb prom_value vl_car_prom = R_UnboundValue /\ vl_car_expr_type = SymSxp then
              let%success vl_car_prseen := PRSEEN S vl_car using S in
              ifb vl_car_prseen = 1 then
                result_success S true
              else
                let%success oldseen := PRSEEN_direct S vl_car using S in
                run%success SET_PRSEEN S vl_car 1 ltac:(nbits_ok) using S in
                let%success val :=
                  let%success vl_car_prexpr := PREXPR globals S vl_car using S in
                  let%success vl_car_prenv := PRENV S vl_car using S in
                  runs_R_isMissing runs S vl_car_prexpr vl_car_prenv using S in
                run%success SET_PRSEEN_direct S vl_car oldseen using S in
                result_success S val
            else result_success S false
          else result_success S false
      else result_success S false.


Require Export CAltrep.

(** ** util.c **)

(** The function names of this section correspond to the function names
  in the file main/util.c. **)

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


Require Export CCoerce.
Require Export CAttrib.
Require Export CObjects.


(** ** eval.c **)

(** The function names of this section correspond to the function names
  in the file main/eval.c. **)

Definition COPY_TAG S vto vfrom :=
  add%stack "COPY_TAG" in
  read%list _, _, vfrom_tag := vfrom using S in
  ifb vfrom_tag <> R_NilValue then
    set%tag vto := vfrom_tag using S in
    result_skip S
  else result_skip S.

Definition mkRHSPROMISE S expr rhs :=
  add%stack "mkRHSPROMISE" in
  R_mkEVPROMISE_NR globals S expr rhs.

Definition asLogicalNoNA S (s call : SEXP) :=
  add%stack "asLogicalNoNA" in
  let%exit cond :=
    if%success IS_SCALAR S s LglSxp using S then
      let%success cond := SCALAR_LVAL S s using S in
      ifb cond <> NA_LOGICAL then
        result_rreturn S cond
      else result_rsuccess S cond
    else
      if%success IS_SCALAR S s IntSxp using S then
        let%success val := SCALAR_IVAL S s using S in
        ifb val <> NA_INTEGER then
          ifb val <> 0 then
            result_rreturn S (1 : int)
          else result_rreturn S (0 : int)
        else result_rsuccess S NA_LOGICAL
      else result_rsuccess S NA_LOGICAL using S in
  let%success len := R_length globals runs S s using S in
  ifb len > 1 then
    result_error S "The condition has length > 1."
  else
    let%success cond :=
      ifb len > 0 then
        let%success s_type := TYPEOF S s using S in
        match s_type with
        | LglSxp =>
          read%Logical cond := s at 0 using S in
          result_success S cond
        | IntSxp =>
          read%Integer cond := s at 0 using S in
          result_success S cond
        | _ =>
          asLogical globals S s
        end
      else result_success S cond using S in
    ifb cond = NA_LOGICAL then
      ifb len = 0 then
        result_error S "Argument is of length zero."
      else
        if%success isLogical S s using S then
          result_error S "Missing value where TRUE/FALSE needed."
        else result_error S "Argument is not interpretable as logical."
    else result_success S cond.

Definition replaceCall S vfun val args rhs :=
  add%stack "replaceCall" in
  let%success args_len := R_length globals runs S args using S in
  let (S, tmp) := allocList globals S (3 + args_len) in
  let ptmp := tmp in
  set%car ptmp := vfun using S in
  read%list _, ptmp_cdr, _ := ptmp using S in
  let ptmp := ptmp_cdr in
  set%car ptmp := val using S in
  read%list _, ptmp_cdr, _ := ptmp using S in
  let ptmp := ptmp_cdr in
  fold%success ptmp := ptmp
  along args
  as args_car, args_tag do
    set%car ptmp := args_car using S in
    set%tag ptmp := args_tag using S in
    read%list _, ptmp_cdr, _ := ptmp using S in
    result_success S ptmp_cdr using S, runs, globals in
  set%car ptmp := rhs using S in
  set%tag ptmp := R_valueSym using S in
  map%pointer tmp with set_type LangSxp using S in
  result_success S tmp.

Definition assignCall S op symbol vfun val args rhs :=
  add%stack "assignCall" in
  let%success val := replaceCall S vfun val args rhs using S in
  lang3 globals S op symbol val.

Definition forcePromise S (e : SEXP) : result SEXP :=
  add%stack "forcePromise" in
  read%prom _, e_prom := e using S in
  ifb prom_value e_prom = R_UnboundValue then
    run%success
      let%success e_prseen := PRSEEN S e using S in
      ifb e_prseen <> 0 then
        ifb e_prseen = 1 then
          result_error S "Promise already under evaluation."
        else
          (** The C code emitted a warning here: restarting interrupted promise evaluation.
            This may be a sign that this part should be ignored. *)
          SET_PRSEEN S e 1 ltac:(nbits_ok)
      else result_skip S using S in
    run%success SET_PRSEEN S e 1 ltac:(nbits_ok) using S in
    let%success val := runs_eval runs S (prom_expr e_prom) (prom_env e_prom) using S in
    run%success SET_PRSEEN S e 0 ltac:(nbits_ok) using S in
    map%pointer val with set_named_plural using S in
    read%prom e_, e_prom := e using S in
    let e_prom := {|
        prom_value := val ;
        prom_expr := prom_expr e_prom ;
        prom_env := R_NilValue
      |} in
    let e_ := {|
        NonVector_SExpRec_header := e_ ;
        NonVector_SExpRec_data := e_prom
      |} in
    write%defined e := e_ using S in
    result_success S val
  else result_success S (prom_value e_prom).

Definition R_execClosure S (call newrho sysparent rho arglist op : SEXP)
    : result SEXP :=
  add%stack "R_execClosure" in
  let%success cntxt :=
    begincontext globals S Ctxt_Return call newrho sysparent arglist op using S in
  read%clo op_, op_clo := op using S in
  let body := clo_body op_clo in
  (** JIT functions have been ignored here. **)
  let%success R_srcef := getAttrib globals runs S op R_SrcrefSymbol using S in
  set%longjump context_cjmpbuf cntxt as jmp using S, runs in
  let%success cntxt_returnValue :=
    ifb jmp <> empty_context_type then
      ifb context_jumptarget cntxt = None then
        ifb R_ReturnedValue S = R_RestartToken then
          let cntxt := context_with_callflag cntxt Ctxt_Return in
          let S := state_with_context S cntxt in
          let S := update_R_ReturnedValue S R_NilValue in
          runs_eval runs S body newrho
        else result_success S (R_ReturnedValue S)
      else result_success S NULL
    else runs_eval runs S body newrho using S in
  let cntxt := context_with_returnValue cntxt cntxt_returnValue in
  let S := state_with_context S cntxt in
  run%success endcontext globals runs S cntxt using S in
  result_success S (context_returnValue cntxt).

Definition applyClosure S (call op arglist rho suppliedvars : SEXP)
    : result SEXP :=
  add%stack "applyClosure" in
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type <> EnvSxp then
    result_error S "‘rho’ must be an environment."
  else
    read%clo op_, op_clo := op using S in
    let formals := clo_formals op_clo in
    let savedrho := clo_env op_clo in
    let%success actuals := matchArgs globals runs S formals arglist call using S in
    let%success newrho := NewEnvironment globals runs S formals actuals savedrho using S in
    fold%success a := actuals
    along formals
    as f_car, f_tag do
      read%list a_car, a_cdr, _ := a using S in
      ifb a_car = R_MissingArg /\ f_car <> R_MissingArg then
        let%success newprom := mkPromise globals S f_car newrho using S in
        set%car a := newprom using S in
        run%success SET_MISSING S a 2 ltac:(nbits_ok) using S in
        result_success S a_cdr
      else result_success S a_cdr using S, runs, globals in
    run%success
      ifb suppliedvars <> R_NilValue then
         addMissingVarsToNewEnv S newrho suppliedvars
       else result_skip S using S in
    if%success R_envHasNoSpecialSymbols S newrho using S then
      run%success SET_SPECIAL_SYMBOL S newrho false using S in
      result_skip S in
    R_execClosure S call newrho
      (ifb context_callflag (R_GlobalContext S) = Ctxt_Generic then
         context_sysparent (R_GlobalContext S)
       else rho)
      rho arglist op.

Definition promiseArgs S (el rho : SEXP) : result SEXP :=
  add%stack "promiseArgs" in
  let (S, tail) := CONS globals S R_NilValue R_NilValue in
  fold%success (ans, tail) := (tail, tail)
  along el
  as el_car, el_tag do
    ifb el_car = R_DotsSymbol then
      let%success h := findVar S el_car rho using S in
      let%success h_type := TYPEOF S h using S in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%success tail := tail
        along h
        as h_car, h_tag do
          let%success h_car_type := TYPEOF S h_car using S in
          run%success
            ifb h_car_type = PromSxp \/ h_car = R_MissingArg then
              let (S, l) := CONS globals S h_car R_NilValue in
              set%cdr tail := l using S in
              result_skip S
            else
              let%success prom :=
                mkPromise globals S h_car rho using S in
              let (S, l) := CONS globals S prom R_NilValue in
              set%cdr tail := l using S in
              result_skip S using S in
          read%list _, tail_cdr, _ := tail using S in
          let tail := tail_cdr in
          run%success
            ifb h_tag <> R_NilValue then
              set%tag tail := h_tag using S in
              result_skip S
            else result_skip S using S in
          result_success S tail
        using S, runs, globals in
        result_success S (ans, tail)
      else ifb h <> R_MissingArg then
        result_error S "‘...’ used in an incorrect context."
      else result_success S (ans, tail)
    else ifb el_car = R_MissingArg then
      let (S, l) := CONS globals S R_MissingArg R_NilValue in
      set%cdr tail := l using S in
      read%list _, tail_cdr, _ := tail using S in
      let tail := tail_cdr in
      set%tag tail := el_tag using S in
      result_success S (ans, tail)
    else
      let%success prom :=
        mkPromise globals S el_car rho using S in
      let (S, l) := CONS globals S prom R_NilValue in
      set%cdr tail := l using S in
      read%list _, tail_cdr, _ := tail using S in
      let tail := tail_cdr in
      set%tag tail := el_tag using S in
      result_success S (ans, tail)
  using S, runs, globals in
  read%list _, ans_cdr, _ := ans using S in
  result_success S ans_cdr.

Definition PRIMFUN S x :=
  add%stack "PRIMFUN" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab runs S (prim_offset x_prim) using S in
  result_success S (fun_cfun x_fun).

Definition PRIMVAL S x :=
  add%stack "PRIMVAL" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab runs S (prim_offset x_prim) using S in
  result_success S (fun_code x_fun).

Definition PPINFO S x :=
  add%stack "PPINFO" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab runs S (prim_offset x_prim) using S in
  result_success S (fun_gram x_fun).

Definition PRIMARITY S x :=
  add%stack "PRIMARITY" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab runs S (prim_offset x_prim) using S in
  result_success S (fun_arity x_fun).

Definition PRIMINTERNAL S x :=
  add%stack "PRIMINTERNAL" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab runs S (prim_offset x_prim) using S in
  result_success S (funtab_eval_arg_internal (fun_eval x_fun)).

Definition evalList S (el rho call : SEXP) n :=
  add%stack "evalList" in
  fold%success (n, head, tail) := (n, R_NilValue : SEXP, R_NilValue : SEXP)
  along el
  as el_car, el_tag
    do
    let n := 1 + n in
    ifb el_car = R_DotsSymbol then
      let%success h := findVar S el_car rho using S in
      let%success h_type := TYPEOF S h using S in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%success tail := tail
        along h
        as h_car, h_tag
        do
          let%success tmp_ev := runs_eval runs S h_car rho using S in
          let (S, ev) := CONS_NR globals S tmp_ev R_NilValue in
          let%success head :=
            ifb head = R_NilValue then
              result_success S ev
            else
              set%cdr tail := ev using S in
              result_success S head using S in
          run%success
            ifb h_tag <> R_NilValue then
              set%tag ev := h_tag using S in
              result_skip S
            else result_skip S using S in
          result_success S ev
        using S, runs, globals in
        result_success S (n, head, tail)
      else ifb h <> R_MissingArg then
        result_error S "‘...’ used in an incorrect context."
      else result_success S (n, head, tail)
    else ifb el_car = R_MissingArg then
      result_error S "Argument is empty."
    else
      let%success ev := runs_eval runs S el_car rho using S in
      let (S, ev) := CONS_NR globals S ev R_NilValue in
      let%success head :=
        ifb head = R_NilValue then
          result_success S ev
        else
          set%cdr tail := ev using S in
          result_success S head using S in
      run%success
        ifb el_tag <> R_NilValue then
          set%tag ev := el_tag using S in
          result_skip S
        else result_skip S using S in
      result_success S (n, head, ev)
  using S, runs, globals in
  result_success S head.

Definition evalListKeepMissing (S : state) (el rho : SEXP) : result SEXP :=
  add%stack "evalListKeepMissing" in
  fold%success (head, tail) := (R_NilValue : SEXP, R_NilValue : SEXP)
  along el
  as _, _, el_list do
    let el_car := list_carval el_list in
    let el_cdr := list_cdrval el_list in
    ifb el_car = R_DotsSymbol then
      let%success h := findVar S el_car rho using S in
      let%success h_type := TYPEOF S h using S in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%let (head, tail) := (head, tail)
        along h
        as _, _, h_list do
          let h_car := list_carval h_list in
          let%success val :=
            ifb h_car = R_MissingArg then
              result_success S (R_MissingArg : SEXP)
            else runs_eval runs S h_car rho using S in
          run%success INCREMENT_LINKS S val using S in
          let (S, ev) := CONS_NR globals S val R_NilValue in
          let%success head :=
            ifb head = R_NilValue then
              result_success S ev
            else
              set%cdr tail := ev using S in
              result_success S head using S in
          run%success COPY_TAG S ev h using S in
          result_success S (head, ev) using S, runs, globals
      else ifb h <> R_MissingArg then
        result_error S "‘...’ used in an incorrect context."
      else result_success S (head, tail)
    else
      let%success val :=
        let%success el_car_sy := isSymbol S el_car using S in
        let%success el_car_mi := R_isMissing S el_car rho using S in
        ifb el_car = R_MissingArg \/ (el_car_sy /\ el_car_mi) then
          result_success S (R_MissingArg : SEXP)
        else runs_eval runs S el_car rho using S in
      run%success
        ifb el_cdr <> R_NilValue then
          INCREMENT_LINKS S val
        else result_skip S using S in
      let (S, ev) := CONS_NR globals S val R_NilValue in
      let%success head :=
        ifb head = R_NilValue then
          result_success S ev
        else
          set%cdr tail := ev using S in
          result_success S head using S in
      run%success COPY_TAG S ev el using S in
      result_success S (head, ev) using S, runs, globals in
  fold%success
  along head
  as _, _, head_list do
    let el_cdr := list_cdrval head_list in
    let el_car := list_carval head_list in
    ifb el_cdr <> R_NilValue then
      DECREMENT_LINKS S el_car
    else result_skip S using S, runs, globals in
  result_success S head.

Definition evalArgs S el rho (dropmissing : bool) call n :=
  add%stack "evalArgs" in
  if dropmissing then
    evalList S el rho call n
  else evalListKeepMissing S el rho.

(** The original function [DispatchGroup] returns a boolean and, if this boolean is true,
  overwrites its additional argument [ans]. This naturally translates as an option type. **)
Definition DispatchGroup S group (call op args rho : SEXP)
    : result (option SEXP) :=
  add%stack "DispatchGroup" in
  read%list args_car, args_cdr, _ := args using S in
  let%success args_car_is := isObject S args_car using S in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let%success args_cdr_car_is := isObject S args_cdr_car using S in
  ifb args_car <> R_NilValue /\ ~ args_car_is /\ (args_cdr = R_NilValue \/ ~ args_cdr_car_is) then
    result_success S None
  else
    let isOps := decide (group = "Ops"%string) in
    let%success args_len := R_length globals runs S args using S in
    let%success args_car_S4 := IS_S4_OBJECT S args_car using S in
    let%success args_cdr_car_S4 := IS_S4_OBJECT S args_cdr_car using S in
    let useS4 :=
      ifb args_len = 1 /\ ~ args_car_S4 then false
      else ifb args_len = 2 /\ ~ args_car_S4 /\ ~ args_cdr_car_S4 then false
      else true in
    run%exit
      if useS4 then
        run%success
          if isOps then
            fold%let
            along args
            as s, _, _ do
              set%tag s := R_NilValue using S in
              result_skip S using S, runs, globals
          else result_skip S using S in
        let%success op_hm := R_has_methods S op using S in
        let%success value := R_possible_dispatch S call op args rho false using S in
        ifb op_hm /\ value <> NULL then
          result_rreturn S (Some value)
        else result_rskip S
      else result_rskip S using S in
    read%list call_car, _, _ := call using S in
    run%exit
      if%success isSymbol S call_car using S then
        let%success call_car_name := PRINTNAME S call_car using S in
        let%success call_car_str := CHAR S call_car_name using S in
        let cstr := String.index 0 "." call_car_str in
        match cstr with
        | None => result_rskip S
        | Some cstr =>
          let cstr_ := String.substring (1 + cstr) (String.length call_car_str - cstr - 1) call_car_str in
          ifb cstr_ = "default"%string then
            result_rreturn S None
          else result_rskip S
        end
      else result_rskip S using S in
    let%success nargs :=
      if isOps then
        R_length globals runs S args
      else result_success S 1 using S in
    read%list args_car, args_cdr, _ := args using S in
    run%exit
      let%success args_car_obj := isObject S args_car using S in
      ifb nargs = 1 /\ ~ args_car_obj then
        result_rreturn S None
      else result_rskip S using S in
    let%success generic := PRINTNAME S op using S in
    unimplemented_function "classForGroupDispatch".

Definition DispatchOrEval S (call op : SEXP) (generic : string) (args rho : SEXP)
    (dropmissing argsevald : bool) : result (bool * SEXP) :=
  add%stack "DispatchOrEval" in
  let%success (x, dots) :=
    if argsevald then
      read%list args_car, _, _ := args using S in
      result_success S (args_car, false)
    else
      fold%return (x, dots) := (R_NilValue : SEXP, false)
      along args as args_car, _ do
        ifb args_car = R_DotsSymbol then
          let%success h := findVar S R_DotsSymbol rho using S in
          let%success h_type := TYPEOF S h using S in
          ifb h_type = DotSxp then
            read%list h_car, _, _ := h using S in
            let%success h_car_type := TYPEOF S h_car using S in
            ifb h_car_type <> PromSxp then
              result_error S "Value in ‘...’ is not a promise."
            else
              let%success r := runs_eval runs S h_car rho using S in
              result_rreturn S (r, true)
          else ifb h <> R_NilValue /\ h <> R_MissingArg then
            result_error S "‘...’ used in an incorrect context."
          else result_rsuccess S (x, dots)
        else
          let%success r := runs_eval runs S args_car rho using S in
          result_rreturn S (r, false) using S, runs, globals in
      result_success S (x, dots) using S in
  run%exit
    if%success isObject S x using S then
      result_not_implemented "Object case."
    else result_rskip S using S in
  let%success ans :=
    if negb argsevald then
      if dots then
        evalArgs S args rho dropmissing call 0
      else
        read%list _, args_cdr, args_tag := args using S in
        let%success r := evalArgs S args_cdr rho dropmissing call 1 using S in
        let (S, ans) := CONS_NR globals S x r in
        let%success t := CreateTag globals runs S args_tag using S in
        set%tag ans := t using S in
        result_success S ans
    else result_success S args using S in
  result_success S (false, ans).

Definition DispatchAnyOrEval S (call op : SEXP) (generic : string) (args rho : SEXP)
    (dropmissing argsevald : bool) : result (bool * SEXP) :=
  add%stack "DispatchAnyOrEval" in
  if%success R_has_methods S op using S then
    result_not_implemented "Method case."
  else DispatchOrEval S call op generic args rho dropmissing argsevald.

Definition eval S (e rho : SEXP) :=
  add%stack "eval" in
  let%success e_type := TYPEOF S e using S in
  match e_type with
  | NilSxp
  | ListSxp
  | LglSxp
  | IntSxp
  | RealSxp
  | StrSxp
  | CplxSxp
  | RawSxp
  | S4Sxp
  | SpecialSxp
  | BuiltinSxp
  | EnvSxp
  | CloSxp
  | VecSxp
  | ExtptrSxp
  | WeakrefSxp
  | ExprSxp =>
    map%pointer e with set_named_plural using S in
    result_success S e
  | _ =>
    let%success rho_type := TYPEOF S rho using S in
    ifb rho_type <> EnvSxp then
      result_error S "‘rho’ must be an environment."
    else
      match e_type with
      | BcodeSxp =>
        unimplemented_function "bcEval"
      | SymSxp =>
        ifb e = R_DotsSymbol then
          result_error S "‘...’ used in an incorrect context."
        else
          let%success tmp :=
            if%success DDVAL S e using S then
              ddfindVar S e rho
            else
              findVar S e rho using S in
          ifb tmp = R_UnboundValue then
            let%success e_name := PRINTNAME S e using S in
            (** Originally, it was [EncodeChar] instead of [CHAR]. **)
            let%success e_str := CHAR S e_name using S in
            result_error S ("Object not found “" ++ e_str ++ "”.")
          else
            let%success ddval := DDVAL S e using S in
            ifb tmp = R_MissingArg /\ ~ ddval then
              result_error S "Argument is missing, with no default."
            else
              let%success tmp_type := TYPEOF S tmp using S in
              ifb tmp_type = PromSxp then
                read%prom _, tmp_prom := tmp using S in
                let%success tmp :=
                  ifb prom_value tmp_prom = R_UnboundValue then
                    forcePromise S tmp
                  else result_success S (prom_value tmp_prom) using S in
                map%pointer tmp with set_named_plural using S in
                result_success S tmp
              else
                let%success tmp_type := TYPEOF S tmp using S in
                let%success tmp_named := NAMED S tmp using S in
                run%success
                  ifb tmp_type <> NilSxp /\ tmp_named = named_temporary then
                    map%pointer tmp with set_named_unique using S in
                    result_skip S
                  else result_skip S using S in
                result_success S tmp
      | PromSxp =>
        run%success
          read%prom _, e_prom := e using S in
          ifb prom_value e_prom = R_UnboundValue then
            run%success forcePromise S e using S in
            result_skip S
          else result_skip S using S in
        read%prom _, e_prom := e using S in
        result_success S (prom_value e_prom)
      | LangSxp =>
        read%list e_car, e_cdr, _ := e using S in
        let%success e_car_type := TYPEOF S e_car using S in
        let%success op :=
          ifb e_car_type = SymSxp then
            let%success ecall :=
              ifb context_callflag (R_GlobalContext S) = Ctxt_CCode then
                result_success S (context_call (R_GlobalContext S))
              else result_success S e using S in
            findFun3 S e_car rho ecall
          else runs_eval runs S e_car rho using S in
        let%success op_type := TYPEOF S op using S in
        match op_type with
        | SpecialSxp =>
          let%success f := PRIMFUN S op using S in
          f S e op e_cdr rho
        | BuiltinSxp =>
          let%success tmp := evalList S e_cdr rho e 0 using S in
          let%success infos := PPINFO S op using S in
          ifb PPinfo_kind infos = PP_FOREIGN then
            let%success cntxt :=
              begincontext globals S Ctxt_Builtin e R_BaseEnv R_BaseEnv R_NilValue R_NilValue using S in
            let%success f := PRIMFUN S op using S in
            let%success tmp := f S e op tmp rho using S in
            run%success endcontext globals runs S cntxt using S in
            result_success S tmp
          else
            let%success f := PRIMFUN S op using S in
            f S e op tmp rho
        | CloSxp =>
          let%success tmp := promiseArgs S e_cdr rho using S in
          applyClosure S e op tmp rho R_NilValue
        | _ => result_error S "Attempt to apply non-function."
        end
      | DotSxp => result_error S "‘...’ used in an incorrect context"
      | _ => result_error S "Type unimplemented in the R source code."
      end
  end.

Definition evalseq S expr rho (forcelocal : bool) tmploc :=
  add%stack "evalseq" in
  if%success isNull S expr using S then
    result_error S "Invalid left side assignment."
  else if%success isSymbol S expr using S then
    let%success nval :=
      if forcelocal then
        EnsureLocal S expr rho
      else
        read%env _, rho_env := rho using S in
        eval S expr (env_enclos rho_env) using S in
    let%success nval :=
      if%success MAYBE_SHARED S nval using S then
        shallow_duplicate globals runs S nval
      else result_success S nval using S in
    let (S, r) := CONS_NR globals S nval expr in
    result_success S r
  else if%success isLanguage globals S expr using S then
    read%list expr_car, expr_cdr, _ := expr using S in
    read%list expr_cdr_car, expr_cdr_cdr, _ := expr_cdr using S in
    let%success val := runs_evalseq runs S expr_cdr_car rho forcelocal tmploc using S in
    read%list val_car, _, _ := val using S in
    run%success R_SetVarLocValue S tmploc val_car using S in
    let%success tmploc_sym := R_GetVarLocSymbol S tmploc using S in
    let%success nexpr := LCONS globals S tmploc_sym expr_cdr_cdr using S in
    let%success nexpr := LCONS globals S expr_car nexpr using S in
    let%success nval := eval S nexpr rho using S in
    let%success nval :=
      if%success MAYBE_REFERENCED S nval using S then
        if%success MAYBE_SHARED S nval using S then
          shallow_duplicate globals runs S nval
        else
          read%list nval_car, _, _ := nval using S in
          if%success MAYBE_SHARED S nval_car using S then
            shallow_duplicate globals runs S nval
          else result_success S nval
      else result_success S nval using S in
    let (S, r) := CONS_NR globals S nval val in
    result_success S r
  else result_error S "Target of assignment expands to non-language object.".

(** Evaluates the expression in the global environment. **)
Definition eval_global S e :=
  add%stack "eval_global" in
  eval S e R_GlobalEnv.

End Parameterised.

Arguments SET_MISSING : clear implicits.
Arguments SET_PRSEEN : clear implicits.
