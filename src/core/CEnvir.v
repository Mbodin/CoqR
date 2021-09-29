(** Core.CEnvir.
  The function names in this file correspond to the function
  names in the file main/envir.c. The most important functions of
  envir.c are however only shown in a later section. **)
  (* TODO: Need reorganisation. *)

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
From Lib Require Import Double.
From CoqR Require Import Loops.
From CoqR.core Require Import Conflicts CRinlinedfuns CMemory CDefn.
From CoqR.core Require Import CRinternals CNames CDuplicate.

Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

Definition R_NewHashedEnv (enclos size : _SEXP) : result_SEXP :=
  add%stack "R_NewHashedEnv" in
  let%success s := NewEnvironment runs R_NilValue R_NilValue enclos in
  (** As we do not model hashtabs, we are here skipping the most
    important part of this function.  This is thus only a
    simplification of the original function. **)
  result_success s.

Definition R_envHasNoSpecialSymbols (env : _SEXP) : result_bool :=
  add%stack "R_envHasNoSpecialSymbols" in
  read%env env_, env_env := env in
  (** A note about hashtabs has been commented out. **)
  fold%let b := contextual_ret true
  along env_frame env_env
  as frame_car, frame_tag do
    if%success IS_SPECIAL_SYMBOL frame_tag then
      result_success false
    else result_success b using runs.

Definition SET_FRAME (x v : _SEXP) :=
  add%stack "SET_FRAME" in
  let%fetch v in
  read%env x_, x_env := x in
  let x_env := {|
      env_frame := v ;
      env_enclos := env_enclos x_env
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_env
    |} in
  write%defined x := x_ in
  result_skip.

Definition SET_ENCLOS (x v : _SEXP) :=
  add%stack "SET_ENCLOS" in
  let%fetch v in
  read%env x_, x_env := x in
  let x_env := {|
      env_frame := env_frame x_env ;
      env_enclos := v
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_env
    |} in
  write%defined x := x_ in
  result_skip.

Definition addMissingVarsToNewEnv (env addVars : _SEXP) :=
  add%stack "addMissingVarsToNewEnv" in
  ifc addVars '== R_NilValue then
    result_skip
  else
    let%success addVars_type := TYPEOF addVars in
    ifb addVars_type = EnvSxp then
      result_error "Additional variables should be passed as a list."
    else
      read%list addVars_car, addVars_cdr, _ := addVars in
      fold%success aprev := addVars
      along addVars_cdr
      as a, _, _ do
        result_success a using runs in
      read%env _, env_env := env in
      set%cdr aprev := env_frame env_env in
      run%success SET_FRAME env addVars in
      fold%let
      along addVars_cdr
      as endp, _, endp_list do
        let endTag := list_tagval endp_list in
        do%success (addVars, s, sprev) := (addVars, addVars, R_NilValue : _SEXP)
        whileb s <> endp do
          read%list _, s_cdr, s_tag := s in
            ifb s_tag = endTag then
              ifc sprev '== R_NilValue then
                let addVars := s_cdr in
                run%success SET_FRAME env addVars in
                result_success (addVars, s_cdr, sprev)
              else
                set%cdr s_cdr := sprev in
                result_success (addVars, s_cdr, sprev)
            else result_success (addVars, s_cdr, s) using runs in
        result_skip using runs.

Definition FRAME_LOCK_BIT := 14.

Definition FRAME_IS_LOCKED rho : result_bool :=
  add%stack "FRAME_IS_LOCKED" in
  read%defined rho_ := rho in
  result_success (nth_bit FRAME_LOCK_BIT (gp rho_) ltac:(nbits_ok)).

Definition getActiveValue f : result_SEXP :=
  add%stack "getActiveValue" in
  let%success expr := lcons f R_NilValue in
  runs_eval runs expr R_GlobalEnv.

Definition SYMBOL_BINDING_VALUE s : result_SEXP :=
  add%stack "SYMBOL_BINDING_VALUE" in
  read%sym _, s_sym := s in
  if%success IS_ACTIVE_BINDING s then
    getActiveValue (sym_value s_sym)
  else result_success (sym_value s_sym).

Definition setActiveValue (vfun val : _SEXP) :=
  add%stack "setActiveValue" in
  let%success arg_tail := lcons val R_NilValue in
  let%success arg := lcons R_QuoteSymbol arg_tail in
  let%success expr_tail := lcons arg R_NilValue in
  let%success expr := lcons vfun expr_tail in
  run%success runs_eval runs expr R_GlobalEnv in
  result_skip.

Definition SET_BINDING_VALUE b val :=
  add%stack "SET_BINDING_VALUE" in
  if%success BINDING_IS_LOCKED b then
    result_error "Can not change value of locked binding."
  else
    if%success IS_ACTIVE_BINDING b then
      read%list b_car, _, _ := b in
      setActiveValue b_car val
    else
      set%car b := val in
      result_skip.

Definition R_SetVarLocValue vl value :=
  add%stack "R_SetVarLocValue" in
  SET_BINDING_VALUE vl value.

Definition R_GetVarLocSymbol vl : result_SEXP :=
  add%stack "R_GetVarLocSymbol" in
  read%list _, _, vl_tag := vl in
  result_success vl_tag.

Definition BINDING_VALUE b : result_SEXP :=
  add%stack "BINDING_VALUE" in
  read%list b_car, _, _ := b in
  if%success IS_ACTIVE_BINDING b then
    getActiveValue b_car
  else result_success b_car.

Definition IS_USER_DATABASE rho : result_bool :=
  add%stack "IS_USER_DATABASE" in
  read%defined rho_ := rho in
  let%success inh := inherits runs rho "UserDefinedDatabase" in
  result_success (obj rho_ && inh).

Definition SET_SYMBOL_BINDING_VALUE sym val :=
  add%stack "SET_SYMBOL_BINDING_VALUE" in
  if%success BINDING_IS_LOCKED sym then
    result_error "Cannot change value of locked binding."
  else if%success IS_ACTIVE_BINDING sym then
    read%sym _, sym_sym := sym in
    setActiveValue (sym_value sym_sym) val
  else SET_SYMVALUE sym val.

Definition simple_as_environment arg : result_SEXP :=
  add%stack "simple_as_environment" in
  let%success arg_s4 := IS_S4_OBJECT arg in
  let%success arg_type := TYPEOF arg in
  ifb arg_s4 /\ arg_type = S4Sxp then
    unimplemented_function "R_getS4DataSlot"
  else (R_NilValue : result_SEXP).

Definition R_EnvironmentIsLocked env : result_bool :=
  add%stack "R_EnvironmentIsLocked" in
  let%success env_type := TYPEOF env in
  ifb env_type = NilSxp then
    result_error "Use of NULL environment is defunct."
  else
    let%success env :=
      ifb env_type <> EnvSxp then
        simple_as_environment env
      else (env : result_SEXP) in
    let%success env_type := TYPEOF env in
    ifb env_type <> EnvSxp then
      result_error "Not an environment."
    else
      FRAME_IS_LOCKED env.

Definition gsetVar (symbol value rho : _SEXP) : result unit :=
  add%stack "gsetVar" in
  if%success FRAME_IS_LOCKED rho then
    read%sym symbol_, symbol_sym := symbol in
    ifc sym_value symbol_sym '== R_UnboundValue then
      result_error "Can not add such a binding to the base environment."
    else result_skip in
  SET_SYMBOL_BINDING_VALUE symbol value.

Definition defineVar (symbol value rho : _SEXP) : result unit :=
  add%stack "defineVar" in
  ifc rho '== R_EmptyEnv then
    result_error "Can not assign values in the empty environment."
  else if%success IS_USER_DATABASE rho then
    result_not_implemented "R_ObjectTable"
  else ifc (rho '== R_BaseNamespace) '|| (rho '== R_BaseEnv) then
    gsetVar symbol value rho
  else
    if%success IS_SPECIAL_SYMBOL symbol then
      run%success SET_SPECIAL_SYMBOL rho false in
      result_skip in
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifc list_tagval frame_list '== symbol then
        run%success SET_BINDING_VALUE frame value in
        run%success SET_MISSING frame 0 ltac:(nbits_ok) in
        result_rreturn tt
      else result_rskip using runs in
    if%success FRAME_IS_LOCKED rho then
      result_error "Can not add a binding to a locked environment."
    else
      let%success l := CONS value (env_frame rho_env) in
      run%success SET_FRAME rho l in
      set%tag l := symbol in
      result_skip.

Definition setVarInFrame (rho symbol value : _SEXP) : result_SEXP :=
  add%stack "setVarInFrame" in
  ifc rho '== R_EmptyEnv then
    (R_NilValue : result_SEXP)
  else if%success IS_USER_DATABASE rho then
    result_not_implemented "R_ObjectTable"
  else ifc (rho '== R_BaseNamespace) '|| (rho '== R_BaseEnv) then
    read%sym _, symbol_sym := symbol in
    ifc sym_value symbol_sym '== R_UnboundValue then
      (R_NilValue : result_SEXP)
    else
      run%success SET_SYMBOL_BINDING_VALUE symbol value in
      (symbol : result_SEXP)
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifc list_tagval frame_list '== symbol then
        run%success SET_BINDING_VALUE frame value in
        run%success SET_MISSING frame 0 ltac:(nbits_ok) in
        let%fetch symbol in
        result_rreturn symbol
      else result_rskip using runs in
      (R_NilValue : result_SEXP).

Definition setVar (symbol value rho : _SEXP) :=
  add%stack "setVar" in
  do%return rho := rho
  while rho '!= R_EmptyEnv do
    let%success vl := setVarInFrame rho symbol value in
    ifc vl '!= R_NilValue then
      result_rreturn tt
    else
      read%env rho_, rho_env := rho in
      result_rsuccess (env_enclos rho_env)
  using runs in
  defineVar symbol value R_GlobalEnv.

Definition findVarInFrame3 rho symbol (doGet : bool) : result_SEXP :=
  add%stack "findVarInFrame3" in
  let%success rho_type := TYPEOF rho in
  ifb rho_type = NilSxp then
    result_error "Use of NULL environment is defunct."
  else ifc (rho '== R_BaseNamespace) '|| (rho '== R_BaseEnv) then
    SYMBOL_BINDING_VALUE symbol
  else ifc rho '== R_EmptyEnv then
    (R_UnboundValue : result_SEXP)
  else
    if%success IS_USER_DATABASE rho then
      result_not_implemented "R_ObjectTable"
    else
      (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
      read%defined rho_ := rho in
      let%env _, rho_env := rho_ in
      fold%return
      along env_frame rho_env
      as frame, _, frame_list do
        ifc list_tagval frame_list '== symbol then
          let%success r := BINDING_VALUE frame in
          result_rreturn r
        else result_rskip using runs in
      (R_UnboundValue : result_SEXP).

Definition findVarInFrame rho symbol : result_SEXP :=
  add%stack "findVarInFrame" in
  findVarInFrame3 rho symbol true.

Definition R_IsNamespaceEnv (rho : _SEXP) : result_bool :=
  add%stack "R_IsNamespaceEnv" in
  ifc rho '== R_BaseNamespace then
    result_success true
  else
    let%success rho_type := TYPEOF rho in
    ifb rho_type = EnvSxp then
      let%success info := findVarInFrame3 rho R_NamespaceSymbol true in
      let%success info_type := TYPEOF info in
      ifc (info '!= R_UnboundValue) '&& 'decide (info_type = EnvSxp) then
        let%success spec_install := install runs "spec" in
        let%success spec := findVarInFrame3 info spec_install true in
        let%success spec_type := TYPEOF spec in
        ifc (spec '!= R_UnboundValue) '&& 'decide (spec_type = StrSxp) then
          let%success spec_len := LENGTH spec in
          result_success (decide (spec_len > 0))
        else result_success false
      else result_success false
    else result_success false.

Definition EnsureLocal symbol rho : result_SEXP :=
  add%stack "EnsureLocal" in
  let%success vl := findVarInFrame3 rho symbol true in
  ifc vl '!= R_UnboundValue then
    let%success vl := runs_eval runs symbol rho in
    let%success vl :=
      if%success MAYBE_SHARED vl then
        let%success vl := shallow_duplicate runs vl in
        run%success defineVar symbol vl rho in
        run%success INCREMENT_NAMED vl in
        result_success vl
      else result_success vl in
    result_success vl
  else
    read%env _, rho_env := rho in
    let%success vl := runs_eval runs symbol (env_enclos rho_env) in
    ifc vl '== R_UnboundValue then
      result_error "Object not found."
    else
      let%success vl := shallow_duplicate runs vl in
      run%success defineVar symbol vl rho in
      run%success INCREMENT_NAMED vl in
      result_success vl.

Definition findVar symbol rho : result_SEXP :=
  add%stack "findVar" in
  let%success rho_type := TYPEOF rho in
  ifb rho_type = NilSxp then
    result_error "Use of NULL environment is defunct."
  else ifb rho_type <> EnvSxp then
    result_error "Argument ‘rho’ is not an environment."
  else
    do%return rho := rho
    while rho '!= R_EmptyEnv do
      let%success vl := findVarInFrame3 rho symbol true in
      ifc vl '!= R_UnboundValue then
        result_rreturn vl
      else
        read%env _, rho_env := rho in
        result_rsuccess (env_enclos rho_env) using runs in
    (R_UnboundValue : result_SEXP).

Definition findVarLocInFrame (rho symbol : _SEXP) : result_SEXP :=
  add%stack "findVarLocInFrame" in
  ifc (rho '== R_BaseEnv) '|| (rho '== R_BaseNamespace) then
    result_error "It can’t be used in the base environment."
  else ifc rho '== R_EmptyEnv then
    (R_NilValue : result_SEXP)
  else if%success IS_USER_DATABASE rho then
    unimplemented_function "R_ExternalPtrAddr"
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifc list_tagval frame_list '== symbol then
        result_rreturn frame
      else result_rskip using runs in
    (R_NilValue : result_SEXP).

Definition R_findVarLocInFrame rho symbol : result_SEXP :=
  add%stack "R_findVarLocInFrame" in
  let%success binding := findVarLocInFrame rho symbol in
  ifc binding '== R_NilValue then
    result_success NULL
  else result_success binding.

Definition RemoveFromList (thing list : _SEXP) :=
  add%stack "RemoveFromList" in
  ifc list '== R_NilValue then
    result_success None
  else
    read%list _, list_cdr, list_tag := list in
    ifc list_tag '== thing then
      set%car list := R_UnboundValue in
      run%success LOCK_BINDING list in
      let rest := list_cdr in
      set%cdr list := R_NilValue in
      result_success (Some rest)
    else
      let next := list_cdr in
      fold%return last := list
      along next
      as next, _, next_list do
        ifc list_tagval next_list '== thing then
          set%car next := R_UnboundValue in
          run%success LOCK_BINDING next in
          set%cdr last := list_cdrval next_list in
          set%cdr next := R_NilValue in
          let%fetch list in
          result_rreturn (Some list)
        else result_rsuccess next using runs in
      result_success None.


Definition unbindVar (symbol rho : _SEXP) :=
  add%stack "unbindVar" in
  ifc rho '== R_BaseNamespace then
    result_error "Can’t unbind in the base namespace."
  else ifc rho '== R_BaseEnv then
    result_error "Unbinding in the base environment is unimplemented."
  else if%success FRAME_IS_LOCKED rho then
    result_error "Can’t remove bindings from a locked environment."
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho in
    if%defined list := RemoveFromList symbol (env_frame rho_env) then
      SET_FRAME rho list
    else result_skip.

Definition ddVal symbol :=
  add%stack "ddVal" in
  let%success symbol_name := PRINTNAME symbol in
  let%success buf := CHAR symbol_name in
  ifb String.substring 0 2 buf = ".."%string /\ String.length buf > 2 then
    let buf := String.substring 2 (String.length buf - 2) in
    unimplemented_function "strtol"
  else result_success 0.

Definition ddfindVar (symbol rho : _SEXP) : result_SEXP :=
  unimplemented_function "ddfindVar".


Definition findFun3 (symbol rho call : _SEXP) : result_SEXP :=
  add%stack "findFun3" in
  let%success rho :=
    if%success IS_SPECIAL_SYMBOL symbol then
      do%success rho := rho
      while let%success special := NO_SPECIAL_SYMBOLS rho in
            ((rho '!= R_EmptyEnv) '&& special : result_bool) do
        read%env _, rho_env := rho in
        result_success (env_enclos rho_env)
      using runs in
      result_success rho
    else
      (rho : result_SEXP) in
  do%return rho := contextual_ret rho
  while rho '!= R_EmptyEnv do
    let%success vl := findVarInFrame3 rho symbol true in
    run%return
      ifc vl '!= R_UnboundValue then
        let%success vl_type := TYPEOF vl in
        let%success vl :=
          ifb vl_type = PromSxp then
            runs_eval runs vl rho
          else result_success vl in
        let%success vl_type := TYPEOF vl in
        ifb vl_type = CloSxp \/ vl_type = BuiltinSxp \/ vl_type = SpecialSxp then
          result_rreturn vl
        else ifc vl '== R_MissingArg then
          let%success str_symbol := PRINTNAME symbol in
          let%success str_symbol_ := CHAR str_symbol in
          result_error ("Argument “" ++ str_symbol_ ++ "” is missing, with no default.")
        else result_rskip
      else result_rskip in
    read%env _, rho_env := rho in
    result_rsuccess (env_enclos rho_env)
  using runs in
  let%success str_symbol := PRINTNAME symbol in
  let%success str_symbol_ := CHAR str_symbol in
  result_error ("Could not find function “" ++ str_symbol_ ++ "”.").

Definition findFun symbol rho : result_SEXP :=
  add%stack "findFun" in
  let%success R_CurrentExpression := result_not_implemented "R_CurrentExpression" in
  findFun3 symbol rho R_CurrentExpression.

Definition findRootPromise p : result_SEXP :=
  add%stack "findRootPromise" in
  let%success p_type := TYPEOF p in
  ifb p_type = PromSxp then
    do%success p := p
    while
      let%success p := PREXPR p in
      let%success p_type := TYPEOF p in
      result_success (decide (p_type = PromSxp))
    do
      PREXPR p using runs in
    result_success p
  else (p : result_SEXP).

Definition R_isMissing (symbol rho : _SEXP) : result_bool :=
  add%stack "R_isMissing" in
  ifc symbol '== R_MissingArg then
    result_success true
  else
    let%success (s, ddv) :=
      if%success DDVAL symbol then
        let%success d := ddVal symbol in
        let%contextual dot := R_DotsSymbol : _SEXP in
        result_success (dot, d)
      else
        let%fetch symbol in
        result_success (symbol, 0) in
    ifc (rho '== R_BaseEnv) '|| (rho '== R_BaseNamespace) then
      result_success false
    else
      let%success vl := findVarLocInFrame rho s in
      ifc vl '!= R_NilValue then
        let%exit vl :=
          if%success DDVAL symbol then
            read%list vl_car, _, _ := vl in
            let%success vl_car_len := R_length runs vl_car in
            ifc decide (vl_car_len < ddv) '|| (vl_car '== R_MissingArg) then
              result_rreturn true
            else
              let%success n := nthcdr runs vl_car (ddv - 1) in
              result_rsuccess n
          else result_rsuccess vl in
        let%success vl_mis := MISSING vl in
        read%list vl_car, _, _ := vl in
        ifc decide (vl_mis = true) '|| (vl_car '== R_MissingArg) then
          result_success true
        else if%success IS_ACTIVE_BINDING vl then
          result_success false
        else
          let%success vl_car_rp := findRootPromise vl_car in
          set%car vl := vl_car_rp in
          let vl_cat := vl_car_rp in
          let%success vl_car_type := TYPEOF vl_car in
          ifb vl_car_type = PromSxp then
            read%prom _, vl_car_prom := vl_car in
            let%success vl_car_expr := PREXPR vl_car in
            let%success vl_car_expr_type := TYPEOF vl_car_expr in
            ifc (prom_value vl_car_prom '== R_UnboundValue)
                '&& decide (vl_car_expr_type = SymSxp) then
              let%success vl_car_prseen := PRSEEN vl_car in
              ifb vl_car_prseen = 1 then
                result_success true
              else
                let%success oldseen := PRSEEN_direct vl_car in
                run%success SET_PRSEEN vl_car 1 ltac:(nbits_ok) in
                let%success val :=
                  let%success vl_car_prexpr := PREXPR vl_car in
                  let%success vl_car_prenv := PRENV vl_car in
                  runs_R_isMissing runs vl_car_prexpr vl_car_prenv in
                run%success SET_PRSEEN_direct vl_car oldseen in
                result_success val
            else result_success false
          else result_success false
      else result_success false.

End Parameterised.

