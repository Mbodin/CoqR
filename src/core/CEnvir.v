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
Require Import Double.
Require Import Loops.
Require Import Conflicts.
Require Import CRinlinedfuns.
Require Import CMemory.
Require Import CDefn.
Require Import CRinternals.
Require Import CNames.
Require Import CDuplicate.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

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

End Parameterised.

