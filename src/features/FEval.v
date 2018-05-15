(** Features.FEval.
  The function names of this file correspond to the function names
  in the file main/eval.c. **)

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
Require Import FErrors.
Require Import FUtil.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

Arguments WrongArgCount [A].


Definition CheckFormals S ls :=
  add%stack "CheckFormals" in
  if%success isList globals S ls using S then
    fold%success
    along ls
    as _, ls_tag do
      let%success ls_tag_type := TYPEOF S ls_tag using S in
      ifb ls_tag_type <> SymSxp then
        result_error S "Invalid formal argument list (not a symbol)."
      else result_skip S using S, runs, globals in
    result_skip S
  else result_error S "Invalid formal argument list (not a list).".

Definition asym := [":=" ; "<-" ; "<<-" ; "="]%string.

Definition lookupAssignFcnSymbol S vfun :=
  add%stack "lookupAssignFcnSymbol" in
  findVarInFrame globals runs S R_ReplaceFunsTable vfun.

Definition enterAssignFcnSymbol S vfun val :=
  add%stack "enterAssignFcnSymbol" in
  defineVar globals runs S vfun val R_ReplaceFunsTable.

Definition installAssignFcnSymbol S vfun :=
  add%stack "installAssignFcnSymbol" in
  let%success fu_name := PRINTNAME S vfun using S in
  let%success fu_name_ := CHAR S fu_name using S in
  let%success val := install globals runs S (fu_name_ ++ "<-") using S in
  run%success enterAssignFcnSymbol S vfun val using S in
  result_success S val.

Definition getAssignFcnSymbol S (vfun : SEXP) :=
  add%stack "getAssignFcnSymbol" in
  ifb vfun = R_SubsetSym then
    result_success S (R_SubassignSym : SEXP)
  else ifb vfun = R_Subset2Sym then
    result_success S (R_Subassign2Sym : SEXP)
  else ifb vfun = R_DollarSymbol then
    result_success S (R_DollarGetsSymbol : SEXP)
  else
    let%success val := lookupAssignFcnSymbol S vfun using S in
    ifb val <> R_UnboundValue then
      result_success S val
    else installAssignFcnSymbol S vfun.

Definition SET_TEMPVARLOC_FROM_CAR S loc lhs :=
  add%stack "SET_TEMPVARLOC_FROM_CAR" in
  read%list lhs_car, _, _ := lhs using S in
  let v := lhs_car in
  if%success MAYBE_SHARED S v using S then
    let%success v := shallow_duplicate globals runs S v using S in
    run%success ENSURE_NAMED S v using S in
    set%car lhs := v using S in
    result_skip S in
  R_SetVarLocValue globals runs S loc v.

Definition applydefine S (call op args rho : SEXP) : result SEXP :=
  add%stack "applydefine" in
  read%list args_car, args_cdr, _ := args using S in
  let expr := args_car in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let%success rhs := eval globals runs S args_cdr_car rho using S in
  let saverhs := rhs in
  ifb rho = R_BaseNamespace then
    result_error S "Can’t do complex assignments in base namespace."
  else ifb rho = R_BaseEnv then
    result_error S "Can’t do complex assignments in base environment."
  else
    run%success defineVar globals runs S R_TmpvalSymbol R_NilValue rho using S in
    let%success tmploc := R_findVarLocInFrame globals runs S rho R_TmpvalSymbol using S in
    let%success cntxt :=
      begincontext globals S Ctxt_CCode call R_BaseEnv R_BaseEnv R_NilValue R_NilValue using S in
    let%success op_val := PRIMVAL runs S op using S in
    let%success lhs :=
      read%list _, expr_cdr, _ := expr using S in
      read%list expr_cdr_car, _, _ := expr_cdr using S in
      evalseq globals runs S expr_cdr_car rho (decide (op_val = 1 \/ op_val = 3)) tmploc using S in
    let%success rhsprom := mkRHSPROMISE globals S args_cdr_car rhs using S in
    do%success (lhs, expr) := (lhs, expr)
    while
        read%list _, expr_cdr, _ := expr using S in
        read%list expr_cdr_car, _, _ := expr_cdr using S in
        isLanguage globals S expr_cdr_car do
      read%list expr_car, expr_cdr, _ := expr using S in
      read%list expr_cdr_car, expr_cdr_cdr, _ := expr_cdr using S in
      let%success tmp :=
        let%success expr_car_type := TYPEOF S expr_car using S in
        ifb expr_car_type = SymSxp then
          getAssignFcnSymbol S expr_car
        else
          read%list expr_car_car, expr_car_cdr, _ := expr_car using S in
          let%success expr_car_len := R_length globals runs S expr_car using S in
          read%list expr_car_cdr_car, expr_car_cdr_cdr, _ := expr_car_cdr using S in
          read%list expr_car_cdr_cdr_car, _, _ := expr_car_cdr_cdr using S in
          let%success expr_car_cdr_cdr_car_type := TYPEOF S expr_car_cdr_cdr_car using S in
          ifb expr_car_type = LangSxp
              /\ (expr_car_car = R_DoubleColonSymbol \/ expr_car_car = R_TripleColonSymbol)
              /\ expr_car_len = 3 /\ expr_car_cdr_cdr_car_type = SymSxp then
            let%success tmp := getAssignFcnSymbol S expr_car_cdr_cdr_car using S in
            let%success tmp := lang3 globals S expr_car_car expr_car_cdr_car tmp using S in
            result_success S tmp
          else result_error S "Invalid function in complex assignment." using S in
      run%success SET_TEMPVARLOC_FROM_CAR S tmploc lhs using S in
      let%success rhs :=
        replaceCall globals runs S tmp R_TmpvalSymbol expr_cdr_cdr rhsprom using S in
      let%success rhs := eval globals runs S rhs rho using S in
      run%success SET_PRVALUE S rhsprom rhs using S in
      run%success SET_PRCODE S rhsprom rhs using S in
      read%list _, lhs_cdr, _ := lhs using S in
      result_success S (lhs_cdr, expr_cdr_car) using S, runs in
    read%list expr_car, expr_cdr, _ := expr using S in
    let%success afun :=
      let%success expr_car_type := TYPEOF S expr_car using S in
      ifb expr_car_type = SymSxp then
        getAssignFcnSymbol S expr_car
      else
        read%list expr_car_car, expr_car_cdr, _ := expr_car using S in
        let%success expr_car_len := R_length globals runs S expr_car using S in
        read%list expr_car_cdr_car, expr_car_cdr_cdr, _ := expr_car_cdr using S in
        read%list expr_car_cdr_cdr_car, _, _ := expr_car_cdr_cdr using S in
        let%success expr_car_cdr_cdr_car_type := TYPEOF S expr_car_cdr_cdr_car using S in
        ifb expr_car_type = LangSxp
            /\ (expr_car_car = R_DoubleColonSymbol \/ expr_car_car = R_TripleColonSymbol)
            /\ expr_car_len = 3 /\ expr_car_cdr_cdr_car_type = SymSxp then
          let%success afun := getAssignFcnSymbol S expr_car_cdr_cdr_car using S in
          let%success afun := lang3 globals S expr_car_car expr_car_cdr_car afun using S in
          result_success S afun
        else result_error S "Invalid function in complex assignment (after the loop)." using S in
    run%success SET_TEMPVARLOC_FROM_CAR S tmploc lhs using S in
    let%success expr :=
      let%success R_asymSymbol_op :=
        ifb op_val < 0 \/ op_val >= length (R_asymSymbol S) then
          result_error S "Out of bound access to R_asymSymbol."
        else
          let%defined sym := nth_option (Z.to_nat op_val) (R_asymSymbol S) using S in
          result_success S sym using S in
      read%list _, lhs_cdr, _ := lhs using S in
      read%list _, expr_cdr_cdr, _ := expr_cdr using S in
      assignCall globals runs S R_asymSymbol_op lhs_cdr afun R_TmpvalSymbol expr_cdr_cdr rhsprom using S in
    let%success expr := eval globals runs S expr rho using S in
    run%success endcontext globals runs S cntxt using S in
    run%success unbindVar globals runs S R_TmpvalSymbol rho using S in
    run%success INCREMENT_NAMED S saverhs using S in
    result_success S saverhs.

Definition do_set S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_set" in
  let%success op_val := PRIMVAL runs S op using S in
  let wrong S :=
    ifb op_val < 0 then
      result_error S "Negative offset."
    else
      let%defined n := nth_option (Z.to_nat op_val) asym using S in
      WrongArgCount S n in
  ifb args = R_NilValue then wrong S
  else read%list args_car, args_cdr, _ := args using S in
  ifb args_cdr = R_NilValue then wrong S
  else read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
  ifb args_cdr_cdr <> R_NilValue then wrong S
  else
    let lhs := args_car in
    let%success lhs_type := TYPEOF S lhs using S in
    match lhs_type with
    | StrSxp
    | SymSxp =>
      let%success lhs :=
        ifb lhs_type = StrSxp then
          let%success lhs_char := STRING_ELT S lhs 0 using S in
          installTrChar globals runs S lhs_char
        else result_success S lhs using S in
      let%success rhs := eval globals runs S args_cdr_car rho using S in
      run%success INCREMENT_NAMED S rhs using S in
      run%success
        ifb op_val = 2 then
          read%env _, rho_env := rho using S in
          setVar globals runs S lhs rhs (env_enclos rho_env)
        else
          defineVar globals runs S lhs rhs rho using S in
      result_success S rhs
    | LangSxp => applydefine S call op args rho
    | _ => result_error S "Invalid left-hand side to assignment."
    end.

Definition do_function S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_function" in
  let%success op :=
    let%success op_type := TYPEOF S op using S in
    ifb op_type = PromSxp then
      let%success op := forcePromise globals runs S op using S in
      set%named op := named_plural using S in
      result_success S op
    else result_success S op using S in
  let%success len := R_length globals runs S args using S in
  ifb len < 2 then
    WrongArgCount S "function"
  else
    read%list args_car, args_cdr, _ := args using S in
    run%success CheckFormals S args_car using S in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
    let%success rval :=
      mkCLOSXP globals S args_car args_cdr_car rho using S in
    read%list args_cdr_cdr_car, _, _ := args_cdr_cdr using S in
    let srcref := args_cdr_cdr_car in
    let%success srcref_type := TYPEOF S srcref using S in
    run%success
      ifb srcref_type = NilSxp then
        run%success
          setAttrib globals runs S rval R_SrcrefSymbol srcref using S in
        result_skip S
      else result_skip S using S in
    result_success S rval.

Definition do_break S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_break" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  let%success op_val := PRIMVAL runs S op using S in
  match int_to_nbits_check op_val with
  | None => result_impossible S "The variable “op_val” should be of type “context_type”."
  | Some c => findcontext globals runs _ S c rho R_NilValue
  end.

Definition do_paren S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_paren" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, _, _ := args using S in
  result_success S args_car.

Definition getBlockSrcrefs S call : result SEXP :=
  add%stack "getBlockSrcrefs" in
  let%success srcrefs := getAttrib globals runs S call R_SrcrefSymbol using S in
  let%success srcrefs_type := TYPEOF S srcrefs using S in
  ifb srcrefs_type = VecSxp then
    result_success S srcrefs
  else result_success S (R_NilValue : SEXP).

Definition do_begin S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_begin" in
  ifb args <> R_NilValue then
    let%success srcrefs := getBlockSrcrefs S call using S in
    fold%success s := R_NilValue : SEXP
    along args
    as args_car, _ do
      let%success s := eval globals runs S args_car rho using S in
      result_success S s using S, runs, globals in
    result_success S s
  else result_success S (R_NilValue : SEXP).

Definition do_return S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_return" in
  let%success v :=
    ifb args = R_NilValue then
      result_success S (R_NilValue : SEXP)
    else
      read%list args_car, args_cdr, _ := args using S in
      ifb args_cdr = R_NilValue then
        eval globals runs S args_car rho
      else result_error S "Multi-argument returns are not permitted." using S in
  findcontext globals runs _ S (context_type_merge Ctxt_Browser Ctxt_Function) rho v.

Definition BodyHasBraces S body :=
  add%stack "BodyHasBraces" in
  if%success isLanguage globals S body using S then
    read%list body_car, _, _ := body using S in
    result_success S (decide (body_car = R_BraceSymbol))
  else result_success S false.

Definition do_if S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_if" in
  read%list args_car, args_cdr, _ := args using S in
  let%success Cond := eval globals runs S args_car rho using S in
  let%success (Stmt, vis) :=
    let%success asLogical := asLogicalNoNA globals runs S Cond call using S in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
    ifb asLogical <> 0 then
      result_success S (args_cdr_car, false)
    else
      let%success l := R_length globals runs S args using S in
      ifb l > 2 then
        read%list args_cdr_cdr_car, _, _ := args_cdr_cdr using S in
        result_success S (args_cdr_cdr_car, false)
      else result_success S (R_NilValue : SEXP, true) using S in
  if vis then
    result_success S Stmt
  else eval globals runs S Stmt rho.

Definition do_while S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_while" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list _, args_cdr, _ := args using S in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let body := args_cdr_car in
  let%success bgn := BodyHasBraces S body using S in
  let%success cntxt :=
    begincontext globals S Ctxt_Loop R_NilValue rho R_BaseEnv R_NilValue R_NilValue using S in
  set%longjump context_cjmpbuf cntxt as jmp using S, runs in
  run%success
    ifb jmp <> Ctxt_Break then
      do%let while
        read%list args_car, _, _ := args using S in
        let%success ev := eval globals runs S args_car rho using S in
        let%success al := asLogicalNoNA globals runs S ev call using S in
        result_success S (decide (al <> 0))
      do
        run%success eval globals runs S body rho using S in
        result_skip S using S, runs
    else result_skip S using S in
  run%success endcontext globals runs S cntxt using S in
  result_success S (R_NilValue : SEXP).

Definition do_repeat S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_repeat" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, _, _ := args using S in
  let body := args_car in
  let%success cntxt :=
    begincontext globals S Ctxt_Loop R_NilValue rho R_BaseEnv R_NilValue R_NilValue using S in
  set%longjump context_cjmpbuf cntxt as jmp using S, runs in
  run%success
    ifb jmp <> Ctxt_Break then
      do%let whileb True do
        run%success eval globals runs S body rho using S in
        result_skip S using S, runs
    else result_skip S using S in
  run%success endcontext globals runs S cntxt using S in
  result_success S (R_NilValue : SEXP).

Definition do_eval S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_eval" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  let expr := args_car in
  read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
  let env := args_cdr_car in
  read%list args_cdr_cdr_car, _, _ := args_cdr_cdr using S in
  let encl := args_cdr_cdr_car in
  let%success tEncl := TYPEOF S encl using S in
  let%success encl :=
    if%success isNull S encl using S then
      result_success S (R_BaseEnv : SEXP)
    else
      let%success encl_ie := isEnvironment S encl using S in
      ifb negb encl_ie then
        let%success encl := simple_as_environment globals S encl using S in
        let%success encl_ie := isEnvironment S encl using S in
        if negb encl_ie then
          result_error S "Invalid argument."
        else result_success S encl
      else result_success S encl using S in
  let%success env :=
    let%success env_s4 := IS_S4_OBJECT S env using S in
    let%success env_type := TYPEOF S env using S in
    ifb env_s4 /\ env_type = S4Sxp then
      unimplemented_function "R_getS4DataSlot"
    else result_success S env using S in
  let%success env_type := TYPEOF S env using S in
  let%success env :=
    match env_type with
    | NilSxp =>
      result_success S encl
    | EnvSxp =>
      result_success S env
    | ListSxp =>
      let%success d := duplicate globals runs S args_cdr_car using S in
      NewEnvironment globals runs S R_NilValue d encl
    | VecSxp =>
      unimplemented_function "VectorToPairListNamed"
    | IntSxp
    | RealSxp =>
      let%success env_len := R_length globals runs S env using S in
      ifb env_len <> 1 then
        result_error S "Numeric ‘envir’ argument not of length one."
      else
        let%success frame := asInteger globals S env using S in
        ifb frame = NA_INTEGER then
          result_error S "Invalid argument ‘envir’ after convertion."
        else unimplemented_function "R_sysframe"
    | _ => result_error S "Invalid argument ‘envir’."
    end using S in
  let%success expr :=
    let%success expr_type := TYPEOF S expr using S in
    let%success expr_bc := isByteCode S expr using S in
    ifb expr_type = LangSxp \/ expr_type = SymSxp \/ expr_bc then
      let%success cntxt :=
        begincontext globals S Ctxt_Return (context_call (R_GlobalContext S)) env rho args op using S in
      set%longjump context_cjmpbuf cntxt as jmp using S, runs in
      let%success expr :=
        ifb jmp <> empty_context_type then
          eval globals runs S expr env
        else
          let expr := R_ReturnedValue S in
          ifb expr = R_RestartToken then
            let S := state_with_context S (context_with_callflag cntxt Ctxt_Return) in
            result_error S "Restarts not supported in ‘eval’."
          else result_success S expr using S in
      run%success endcontext globals runs S cntxt using S in
      result_success S expr
    else ifb expr_type = ExprSxp then
      let%success srcrefs := getBlockSrcrefs S expr using S in
      let%success n := LENGTH globals S expr using S in
      let%success cntxt :=
        begincontext globals S Ctxt_Return (context_call (R_GlobalContext S)) env rho args op using S in
      set%longjump context_cjmpbuf cntxt as jmp using S, runs in
      let%success tmp :=
        ifb jmp <> empty_context_type then
          do%let tmp := R_NilValue : SEXP
          for i from 0 to n - 1 do
            unimplemented_function "getSrcref" using S
        else
          let tmp := R_ReturnedValue S in
          ifb tmp = R_RestartToken then
            let S := state_with_context S (context_with_callflag cntxt Ctxt_Return) in
            result_error S "Restarts not supported in ‘eval’."
          else result_success S tmp using S in
      run%success endcontext globals runs S cntxt using S in
      result_success S tmp
    else ifb expr_type = PromSxp then
      eval globals runs S expr rho
    else result_success S expr using S in
  result_success S expr.

End Parameters.

