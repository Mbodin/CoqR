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
From CoqR Require Import Rcore.
From CoqR.features Require Import FErrors FUtil.

Section Parameters.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

Arguments WrongArgCount [A].


Definition CheckFormals ls :=
  add%stack "CheckFormals" in
  if%success isList globals ls then
    fold%success
    along ls
    as _, ls_tag do
      let%success ls_tag_type := TYPEOF ls_tag in
      ifb ls_tag_type <> SymSxp then
        result_error "Invalid formal argument list (not a symbol)."
      else result_skip using runs in
    result_skip
  else result_error "Invalid formal argument list (not a list).".

Definition asym := [":=" ; "<-" ; "<<-" ; "="]%string.

Definition lookupAssignFcnSymbol vfun :=
  add%stack "lookupAssignFcnSymbol" in
  findVarInFrame globals runs R_ReplaceFunsTable vfun.

Definition enterAssignFcnSymbol vfun val :=
  add%stack "enterAssignFcnSymbol" in
  defineVar globals runs vfun val R_ReplaceFunsTable.

Definition installAssignFcnSymbol vfun :=
  add%stack "installAssignFcnSymbol" in
  let%success fu_name := PRINTNAME vfun in
  let%success fu_name_ := CHAR fu_name in
  let%success val := install globals runs (fu_name_ ++ "<-") in
  run%success enterAssignFcnSymbol vfun val in
  result_success val.

Definition getAssignFcnSymbol (vfun : SEXP) :=
  add%stack "getAssignFcnSymbol" in
  ifb vfun = R_SubsetSym then
    result_success (R_SubassignSym : SEXP)
  else ifb vfun = R_Subset2Sym then
    result_success (R_Subassign2Sym : SEXP)
  else ifb vfun = R_DollarSymbol then
    result_success (R_DollarGetsSymbol : SEXP)
  else
    let%success val := lookupAssignFcnSymbol vfun in
    ifb val <> R_UnboundValue then
      result_success val
    else installAssignFcnSymbol vfun.

Definition SET_TEMPVARLOC_FROM_CAR loc lhs :=
  add%stack "SET_TEMPVARLOC_FROM_CAR" in
  read%list lhs_car, _, _ := lhs in
  let v := lhs_car in
  if%success MAYBE_SHARED v then
    let%success v := shallow_duplicate globals runs v in
    run%success ENSURE_NAMED v in
    set%car lhs := v in
    result_skip in
  R_SetVarLocValue globals runs loc v.

Definition applydefine (call op args rho : SEXP) : result_SEXP :=
  add%stack "applydefine" in
  read%list args_car, args_cdr, _ := args in
  let expr := args_car in

  (*  It's important that the rhs get evaluated first because
	assignment is right associative i.e.  a <- b <- c is parsed as
	a <- (b <- c).  *)

  read%list args_cdr_car, _, _ := args_cdr in
  let%success rhs := eval globals runs args_cdr_car rho in
  let saverhs := rhs in

  run%success
    let%success ans_named := NAMED rhs in
    ifb ans_named <> named_temporary then
      set%named rhs := named_plural in
      result_skip
    else result_skip
  in

  ifb rho = R_BaseNamespace then
    result_error "Can’t do complex assignments in base namespace."
  else ifb rho = R_BaseEnv then
    result_error "Can’t do complex assignments in base environment."
  else
    run%success defineVar globals runs R_TmpvalSymbol R_NilValue rho in
    let%success tmploc := R_findVarLocInFrame globals runs rho R_TmpvalSymbol in

    let%success cntxt :=
      begincontext globals Ctxt_CCode call R_BaseEnv R_BaseEnv R_NilValue R_NilValue in

    (*  Do a partial evaluation down through the LHS. *)
    let%success op_val := PRIMVAL runs op in
    let%success lhs :=
      read%list _, expr_cdr, _ := expr in
      read%list expr_cdr_car, _, _ := expr_cdr in
      evalseq globals runs expr_cdr_car rho (decide (op_val = 1 \/ op_val = 3)) tmploc in
    let%success rhsprom := mkRHSPROMISE globals args_cdr_car rhs in

    do%success (lhs, expr) := (lhs, expr)
    while
        read%list _, expr_cdr, _ := expr in
        read%list expr_cdr_car, _, _ := expr_cdr in
        isLanguage globals expr_cdr_car do
      read%list expr_car, expr_cdr, _ := expr in
      read%list expr_cdr_car, expr_cdr_cdr, _ := expr_cdr in
      let%success tmp :=
        let%success expr_car_type := TYPEOF expr_car in
        ifb expr_car_type = SymSxp then
          getAssignFcnSymbol expr_car
        else
          read%list expr_car_car, expr_car_cdr, _ := expr_car in
          let%success expr_car_len := R_length globals runs expr_car in
          read%list expr_car_cdr_car, expr_car_cdr_cdr, _ := expr_car_cdr in
          read%list expr_car_cdr_cdr_car, _, _ := expr_car_cdr_cdr in
          let%success expr_car_cdr_cdr_car_type := TYPEOF expr_car_cdr_cdr_car in
          ifb expr_car_type = LangSxp
              /\ (expr_car_car = R_DoubleColonSymbol \/ expr_car_car = R_TripleColonSymbol)
              /\ expr_car_len = 3 /\ expr_car_cdr_cdr_car_type = SymSxp then
            let%success tmp := getAssignFcnSymbol expr_car_cdr_cdr_car in
            let%success tmp := lang3 globals expr_car_car expr_car_cdr_car tmp in
            result_success tmp
          else result_error "Invalid function in complex assignment." in
      run%success SET_TEMPVARLOC_FROM_CAR tmploc lhs in
      let%success rhs :=
        replaceCall globals runs tmp R_TmpvalSymbol expr_cdr_cdr rhsprom in
      let%success rhs := eval globals runs rhs rho in
      run%success SET_PRVALUE rhsprom rhs in
      run%success SET_PRCODE rhsprom rhs in
      read%list _, lhs_cdr, _ := lhs in
      result_success (lhs_cdr, expr_cdr_car) using runs in
    read%list expr_car, expr_cdr, _ := expr in
    let%success afun :=
      let%success expr_car_type := TYPEOF expr_car in
      ifb expr_car_type = SymSxp then
        getAssignFcnSymbol expr_car
      else
        read%list expr_car_car, expr_car_cdr, _ := expr_car in
        let%success expr_car_len := R_length globals runs expr_car in
        read%list expr_car_cdr_car, expr_car_cdr_cdr, _ := expr_car_cdr in
        read%list expr_car_cdr_cdr_car, _, _ := expr_car_cdr_cdr in
        let%success expr_car_cdr_cdr_car_type := TYPEOF expr_car_cdr_cdr_car in
        ifb expr_car_type = LangSxp
            /\ (expr_car_car = R_DoubleColonSymbol \/ expr_car_car = R_TripleColonSymbol)
            /\ expr_car_len = 3 /\ expr_car_cdr_cdr_car_type = SymSxp then
          let%success afun := getAssignFcnSymbol expr_car_cdr_cdr_car in
          let%success afun := lang3 globals expr_car_car expr_car_cdr_car afun in
          result_success afun
        else result_error "Invalid function in complex assignment (after the loop)." in
    run%success SET_TEMPVARLOC_FROM_CAR tmploc lhs in
    let%success expr :=
      let%success R_asymSymbol_op :=
        read%state asymSymbol := R_asymSymbol in
        ifb op_val < 0 \/ op_val >= length asymSymbol then
          result_error "Out of bound access to R_asymSymbol."
        else
          let%defined sym := nth_option (Z.to_nat op_val) asymSymbol in
          result_success sym in
      read%list _, lhs_cdr, _ := lhs in
      read%list _, expr_cdr_cdr, _ := expr_cdr in
      assignCall globals runs R_asymSymbol_op lhs_cdr afun R_TmpvalSymbol expr_cdr_cdr rhsprom in
    let%success expr := eval globals runs expr rho in
    run%success endcontext globals runs cntxt in
    run%success unbindVar globals runs R_TmpvalSymbol rho in
    run%success INCREMENT_NAMED saverhs in
    result_success saverhs.

Definition do_set (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_set" in
  let%success op_val := PRIMVAL runs op in
  let wrong :=
    ifb op_val < 0 then
      result_error "Negative offset."
    else
      let%defined n := nth_option (Z.to_nat op_val) asym in
      WrongArgCount n in
  ifb args = R_NilValue then wrong
  else read%list args_car, args_cdr, _ := args in
  ifb args_cdr = R_NilValue then wrong
  else read%list args_cdr_car, args_cdr_cdr, _ := args_cdr in
  ifb args_cdr_cdr <> R_NilValue then wrong
  else
    let lhs := args_car in
    let%success lhs_type := TYPEOF lhs in
    match lhs_type with
    | StrSxp
    | SymSxp =>
      let%success lhs :=
        ifb lhs_type = StrSxp then
          let%success lhs_char := STRING_ELT lhs 0 in
          installTrChar globals runs lhs_char
        else result_success lhs in
      let%success rhs := eval globals runs args_cdr_car rho in
      run%success INCREMENT_NAMED rhs in
      run%success
        ifb op_val = 2 then
          read%env _, rho_env := rho in
          setVar globals runs lhs rhs (env_enclos rho_env)
        else
          defineVar globals runs lhs rhs rho in
      result_success rhs
    | LangSxp => applydefine call op args rho
    | _ => result_error "Invalid left-hand side to assignment."
    end.

Definition do_function (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_function" in
  let%success op :=
    let%success op_type := TYPEOF op in
    ifb op_type = PromSxp then
      let%success op := forcePromise globals runs op in
      set%named op := named_plural in
      result_success op
    else result_success op in
  let%success len := R_length globals runs args in
  ifb len < 2 then
    WrongArgCount "function"
  else
    read%list args_car, args_cdr, _ := args in
    run%success CheckFormals args_car in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr in
    let%success rval :=
      mkCLOSXP globals args_car args_cdr_car rho in
    read%list args_cdr_cdr_car, _, _ := args_cdr_cdr in
    let srcref := args_cdr_cdr_car in
    let%success srcref_type := TYPEOF srcref in
    run%success
      ifb not (srcref_type = NilSxp) then
        run%success
          setAttrib globals runs rval R_SrcrefSymbol srcref in
        result_skip
      else result_skip in
    result_success rval.

Definition do_break (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_break" in
  run%success Rf_checkArityCall globals runs op args call in
  let%success op_val := PRIMVAL runs op in
  match int_to_nbits_check op_val with
  | None => result_impossible "The variable “op_val” should be of type “context_type”."
  | Some c => findcontext globals runs _ c rho R_NilValue
  end.

Definition do_paren (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_paren" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, _, _ := args in
  result_success args_car.

Definition getBlockSrcrefs call : result_SEXP :=
  add%stack "getBlockSrcrefs" in
  let%success srcrefs := getAttrib globals runs call R_SrcrefSymbol in
  let%success srcrefs_type := TYPEOF srcrefs in
  ifb srcrefs_type = VecSxp then
    result_success srcrefs
  else result_success (R_NilValue : SEXP).

Definition do_begin (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_begin" in
  ifb args <> R_NilValue then
    let%success srcrefs := getBlockSrcrefs call in
    fold%success s := R_NilValue : SEXP
    along args
    as args_car, _ do
      let%success s := eval globals runs args_car rho in
      result_success s using runs in
    result_success s
  else result_success (R_NilValue : SEXP).

Definition do_return (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_return" in
  let%success v :=
    ifb args = R_NilValue then
      result_success (R_NilValue : SEXP)
    else
      read%list args_car, args_cdr, _ := args in
      ifb args_cdr = R_NilValue then
        eval globals runs args_car rho
      else result_error "Multi-argument returns are not permitted." in
  findcontext globals runs _ (context_type_merge Ctxt_Browser Ctxt_Function) rho v.

Definition BodyHasBraces body :=
  add%stack "BodyHasBraces" in
  if%success isLanguage globals body then
    read%list body_car, _, _ := body in
    result_success (decide (body_car = R_BraceSymbol))
  else result_success false.

(** Omitting vpi value as REPROTECT is not used **)
Definition ALLOC_LOOP_VAR v val_type :=
  add%stack "ALLOC_LOOP_VAR" in
    let%success v_maybeShared := MAYBE_SHARED v in
    let%success v :=
    ifb v = R_NilValue \/ v_maybeShared then
        let%success v := allocVector globals val_type 1 in
        set%named v := named_unique in
        result_success v
    else
      result_success v

    in
    result_success v.

Definition do_if (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_if" in
  read%list args_car, args_cdr, _ := args in
  let%success Cond := eval globals runs args_car rho in
  let%success (Stmt, vis) :=
    let%success asLogical := asLogicalNoNA globals runs Cond call in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr in
    ifb asLogical <> 0 then
      result_success (args_cdr_car, false)
    else
      let%success l := R_length globals runs args in
      ifb l > 2 then
        read%list args_cdr_cdr_car, _, _ := args_cdr_cdr in
        result_success (args_cdr_cdr_car, false)
      else result_success (R_NilValue : SEXP, true) in
  if vis then
    result_success Stmt
  else eval globals runs Stmt rho.

Definition do_while (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_while" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list _, args_cdr, _ := args in
  read%list args_cdr_car, _, _ := args_cdr in
  let body := args_cdr_car in
  let%success bgn := BodyHasBraces body in
  let%success cntxt :=
    begincontext globals Ctxt_Loop R_NilValue rho R_BaseEnv R_NilValue R_NilValue in
  set%longjump context_cjmpbuf cntxt as jmp using runs in
  run%success
    ifb jmp <> Ctxt_Break then
      do%let while
        read%list args_car, _, _ := args in
        let%success ev := eval globals runs args_car rho in
        let%success al := asLogicalNoNA globals runs ev call in
        result_success (decide (al <> 0))
      do
        run%success eval globals runs body rho in
        result_skip using runs
    else result_skip in
  run%success endcontext globals runs cntxt in
  result_success (R_NilValue : SEXP).


Definition do_for (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_for" in
    run%success Rf_checkArityCall globals runs op args call in
    read%list args_car, args_cdr, _ := args in
    let sym := args_car in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr in
    let val := args_cdr_car in
    read%list args_cdr_cdr_car, _, _ := args_cdr_cdr in
    let body := args_cdr_cdr_car in

    let%success sym_isSymbol := isSymbol sym in
    ifb negb sym_isSymbol then
      result_error "non-symbol loop variable"
    else

    (** Omitting RDEBUG and JIT check **)
    let%success val := eval globals runs val rho in

    let%success val :=
    let%success val_inherits := inherits globals runs val "factor" in
    ifb val_inherits then
      let%success tmp := asCharacterFactor globals runs val in
      result_success tmp
    else result_success val
    in
    let%success val_isList := isList globals val in
    let%success val_isNull := isNull val in
    let%success n :=
    ifb val_isList \/ val_isNull then
      R_length globals runs val
    else
      LENGTH globals val
    in

    let%success val_type := TYPEOF val in
    run%success defineVar globals runs sym R_NilValue rho in
    let%success cell := GET_BINDING_CELL globals runs sym rho in
    let%success bgn := BodyHasBraces body in

    (** bump up links count of sequence to avoid modification by loop code **)
    run%success INCREMENT_NAMED val in
    run%success INCREMENT_REFCNT val in

    (** Not protecting with index **)
    let v := R_NilValue in
    let%success cntxt := begincontext globals Ctxt_Loop R_NilValue rho R_BaseEnv R_NilValue R_NilValue in
    let for_break :=
      run%success endcontext globals runs cntxt in
      run%success DECREMENT_REFCNT val in (** Not sure if this works for val **)
      result_success (R_NilValue : SEXP) in

    set%longjump context_cjmpbuf cntxt as jmp using runs in
    ifb jmp = Ctxt_Break then for_break
    else ifb jmp = Ctxt_Next then result_not_implemented "goto for_next"
    else
      do%success val := val
      for i from 0 to n - 1 do
        let%success val :=
        match val_type with
        | ExprSxp
        | VecSxp => let%success val_i := VECTOR_ELT val i in
                    set%named val_i := named_plural in
                    run%success defineVar globals runs sym val_i rho in
                    result_success val
        | ListSxp => read%list val_car, _, _ := val in
                     set%named val_car := named_plural in
                     run%success defineVar globals runs sym val_car rho in
                     result_success val_car
        | _ => let%success v :=
               match val_type with
               | LglSxp => let%success v := ALLOC_LOOP_VAR v val_type in
                           read%Logical val_i := val at i in
                           write%Logical v at 0 := val_i in
                           result_success v
               | IntSxp => let%success v := ALLOC_LOOP_VAR v val_type in
                           read%Integer val_i := val at i in
                           write%Integer v at 0 := val_i in
                           result_success v
               | RealSxp => let%success v := ALLOC_LOOP_VAR v val_type in
                            read%Real val_i := val at i in
                            write%Real v at 0 := val_i in
                            result_success v
               | CplxSxp => let%success v := ALLOC_LOOP_VAR v val_type in
                            read%Complex val_i := val at i in
                            write%Complex v at 0 := val_i in
                            result_success v
               | StrSxp => let%success v := ALLOC_LOOP_VAR v val_type in
                           let%success val_i := STRING_ELT val i in
                           run%success SET_STRING_ELT v 0 val_i in
                           result_success v
               | RawSxp => result_not_implemented "Raw case not implemented"
               | _ => result_error "invalid for() loop sequence"
               end
               in
               read%list cell_car, _, _ := cell in
               run%success
               ifb cell_car = R_UnboundValue then
                 defineVar globals runs sym v rho
               else
                 run%success SET_BINDING_VALUE globals runs cell v in
                 defineVar globals runs sym v rho
               in result_success val
        end
      in
      run%success eval globals runs body rho in
      result_success val
    in
    for_break.

Definition do_repeat (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_repeat" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, _, _ := args in
  let body := args_car in
  let%success cntxt :=
    begincontext globals Ctxt_Loop R_NilValue rho R_BaseEnv R_NilValue R_NilValue in
  set%longjump context_cjmpbuf cntxt as jmp using runs in
  run%success
    ifb jmp <> Ctxt_Break then
      do%let whileb True do
        run%success eval globals runs body rho in
        result_skip using runs
    else result_skip in
  run%success endcontext globals runs cntxt in
  result_success (R_NilValue : SEXP).

Definition do_eval (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_eval" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, args_cdr, _ := args in
  let expr := args_car in
  read%list args_cdr_car, args_cdr_cdr, _ := args_cdr in
  let env := args_cdr_car in
  read%list args_cdr_cdr_car, _, _ := args_cdr_cdr in
  let encl := args_cdr_cdr_car in
  let%success tEncl := TYPEOF encl in
  let%success encl :=
    if%success isNull encl then
      result_success (R_BaseEnv : SEXP)
    else
      let%success encl_ie := isEnvironment encl in
      ifb negb encl_ie then
        let%success encl := simple_as_environment globals encl in
        let%success encl_ie := isEnvironment encl in
        if negb encl_ie then
          result_error "Invalid argument."
        else result_success encl
      else result_success encl in
  let%success env :=
    let%success env_s4 := IS_S4_OBJECT env in
    let%success env_type := TYPEOF env in
    ifb env_s4 /\ env_type = S4Sxp then
      unimplemented_function "R_getS4DataSlot"
    else result_success env in
  let%success env_type := TYPEOF env in
  let%success env :=
    match env_type with
    | NilSxp =>
      result_success encl
    | EnvSxp =>
      result_success env
    | ListSxp =>
      let%success d := duplicate globals runs args_cdr_car in
      NewEnvironment globals runs R_NilValue d encl
    | VecSxp =>
      unimplemented_function "VectorToPairListNamed"
    | IntSxp
    | RealSxp =>
      let%success env_len := R_length globals runs env in
      ifb env_len <> 1 then
        result_error "Numeric ‘envir’ argument not of length one."
      else
        let%success frame := asInteger globals env in
        ifb frame = NA_INTEGER then
          result_error "Invalid argument ‘envir’ after convertion."
        else unimplemented_function "R_sysframe"
    | _ => result_error "Invalid argument ‘envir’."
    end in
  let%success expr :=
    let%success expr_type := TYPEOF expr in
    let%success expr_bc := isByteCode expr in
    ifb expr_type = LangSxp \/ expr_type = SymSxp \/ expr_bc then
      let%success cntxt :=
        read%state GlobalContext := R_GlobalContext in
        begincontext globals Ctxt_Return (context_call GlobalContext) env rho args op in
      set%longjump context_cjmpbuf cntxt as jmp using runs in
      let%success expr :=
        ifb jmp = empty_context_type then
          eval globals runs expr env
        else
          read%state expr := R_ReturnedValue in
          ifb expr = R_RestartToken then
            map%state state_with_context (context_with_callflag cntxt Ctxt_Return) in
            result_error "Restarts not supported in ‘eval’."
          else result_success expr in
      run%success endcontext globals runs cntxt in
      result_success expr
    else ifb expr_type = ExprSxp then
      let%success srcrefs := getBlockSrcrefs expr in
      let%success n := LENGTH globals expr in
      let%success cntxt :=
        read%state GlobalContext := R_GlobalContext in
        begincontext globals Ctxt_Return (context_call GlobalContext) env rho args op in
      set%longjump context_cjmpbuf cntxt as jmp using runs in
      let%success tmp :=
        ifb jmp <> empty_context_type then
          do%let tmp := R_NilValue : SEXP
          for i from 0 to n - 1 do
            unimplemented_function "getSrcref"
        else
          read%state tmp := R_ReturnedValue in
          ifb tmp = R_RestartToken then
            map%state state_with_context (context_with_callflag cntxt Ctxt_Return) in
            result_error "Restarts not supported in ‘eval’."
          else result_success tmp in
      run%success endcontext globals runs cntxt in
      result_success tmp
    else ifb expr_type = PromSxp then
      eval globals runs expr rho
    else result_success expr in
  result_success expr.

Definition R_forceAndCall (e : SEXP) (n : int) (rho : SEXP) : result_SEXP :=
  add%stack "R_forceAndCall" in
  read%list e_car, e_cdr, _ := e in
  let%success fun_ :=
    let%success e_car_type := TYPEOF e_car in
    ifb e_car_type = SymSxp then
      findFun globals runs e_car rho
    else
      eval globals runs e_car rho in
  let%success fun_type := TYPEOF fun_ in
  let%success tmp :=
    ifb fun_type = SpecialSxp then
      (* let%success flag := PRIMPRINT fun_ in *)
      (* R_Visible = flag != 1 *)
      let%success f := PRIMFUN runs fun_ in
      let%success tmp := f e fun_ e_cdr rho in
      (* if (flag < 2) R_Visible = flag != 1 *)
      result_success tmp
    else ifb fun_type = BuiltinSxp then
      (* let%success flag := PRIMPRINT fun_ in *)
      let%success tmp := evalList globals runs e_cdr rho e 0 in
      (* if (flag < 2) R_Visible = flag != 1 *)
      let%success tmp :=
        let R_Profiling := false in
        let%success fun_infos := PPINFO runs fun_ in
        ifb R_Profiling \/ PPinfo_kind fun_infos = PP_FOREIGN then
          let%success cntxt :=
            begincontext globals Ctxt_Builtin e R_BaseEnv R_BaseEnv R_NilValue R_NilValue in
          let%success f := PRIMFUN runs fun_ in
          let%success tmp := f e fun_ tmp rho in
          run%success endcontext globals runs cntxt in
          result_success tmp
        else
          let%success f := PRIMFUN runs fun_ in
          f e fun_ tmp rho in
      (* if (flag < 2) R_Visible = flag != 1 *)
      result_success tmp
    else ifb fun_type = CloSxp then
      let%success tmp := promiseArgs globals runs e_cdr rho in
      do%success (a, i) := (tmp, 0 : int)
      whileb i < n /\ a <> R_NilValue do
        read%list p, a_cdr, _ := a in
        let%success p_type := TYPEOF p in
        run%success
          ifb p_type = PromSxp then
            eval globals runs p rho
          else ifb p = R_MissingArg then
            result_error "argument i is empty"
          else result_error "something weird happened" in
        result_success (a_cdr, 1 + i)%Z using runs in
      let pargs := tmp in
      let%success tmp := applyClosure globals runs e fun_ pargs rho R_NilValue in
      result_success tmp
    else result_error "attempt to apply non-function" in
  result_success tmp.

Definition do_forceAndCall (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_forceAndCall" in
  read%list _, call_cdr, _ := call in
  read%list call_cadr, e, _ := call_cdr in
  let%success call_cadr_eval := eval globals runs call_cadr rho in
  let%success n := asInteger globals call_cadr_eval in
  let%success e :=
    read%list e_car, e_cdr, _ := e in
    LCONS globals e_car e_cdr in
  let%success val := R_forceAndCall e n rho in
  result_success val.

End Parameters.

