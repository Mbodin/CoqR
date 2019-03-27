(** Core.CEval.
  The function names in this file correspond to the function
  names in the file main/eval.c. **)

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
Require Import CRinternals.
Require Import CMemory.
Require Import CRinlinedfuns.
Require Import CCoerce.
Require Import CDefn.
Require Import CContext.
Require Import CAttrib.
Require Import CMatch.
Require Import CEnvir.
Require Import CObjects.
Require Import CDuplicate.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition COPY_TAG vto vfrom :=
  add%stack "COPY_TAG" in
  read%list _, _, vfrom_tag := vfrom in
  ifb vfrom_tag <> R_NilValue then
    set%tag vto := vfrom_tag in
    result_skip
  else result_skip.

Definition mkRHSPROMISE expr rhs :=
  add%stack "mkRHSPROMISE" in
  R_mkEVPROMISE_NR globals expr rhs.

Definition asLogicalNoNA (s call : SEXP) :=
  add%stack "asLogicalNoNA" in
  let%exit cond :=
    if%success IS_SCALAR s LglSxp then
      let%success cond := SCALAR_LVAL s in
      ifb cond <> NA_LOGICAL then
        result_rreturn cond
      else result_rsuccess cond
    else
      if%success IS_SCALAR s IntSxp then
        let%success val := SCALAR_IVAL s in
        ifb val <> NA_INTEGER then
          ifb val <> 0 then
            result_rreturn (1 : int)
          else result_rreturn (0 : int)
        else result_rsuccess NA_LOGICAL
      else result_rsuccess NA_LOGICAL in
  let%success len := R_length globals runs s in
  ifb len > 1 then
    result_error "The condition has length > 1."
  else
    let%success cond :=
      ifb len > 0 then
        let%success s_type := TYPEOF s in
        match s_type with
        | LglSxp =>
          read%Logical cond := s at 0 in
          result_success cond
        | IntSxp =>
          read%Integer cond := s at 0 in
          result_success cond
        | _ =>
          asLogical globals s
        end
      else result_success cond in
    ifb cond = NA_LOGICAL then
      ifb len = 0 then
        result_error "Argument is of length zero."
      else
        if%success isLogical s then
          result_error "Missing value where TRUE/FALSE needed."
        else result_error "Argument is not interpretable as logical."
    else result_success cond.

Definition replaceCall vfun val args rhs :=
  add%stack "replaceCall" in
  let%success args_len := R_length globals runs args in
  let%success tmp := allocList globals (3 + args_len) in
  let ptmp := tmp in
  set%car ptmp := vfun in
  read%list _, ptmp_cdr, _ := ptmp in
  let ptmp := ptmp_cdr in
  set%car ptmp := val in
  read%list _, ptmp_cdr, _ := ptmp in
  let ptmp := ptmp_cdr in
  fold%success ptmp := ptmp
  along args
  as args_car, args_tag do
    set%car ptmp := args_car in
    set%tag ptmp := args_tag in
    read%list _, ptmp_cdr, _ := ptmp in
    result_success ptmp_cdr using runs, globals in
  set%car ptmp := rhs in
  set%tag ptmp := R_valueSym in
  set%type tmp := LangSxp in
  result_success tmp.

Definition assignCall op symbol vfun val args rhs :=
  add%stack "assignCall" in
  let%success val := replaceCall vfun val args rhs in
  lang3 globals op symbol val.

Definition forcePromise (e : SEXP) : result SEXP :=
  add%stack "forcePromise" in
  read%prom _, e_prom := e in
  ifb prom_value e_prom = R_UnboundValue then
    run%success
      let%success e_prseen := PRSEEN e in
      ifb e_prseen <> 0 then
        ifb e_prseen = 1 then
          result_error "Promise already under evaluation."
        else
          (** The C code emitted a warning here: restarting interrupted promise evaluation.
            This may be a sign that this part should be ignored. *)
          SET_PRSEEN e 1 ltac:(nbits_ok)
      else result_skip in
    run%success SET_PRSEEN e 1 ltac:(nbits_ok) in
    let%success val := runs_eval runs (prom_expr e_prom) (prom_env e_prom) in
    run%success SET_PRSEEN e 0 ltac:(nbits_ok) in
    set%named val := named_plural in
    read%prom e_, e_prom := e in
    let e_prom := {|
        prom_value := val ;
        prom_expr := prom_expr e_prom ;
        prom_env := R_NilValue
      |} in
    let e_ := {|
        NonVector_SExpRec_header := e_ ;
        NonVector_SExpRec_data := e_prom
      |} in
    write%defined e := e_ in
    result_success val
  else result_success (prom_value e_prom).

Definition R_execClosure (call newrho sysparent rho arglist op : SEXP)
    : result SEXP :=
  add%stack "R_execClosure" in
  let%success cntxt :=
    begincontext globals Ctxt_Return call newrho sysparent arglist op in
  read%clo op_, op_clo := op in
  let body := clo_body op_clo in
  (** JIT functions have been ignored here. **)
  let%success R_srcef := getAttrib globals runs op R_SrcrefSymbol in
  set%longjump context_cjmpbuf cntxt as jmp using runs in
  let%success cntxt_returnValue :=
    ifb jmp <> empty_context_type then
      if match context_jumptarget cntxt with
         | None => true
         | Some _ => false
         end then
        get%state S in
        ifb R_ReturnedValue S = R_RestartToken then
          let cntxt := context_with_callflag cntxt Ctxt_Return in
          get%state S in
          set%state state_with_context S cntxt in
          set%state update_R_ReturnedValue S R_NilValue in
          runs_eval runs body newrho
        else result_success (R_ReturnedValue S)
      else result_success NULL
    else runs_eval runs body newrho in
  let cntxt := context_with_returnValue cntxt cntxt_returnValue in
  get%state S in
  set%state state_with_context S cntxt in
  run%success endcontext globals runs cntxt in
  result_success (context_returnValue cntxt).

Definition applyClosure (call op arglist rho suppliedvars : SEXP) : result SEXP :=
  add%stack "applyClosure" in
  ifb rho = NULL then
    result_error "‘rho’ can’t be C NULL."
  else
    let%success rho_env := isEnvironment rho in
    if negb rho_env then
      result_error "‘rho’ must be an environment."
    else
      read%clo op_, op_clo := op in
      let formals := clo_formals op_clo in
      let savedrho := clo_env op_clo in
      let%success actuals := matchArgs_RC globals runs formals arglist call in
      let%success newrho := NewEnvironment globals runs formals actuals savedrho in
      fold%success a := actuals
      along formals
      as f_car, f_tag do
        read%list a_car, a_cdr, _ := a in
        run%success
          ifb a_car = R_MissingArg /\ f_car <> R_MissingArg then
            let%success newprom := mkPromise globals f_car newrho in
            set%car a := newprom in
            run%success SET_MISSING a 2 ltac:(nbits_ok) in
            result_skip
          else result_skip in
        result_success a_cdr using runs, globals in
      run%success
        ifb suppliedvars <> R_NilValue then
           addMissingVarsToNewEnv globals runs newrho suppliedvars
         else result_skip in
      if%success R_envHasNoSpecialSymbols globals runs newrho then
        SET_NO_SPECIAL_SYMBOLS newrho in
      let%success val :=
        get%state S in
        R_execClosure call newrho
          (ifb context_callflag (R_GlobalContext S) = Ctxt_Generic then
             context_sysparent (R_GlobalContext S)
           else rho)
          rho arglist op in
      result_success val.

Definition promiseArgs (el rho : SEXP) : result SEXP :=
  add%stack "promiseArgs" in
  let%success tail := CONS globals R_NilValue R_NilValue in
  fold%success (ans, tail) := (tail, tail)
  along el
  as el_car, el_tag do
    ifb el_car = R_DotsSymbol then
      let%success h := findVar globals runs el_car rho in
      let%success h_type := TYPEOF h in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%success tail := tail
        along h
        as h_car, h_tag do
          let%success h_car_type := TYPEOF h_car in
          run%success
            ifb h_car_type = PromSxp \/ h_car = R_MissingArg then
              let%success l := CONS globals h_car R_NilValue in
              set%cdr tail := l in
              result_skip
            else
              let%success prom :=
                mkPromise globals h_car rho in
              let%success l := CONS globals prom R_NilValue in
              set%cdr tail := l in
              result_skip in
          read%list _, tail_cdr, _ := tail in
          let tail := tail_cdr in
          run%success
            ifb h_tag <> R_NilValue then
              set%tag tail := h_tag in
              result_skip
            else result_skip in
          result_success tail
        using runs, globals in
        result_success (ans, tail)
      else ifb h <> R_MissingArg then
        result_error "‘...’ used in an incorrect context."
      else result_success (ans, tail)
    else ifb el_car = R_MissingArg then
      let%success l := CONS globals R_MissingArg R_NilValue in
      set%cdr tail := l in
      read%list _, tail_cdr, _ := tail in
      let tail := tail_cdr in
      set%tag tail := el_tag in
      result_success (ans, tail)
    else
      let%success prom :=
        mkPromise globals el_car rho in
      let%success l := CONS globals prom R_NilValue in
      set%cdr tail := l in
      read%list _, tail_cdr, _ := tail in
      let tail := tail_cdr in
      set%tag tail := el_tag in
      result_success (ans, tail)
  using runs, globals in
  read%list _, ans_cdr, _ := ans in
  result_success ans_cdr.

Definition PRIMFUN x :=
  add%stack "PRIMFUN" in
  read%prim _, x_prim := x in
  let%success x_fun := read_R_FunTab runs (prim_offset x_prim) in
  result_success (fun_cfun x_fun).

Definition PRIMVAL x :=
  add%stack "PRIMVAL" in
  read%prim _, x_prim := x in
  let%success x_fun := read_R_FunTab runs (prim_offset x_prim) in
  result_success (fun_code x_fun).

Definition PPINFO x :=
  add%stack "PPINFO" in
  read%prim _, x_prim := x in
  let%success x_fun := read_R_FunTab runs (prim_offset x_prim) in
  result_success (fun_gram x_fun).

Definition PRIMARITY x :=
  add%stack "PRIMARITY" in
  read%prim _, x_prim := x in
  let%success x_fun := read_R_FunTab runs (prim_offset x_prim) in
  result_success (fun_arity x_fun).

Definition PRIMINTERNAL x :=
  add%stack "PRIMINTERNAL" in
  read%prim _, x_prim := x in
  let%success x_fun := read_R_FunTab runs (prim_offset x_prim) in
  result_success (funtab_eval_arg_internal (fun_eval x_fun)).

Definition evalList (el rho call : SEXP) n :=
  add%stack "evalList" in
  fold%success (n, head, tail) := (n, R_NilValue : SEXP, R_NilValue : SEXP)
  along el
  as el_car, el_tag
    do
    let n := 1 + n in
    ifb el_car = R_DotsSymbol then
      let%success h := findVar globals runs el_car rho in
      let%success h_type := TYPEOF h in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%success tail := tail
        along h
        as h_car, h_tag
        do
          let%success tmp_ev := runs_eval runs h_car rho in
          let%success ev := CONS_NR globals tmp_ev R_NilValue in
          let%success head :=
            ifb head = R_NilValue then
              result_success ev
            else
              set%cdr tail := ev in
              result_success head in
          run%success
            ifb h_tag <> R_NilValue then
              set%tag ev := h_tag in
              result_skip
            else result_skip in
          result_success ev
        using runs, globals in
        result_success (n, head, tail)
      else ifb h <> R_MissingArg then
        result_error "‘...’ used in an incorrect context."
      else result_success (n, head, tail)
    else ifb el_car = R_MissingArg then
      result_error "Argument is empty."
    else
      let%success ev := runs_eval runs el_car rho in
      let%success ev := CONS_NR globals ev R_NilValue in
      let%success head :=
        ifb head = R_NilValue then
          result_success ev
        else
          set%cdr tail := ev in
          result_success head in
      run%success
        ifb el_tag <> R_NilValue then
          set%tag ev := el_tag in
          result_skip
        else result_skip in
      result_success (n, head, ev)
  using runs, globals in
  result_success head.

Definition evalListKeepMissing (el rho : SEXP) : result SEXP :=
  add%stack "evalListKeepMissing" in
  fold%success (head, tail) := (R_NilValue : SEXP, R_NilValue : SEXP)
  along el
  as _, _, el_list do
    let el_car := list_carval el_list in
    let el_cdr := list_cdrval el_list in
    ifb el_car = R_DotsSymbol then
      let%success h := findVar globals runs el_car rho in
      let%success h_type := TYPEOF h in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%let (head, tail) := (head, tail)
        along h
        as _, _, h_list do
          let h_car := list_carval h_list in
          let%success val :=
            ifb h_car = R_MissingArg then
              result_success (R_MissingArg : SEXP)
            else runs_eval runs h_car rho in
          run%success INCREMENT_LINKS val in
          let%success ev := CONS_NR globals val R_NilValue in
          let%success head :=
            ifb head = R_NilValue then
              result_success ev
            else
              set%cdr tail := ev in
              result_success head in
          run%success COPY_TAG ev h in
          result_success (head, ev) using runs, globals
      else ifb h <> R_MissingArg then
        result_error "‘...’ used in an incorrect context."
      else result_success (head, tail)
    else
      let%success val :=
        let%success el_car_sy := isSymbol el_car in
        let%success el_car_mi := R_isMissing globals runs el_car rho in
        ifb el_car = R_MissingArg \/ (el_car_sy /\ el_car_mi) then
          result_success (R_MissingArg : SEXP)
        else runs_eval runs el_car rho in
      run%success
        ifb el_cdr <> R_NilValue then
          INCREMENT_LINKS val
        else result_skip in
      let%success ev := CONS_NR globals val R_NilValue in
      let%success head :=
        ifb head = R_NilValue then
          result_success ev
        else
          set%cdr tail := ev in
          result_success head in
      run%success COPY_TAG ev el in
      result_success (head, ev) using runs, globals in
  fold%success
  along head
  as _, _, head_list do
    let el_cdr := list_cdrval head_list in
    let el_car := list_carval head_list in
    ifb el_cdr <> R_NilValue then
      DECREMENT_LINKS el_car
    else result_skip using runs, globals in
  result_success head.

Definition evalArgs el rho (dropmissing : bool) call n :=
  add%stack "evalArgs" in
  if dropmissing then
    evalList el rho call n
  else evalListKeepMissing el rho.

(** The original function [DispatchGroup] returns a boolean and, if this boolean is true,
  overwrites its additional argument [ans]. This naturally translates as an option type. **)
Definition DispatchGroup group (call op args rho : SEXP)
    : result (option SEXP) :=
  add%stack "DispatchGroup" in
  read%list args_car, args_cdr, _ := args in
  let%success args_car_is := isObject args_car in
  read%list args_cdr_car, _, _ := args_cdr in
  let%success args_cdr_car_is := isObject args_cdr_car in
  ifb args_car <> R_NilValue /\ ~ args_car_is /\ (args_cdr = R_NilValue \/ ~ args_cdr_car_is) then
    result_success None
  else
    let isOps := decide (group = "Ops"%string) in
    let%success args_len := R_length globals runs args in
    let%success args_car_S4 := IS_S4_OBJECT args_car in
    let%success args_cdr_car_S4 := IS_S4_OBJECT args_cdr_car in
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
              set%tag s := R_NilValue in
              result_skip using runs, globals
          else result_skip in
        let%success op_hm := R_has_methods op in
        let%success value := R_possible_dispatch call op args rho false in
        ifb op_hm /\ value <> NULL then
          result_rreturn (Some value)
        else result_rskip
      else result_rskip in
    read%list call_car, _, _ := call in
    run%exit
      if%success isSymbol call_car then
        let%success call_car_name := PRINTNAME call_car in
        let%success call_car_str := CHAR call_car_name in
        let cstr := String.index 0 "." call_car_str in
        match cstr with
        | None => result_rskip
        | Some cstr =>
          let cstr_ := String.substring (1 + cstr) (String.length call_car_str - cstr - 1) call_car_str in
          ifb cstr_ = "default"%string then
            result_rreturn None
          else result_rskip
        end
      else result_rskip in
    let%success nargs :=
      if isOps then
        R_length globals runs args
      else result_success 1 in
    read%list args_car, args_cdr, _ := args in
    run%exit
      let%success args_car_obj := isObject args_car in
      ifb nargs = 1 /\ ~ args_car_obj then
        result_rreturn None
      else result_rskip in
    let%success generic := PRINTNAME op in
    unimplemented_function "classForGroupDispatch".

Definition DispatchOrEval (call op : SEXP) (generic : string) (args rho : SEXP)
    (dropmissing argsevald : bool) : result (bool * SEXP) :=
  add%stack "DispatchOrEval" in
  let%success (x, dots) :=
    if argsevald then
      read%list args_car, _, _ := args in
      result_success (args_car, false)
    else
      fold%return (x, dots) := (R_NilValue : SEXP, false)
      along args as args_car, _ do
        ifb args_car = R_DotsSymbol then
          let%success h := findVar globals runs R_DotsSymbol rho in
          let%success h_type := TYPEOF h in
          ifb h_type = DotSxp then
            read%list h_car, _, _ := h in
            let%success h_car_type := TYPEOF h_car in
            ifb h_car_type <> PromSxp then
              result_error "Value in ‘...’ is not a promise."
            else
              let%success r := runs_eval runs h_car rho in
              result_rreturn (r, true)
          else ifb h <> R_NilValue /\ h <> R_MissingArg then
            result_error "‘...’ used in an incorrect context."
          else result_rsuccess (x, dots)
        else
          let%success r := runs_eval runs args_car rho in
          result_rreturn (r, false) using runs, globals in
      result_success (x, dots) in
  run%exit
    if%success isObject x then
      result_not_implemented "Object case."
    else result_rskip in
  let%success ans :=
    if negb argsevald then
      if dots then
        evalArgs args rho dropmissing call 0
      else
        read%list _, args_cdr, args_tag := args in
        let%success r := evalArgs args_cdr rho dropmissing call 1 in
        let%success ans := CONS_NR globals x r in
        let%success t := CreateTag globals runs args_tag in
        set%tag ans := t in
        result_success ans
    else result_success args in
  result_success (false, ans).

Definition DispatchAnyOrEval (call op : SEXP) (generic : string) (args rho : SEXP)
    (dropmissing argsevald : bool) : result (bool * SEXP) :=
  add%stack "DispatchAnyOrEval" in
  if%success R_has_methods op then
    result_not_implemented "Method case."
  else DispatchOrEval call op generic args rho dropmissing argsevald.

Definition eval (e rho : SEXP) :=
  add%stack "eval" in
  let%success e_type := TYPEOF e in
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
    set%named e := named_plural in
    result_success e
  | _ =>
    ifb rho = NULL then
      result_error "‘rho’ cannot be C NULL."
    else
      let%success rho_env := isEnvironment rho in
      if negb rho_env then
        result_error "‘rho’ must be an environment."
      else
        let%success e_type := TYPEOF e in
        match e_type with
        | BcodeSxp =>
          unimplemented_function "bcEval"
        | SymSxp =>
          ifb e = R_DotsSymbol then
            result_error "‘...’ used in an incorrect context."
          else
            let%success tmp :=
              if%success DDVAL e then
                ddfindVar e rho
              else
                findVar globals runs e rho in
            ifb tmp = R_UnboundValue then
              let%success e_name := PRINTNAME e in
              (** Originally, it was [EncodeChar] instead of [CHAR]. **)
              let%success e_str := CHAR e_name in
              result_error ("Object not found “" ++ e_str ++ "”.")
            else
              let%success ddval := DDVAL e in
              ifb tmp = R_MissingArg /\ ~ ddval then
                result_error "Argument is missing, with no default."
              else
                let%success tmp_type := TYPEOF tmp in
                ifb tmp_type = PromSxp then
                  read%prom _, tmp_prom := tmp in
                  let%success tmp :=
                    ifb prom_value tmp_prom = R_UnboundValue then
                      forcePromise tmp
                    else result_success (prom_value tmp_prom) in
                  set%named tmp := named_plural in
                  result_success tmp
                else
                  let%success tmp_type := TYPEOF tmp in
                  let%success tmp_named := NAMED tmp in
                  run%success
                    ifb tmp_type <> NilSxp /\ tmp_named = named_temporary then
                      set%named tmp := named_unique in
                      result_skip
                    else result_skip in
                  result_success tmp
        | PromSxp =>
          run%success
            read%prom _, e_prom := e in
            ifb prom_value e_prom = R_UnboundValue then
              run%success forcePromise e in
              result_skip
            else result_skip in
          read%prom _, e_prom := e in
          result_success (prom_value e_prom)
        | LangSxp =>
          read%list e_car, e_cdr, _ := e in
          let%success e_car_type := TYPEOF e_car in
          let%success op :=
            ifb e_car_type = SymSxp then
              let%success ecall :=
                get%state S in
                ifb context_callflag (R_GlobalContext S) = Ctxt_CCode then
                  result_success (context_call (R_GlobalContext S))
                else result_success e in
              findFun3 globals runs e_car rho ecall
            else runs_eval runs e_car rho in
          let%success op_type := TYPEOF op in
          match op_type with
          | SpecialSxp =>
            let%success f := PRIMFUN op in
            f e op e_cdr rho
          | BuiltinSxp =>
            let%success tmp := evalList e_cdr rho e 0 in
            let%success infos := PPINFO op in
            ifb PPinfo_kind infos = PP_FOREIGN then
              let%success cntxt :=
                begincontext globals Ctxt_Builtin e R_BaseEnv R_BaseEnv R_NilValue R_NilValue in
              let%success f := PRIMFUN op in
              let%success tmp := f e op tmp rho in
              run%success endcontext globals runs cntxt in
              result_success tmp
            else
              let%success f := PRIMFUN op in
              f e op tmp rho
          | CloSxp =>
            let%success tmp := promiseArgs e_cdr rho in
            applyClosure e op tmp rho R_NilValue
          | _ => result_error "Attempt to apply non-function."
          end
        | DotSxp => result_error "‘...’ used in an incorrect context"
        | _ => result_error "Type unimplemented in the R source code."
        end
  end.

Definition evalseq expr rho (forcelocal : bool) tmploc :=
  add%stack "evalseq" in
  if%success isNull expr then
    result_error "Invalid left side assignment."
  else if%success isSymbol expr then
    let%success nval :=
      if forcelocal then
        EnsureLocal globals runs expr rho
      else  (* now we are down to the target symbol *)
        read%env _, rho_env := rho in
        eval expr (env_enclos rho_env) in

    let%success nval :=
      if%success MAYBE_SHARED nval then
        shallow_duplicate globals runs nval
      else result_success nval in
    let%success r := CONS_NR globals nval expr in
    result_success r

  else if%success isLanguage globals expr then
    read%list expr_car, expr_cdr, _ := expr in
    read%list expr_cdr_car, expr_cdr_cdr, _ := expr_cdr in
    let%success val := runs_evalseq runs expr_cdr_car rho forcelocal tmploc in
    read%list val_car, _, _ := val in
    run%success R_SetVarLocValue globals runs tmploc val_car in
    let%success tmploc_sym := R_GetVarLocSymbol tmploc in
    let%success nexpr := LCONS globals tmploc_sym expr_cdr_cdr in
    let%success nexpr := LCONS globals expr_car nexpr in
    let%success nval := eval nexpr rho in
    let%success nval :=
      if%success MAYBE_REFERENCED nval then
        if%success MAYBE_SHARED nval then
          shallow_duplicate globals runs nval
        else
          read%list val_car, _, _ := val in
          if%success MAYBE_SHARED val_car then
            shallow_duplicate globals runs nval
          else result_success nval
      else result_success nval in
    let%success r := CONS_NR globals nval val in
    result_success r
  else result_error "Target of assignment expands to non-language object.".

Definition GET_BINDING_CELL (symbol rho : SEXP) : result SEXP :=
  add%stack "GET_BINDING_CELL" in
    ifb rho = R_BaseEnv \/ rho = R_BaseNamespace then
        result_success (R_NilValue : SEXP)
    else
        let%success loc := R_findVarLocInFrame globals runs rho symbol in
        result_success (if negb (R_VARLOC_IS_NULL loc) then loc else R_NilValue).
        
End Parameterised.

