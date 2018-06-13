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
  set%type tmp := LangSxp using S in
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
    set%named val := named_plural using S in
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
      if match context_jumptarget cntxt with
         | None => true
         | Some _ => false
         end then
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

Definition applyClosure S (call op arglist rho suppliedvars : SEXP) : result SEXP :=
  add%stack "applyClosure" in
  ifb rho = NULL then
    result_error S "‘rho’ can’t be C NULL."
  else
    let%success rho_env := isEnvironment S rho using S in
    if negb rho_env then
      result_error S "‘rho’ must be an environment."
    else
      read%clo op_, op_clo := op using S in
      let formals := clo_formals op_clo in
      let savedrho := clo_env op_clo in
      let%success actuals := matchArgs_RC globals runs S formals arglist call using S in
      let%success newrho := NewEnvironment globals runs S formals actuals savedrho using S in
      fold%success a := actuals
      along formals
      as f_car, f_tag do
        read%list a_car, a_cdr, _ := a using S in
        run%success
          ifb a_car = R_MissingArg /\ f_car <> R_MissingArg then
            let%success newprom := mkPromise globals S f_car newrho using S in
            set%car a := newprom using S in
            run%success SET_MISSING S a 2 ltac:(nbits_ok) using S in
            result_skip S
          else result_skip S using S in
        result_success S a_cdr using S, runs, globals in
      run%success
        ifb suppliedvars <> R_NilValue then
           addMissingVarsToNewEnv globals runs S newrho suppliedvars
         else result_skip S using S in
      if%success R_envHasNoSpecialSymbols globals runs S newrho using S then
        SET_NO_SPECIAL_SYMBOLS S newrho in
      let%success val :=
        R_execClosure S call newrho
          (ifb context_callflag (R_GlobalContext S) = Ctxt_Generic then
             context_sysparent (R_GlobalContext S)
           else rho)
          rho arglist op using S in
      result_success S val.

Definition promiseArgs S (el rho : SEXP) : result SEXP :=
  add%stack "promiseArgs" in
  let (S, tail) := CONS globals S R_NilValue R_NilValue in
  fold%success (ans, tail) := (tail, tail)
  along el
  as el_car, el_tag do
    ifb el_car = R_DotsSymbol then
      let%success h := findVar globals runs S el_car rho using S in
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
      let%success h := findVar globals runs S el_car rho using S in
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
      let%success h := findVar globals runs S el_car rho using S in
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
        let%success el_car_mi := R_isMissing globals runs S el_car rho using S in
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
          let%success h := findVar globals runs S R_DotsSymbol rho using S in
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
    set%named e := named_plural using S in
    result_success S e
  | _ =>
    ifb rho = NULL then
      result_error S "‘rho’ cannot be C NULL."
    else
      let%success rho_env := isEnvironment S rho using S in
      if negb rho_env then
        result_error S "‘rho’ must be an environment."
      else
        let%success e_type := TYPEOF S e using S in
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
                findVar globals runs S e rho using S in
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
                  set%named tmp := named_plural using S in
                  result_success S tmp
                else
                  let%success tmp_type := TYPEOF S tmp using S in
                  let%success tmp_named := NAMED S tmp using S in
                  run%success
                    ifb tmp_type <> NilSxp /\ tmp_named = named_temporary then
                      set%named tmp := named_unique using S in
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
              findFun3 globals runs S e_car rho ecall
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
        EnsureLocal globals runs S expr rho
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
    run%success R_SetVarLocValue globals runs S tmploc val_car using S in
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

Definition GET_BINDING_CELL S (symbol rho : SEXP) : result SEXP :=
  add%stack "GET_BINDING_CELL" in
    ifb rho = R_BaseEnv \/ rho = R_BaseNamespace then
        result_success S (R_NilValue : SEXP)
    else
        let%success loc := R_findVarLocInFrame globals runs S rho symbol using S in
        result_success S (if negb (R_VARLOC_IS_NULL loc) then loc else R_NilValue).
        
End Parameterised.

