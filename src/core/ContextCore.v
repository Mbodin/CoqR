(** ** context.c **)

(** The function names of this section correspond to the function names
  in the file main/context.c. **)

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
Require Import Loops.


Section Parameterised.

(** * Global Variables **)

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition get_R_FunTab S :=
  add%stack "get_R_FunTab" in
  match runs_R_FunTab runs with
  | None => result_bottom S
  | Some t => result_success S t
  end.

Definition read_R_FunTab S n :=
  add%stack "read_R_FunTab" in
  let%success t := get_R_FunTab S using S in
  ifb n >= ArrayList.length t then
    result_impossible S "Out of bounds."
  else
    let c := ArrayList.read t n in
    result_success S c.


Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

(* We may want to make [INT_MIN] and [INT_MAX] a parameter of the formalisation,
  as it depends on the C compiler options. *)
Definition INT_MIN : int := - 2 ^ 31.
Definition INT_MAX : int := 2 ^ 31 - 1.

Definition R_INT_MAX := INT_MAX.
Definition R_INT_MIN := INT_MIN.

Definition R_NaInt := INT_MIN.
Definition NA_INTEGER := R_NaInt.
Definition NA_LOGICAL := R_NaInt.
Definition R_PosInf : double := Double.posInf.
Definition R_NegInf : double := Double.negInf.
Definition R_NaN : double := Double.NaN.
Definition R_NaReal : double := Double.NaN1954.
Definition NA_REAL : double := R_NaReal.

Definition R_NaString := NA_STRING.

Definition R_XLEN_T_MAX : int := Zpos 4503599627370496.

Definition PLUSOP := 1.
Definition MINUSOP := 2.
Definition TIMESOP := 3.
Definition DIVOP := 4.
Definition POWOP := 5.
Definition MODOP := 6.
Definition IDIVOP := 7.

Definition EQOP := 1.
Definition NEOP := 2.
Definition LTOP := 3.
Definition LEOP := 4.
Definition GEOP := 5.
Definition GTOP := 6.

(** End of Global Variables **)

(** Instead of updating a context given as its first argument, it returns it. **)
Definition begincontext S flags syscall env sysp promargs callfun :=
  add%stack "begincontext" in
  let cptr := {|
     context_nextcontext := Some (R_GlobalContext S) ;
     context_cjmpbuf := 1 + context_cjmpbuf (R_GlobalContext S) ;
     context_callflag := flags ;
     context_promargs := promargs ;
     context_callfun := callfun ;
     context_sysparent := sysp ;
     context_call := syscall ;
     context_cloenv := env ;
     context_conexit := R_NilValue ;
     context_returnValue := NULL ;
     context_jumptarget := None ;
     context_jumpmask := empty_context_type
   |} in
  let S := state_with_context S cptr in
  result_success S cptr.

Fixpoint first_jump_target_loop S c cptr mask :=
  ifb c = cptr then
    result_success S cptr
  else
    ifb context_cloenv c <> R_NilValue /\ context_conexit c <> R_NilValue then
      let c := context_with_jumptarget c (Some cptr) in
      let c := context_with_jumpmask c mask in
      result_success S c
    else
      match context_nextcontext c with
      | None => result_success S cptr
      | Some c => first_jump_target_loop S c cptr mask
      end.

Definition first_jump_target S cptr mask :=
  add%stack "first_jump_target" in
  first_jump_target_loop S (R_GlobalContext S) cptr mask.

Fixpoint R_run_onexits_loop S c cptr :=
  ifb c = cptr then
    result_skip S
  else
    run%success
      ifb context_cloenv c <> R_NilValue /\ context_conexit c <> R_NilValue then
        let s := context_conexit c in
        let savecontext := R_ExitContext S in
        let c := context_with_conexit c R_NilValue in
        let c := context_with_returnValue c NULL in
        let S := update_R_ExitContext S (Some c) in
        fold%success
        along s
        as _, _, s_list do
          let c := context_with_conexit c (list_cdrval s_list) in
          let S := state_with_context S c in
          run%success
            runs_eval runs S (list_carval s_list) (context_cloenv cptr) using S in
            result_skip S using S, runs, globals in
        let S := update_R_ExitContext S savecontext in
        result_skip S
      else result_skip S using S in
    run%success
      ifb R_ExitContext S = Some c then
        let S := update_R_ExitContext S None in
        result_skip S
      else result_skip S using S in
    match context_nextcontext c with
    | None => result_impossible S "Bad target context."
    | Some c => R_run_onexits_loop S c cptr
    end.

Definition R_run_onexits S cptr :=
  add%stack "R_run_onexits" in
  R_run_onexits_loop S (R_GlobalContext S) cptr.

Definition R_restore_globals S (cptr : context) :=
  add%stack "R_restore_globals" in
  result_skip S.

Definition R_jumpctxt A S targetcptr mask val : result A :=
  add%stack "R_jumpctxt" in
  let%success cptr := first_jump_target S targetcptr mask using S in
  run%success R_run_onexits S cptr using S in
  let S := update_R_ReturnedValue S val in
  let S := state_with_context S cptr in
  run%success R_restore_globals S (R_GlobalContext S) using S in
  result_longjump S (context_cjmpbuf cptr) mask.
Arguments R_jumpctxt [A].

Definition endcontext S cptr :=
  add%stack "endcontext" in
  let jmptarget := context_jumptarget cptr in
  run%success
    ifb context_cloenv cptr <> R_NilValue /\ context_conexit cptr <> R_NilValue then
      let s := context_conexit cptr in
      let savecontext := R_ExitContext S in
      let cptr := context_with_conexit cptr R_NilValue in
      let cptr := context_with_jumptarget cptr None in
      let S := update_R_ExitContext S (Some cptr) in
      fold%success
      along s
      as _, _, s_list do
        let cptr := context_with_conexit cptr (list_cdrval s_list) in
        let S := state_with_context S cptr in
        run%success
          runs_eval runs S (list_carval s_list) (context_cloenv cptr) using S in
        result_skip S using S, runs, globals in
      let S := update_R_ExitContext S savecontext in
      result_skip S
    else result_skip S using S in
  run%success
    ifb R_ExitContext S = Some cptr then
      let S := update_R_ExitContext S None in
      result_skip S
    else result_skip S using S in
  run%success
    match jmptarget with
    | None => result_skip S
    | Some jmptarget =>
      R_jumpctxt S jmptarget (context_jumpmask cptr) (R_ReturnedValue S)
    end using S in
  let%defined c := context_nextcontext cptr using S in
  let S := state_with_context S c in
  result_skip S.

Fixpoint findcontext_loop A S cptr env mask mask_against val err : result A :=
  ifb context_type_mask (context_callflag cptr) mask_against /\ context_cloenv cptr = env then
    R_jumpctxt S cptr mask val
  else
    let error S := result_error S err in
    match context_nextcontext cptr with
    | None => error S
    | Some cptr =>
      ifb context_callflag cptr = Ctxt_TopLevel then error S
      else findcontext_loop _ S cptr env mask mask_against val err
    end.
Arguments findcontext_loop [A].

Definition findcontext A S mask env val : result A :=
  add%stack "findcontext" in
  ifb context_type_mask Ctxt_Loop mask then
    findcontext_loop S (R_GlobalContext S) env mask Ctxt_Loop val "No loop for break/next, jumping to top level."
  else
    findcontext_loop S (R_GlobalContext S) env mask mask val "No function to return from, jumping to top level.".
Arguments findcontext [A].

End Parameterised.
