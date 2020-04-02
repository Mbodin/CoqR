(** Core.CContext.
  The function names in this file correspond to the function names
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
Require Import Loops.


Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


(** Instead of updating a context given as its first argument, it returns it. **)
Definition begincontext flags syscall env sysp promargs callfun :=
  add%stack "begincontext" in
  read%state GlobalContext := R_GlobalContext in
  let cptr := {|
     context_nextcontext := Some GlobalContext ;
     context_cjmpbuf := 1 + context_cjmpbuf GlobalContext ;
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
  map%state state_with_context cptr in
  result_success cptr.

Fixpoint first_jump_target_loop c cptr mask :=
  (** In the original program, the pointers [c] and [cptr] are directly compared.
    We here used the unique [cjmpbuf] to model this comparison. **)
  ifb context_cjmpbuf c = context_cjmpbuf cptr then
    result_success cptr
  else
    ifb (context_cloenv c <> R_NilValue /\ context_conexit c <> R_NilValue)
        \/ context_callflag c = Ctxt_Unwind then
      let c := context_with_jumptarget c (Some cptr) in
      let c := context_with_jumpmask c mask in
      result_success c
    else
      match context_nextcontext c with
      | None => result_success cptr
      | Some c => first_jump_target_loop c cptr mask
      end.

Definition first_jump_target cptr mask :=
  add%stack "first_jump_target" in
  read%state GlobalContext := R_GlobalContext in
  first_jump_target_loop GlobalContext cptr mask.

Fixpoint R_run_onexits_loop c cptr :=
  (** In the original program, the pointers [c] and [cptr] are directly compared.
    We here used the unique [cjmpbuf] to model this comparison. **)
  ifb context_cjmpbuf c = context_cjmpbuf cptr then
    result_skip
  else
    run%success
      ifb context_cloenv c <> R_NilValue /\ context_conexit c <> R_NilValue then
        let s := context_conexit c in
        read%state savecontext := R_ExitContext in
        let c := context_with_conexit c R_NilValue in
        let c := context_with_returnValue c NULL in
        map%state update_R_ExitContext (Some c) in
        fold%success
        along s
        as _, _, s_list do
          let c := context_with_conexit c (list_cdrval s_list) in
          map%state state_with_context c in
          run%success
            runs_eval runs (list_carval s_list) (context_cloenv cptr) in
            result_skip using runs in
        map%state update_R_ExitContext savecontext in
        result_skip
      else result_skip in
    run%success
      read%state ExitContext := R_ExitContext in
      if match ExitContext with
         | None => false
         | Some ce => decide (context_cjmpbuf ce = context_cjmpbuf c)
         end then
        map%state update_R_ExitContext None in
        result_skip
      else result_skip in
    match context_nextcontext c with
    | None => result_impossible "Bad target context."
    | Some c => R_run_onexits_loop c cptr
    end.

Definition R_run_onexits cptr :=
  add%stack "R_run_onexits" in
  read%state GlobalContext := R_GlobalContext in
  R_run_onexits_loop GlobalContext cptr.

Definition R_restore_globals (cptr : context) :=
  add%stack "R_restore_globals" in
  result_skip.

Definition R_jumpctxt A targetcptr mask val : result A :=
  add%stack "R_jumpctxt" in
  let%success cptr := first_jump_target targetcptr mask in
  run%success R_run_onexits cptr in
  map%state update_R_ReturnedValue val in
  map%state state_with_context cptr in
  run%success
    read%state GlobalContext := R_GlobalContext in
    R_restore_globals GlobalContext in
  result_longjump (context_cjmpbuf cptr) mask.
Arguments R_jumpctxt [A].

Definition endcontext cptr :=
  add%stack "endcontext" in
  let jmptarget := context_jumptarget cptr in
  run%success
    ifb context_cloenv cptr <> R_NilValue /\ context_conexit cptr <> R_NilValue then
      let s := context_conexit cptr in
      read%state savecontext := R_ExitContext in
      let cptr := context_with_conexit cptr R_NilValue in
      let cptr := context_with_jumptarget cptr None in
      map%state update_R_ExitContext (Some cptr) in
      fold%success
      along s
      as _, _, s_list do
        let cptr := context_with_conexit cptr (list_cdrval s_list) in
        map%state state_with_context cptr in
        run%success
          runs_eval runs (list_carval s_list) (context_cloenv cptr) in
        result_skip using runs in
      map%state update_R_ExitContext savecontext in
      result_skip
    else result_skip in
  run%success
    read%state ExitContext := R_ExitContext in
    if match ExitContext with
       | None => false
       | Some ce => decide (context_cjmpbuf ce = context_cjmpbuf cptr)
       end then
      map%state update_R_ExitContext None in
      result_skip
    else result_skip in
  run%success
    match jmptarget with
    | None => result_skip
    | Some jmptarget =>
      read%state ReturnedValue := R_ReturnedValue in
      R_jumpctxt jmptarget (context_jumpmask cptr) ReturnedValue
    end in
  let%defined c := context_nextcontext cptr in
  map%state state_with_context c in
  result_skip.

Fixpoint findcontext_loop A cptr env mask mask_against val err : result A :=
  ifb context_type_mask (context_callflag cptr) mask_against /\ context_cloenv cptr = env then
    R_jumpctxt cptr mask val
  else
    let error := result_error err in
    match context_nextcontext cptr with
    | None => error
    | Some cptr =>
      ifb context_callflag cptr = Ctxt_TopLevel then error
      else findcontext_loop _ cptr env mask mask_against val err
    end.
Arguments findcontext_loop [A].

Definition findcontext A mask env val : result A :=
  add%stack "findcontext" in
  read%state GlobalContext := R_GlobalContext in
  ifb context_type_mask Ctxt_Loop mask then
    findcontext_loop GlobalContext env mask Ctxt_Loop val "No loop for break/next, jumping to top level."
  else
    findcontext_loop GlobalContext env mask mask val "No function to return from, jumping to top level.".
Arguments findcontext [A].

End Parameterised.

