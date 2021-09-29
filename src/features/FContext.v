(** Features.FContext.
  The function names of this file correspond to the function names
  in the file main/context.c. **)

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
From CoqR.features Require Import FUtil.

Section Parameters.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

Fixpoint do_parentframe_loop cptr t (n : int) :=
  match context_nextcontext cptr with
  | None => (R_GlobalEnv : SEXP)
  | Some cptr_nextcontext =>
    ifb context_type_mask (context_callflag cptr) Ctxt_Function then
      ifb context_cloenv cptr = t then
        ifb n = 1 then context_sysparent cptr
        else do_parentframe_loop cptr_nextcontext (context_sysparent cptr) (n - 1)
      else do_parentframe_loop cptr_nextcontext t n
    else do_parentframe_loop cptr_nextcontext t n
  end.

Definition do_parentframe (call op args rho : SEXP) : result_SEXP :=
  add%stack "do_parentframe" in
  run%success Rf_checkArityCall globals runs op args call in
  read%list args_car, _, _ := args in
  let t := args_car in
  let%success n := asInteger globals t in
  ifb n = NA_INTEGER \/ n < 1 then
    result_error "Invalid ‘n’ value."
  else
    read%state cptr := R_GlobalContext in
    let t := context_sysparent cptr in
    result_success (do_parentframe_loop cptr t n).

End Parameters.

