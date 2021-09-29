(** Features.FLogic.
  The function names of this file correspond to the function names
  in the file main/logic.c. **)

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

Definition do_logic (call op args env : SEXP) : result_SEXP :=
  add%stack "do_logic" in
  read%list args_car, args_cdr, _ := args in
  read%list args_cdr_car, _, _ := args_cdr in
  let arg1 := args_car in
  let%success arg1_attrib := ATTRIB arg1 in
  let attr1 := decide (arg1_attrib <> R_NilValue) in
  let%success args_cdr_car_attrib := ATTRIB args_cdr_car in

  run%exit
  ifb attr1 \/ args_cdr_car_attrib <> R_NilValue then
   if%defined ans := DispatchGroup globals runs "Ops" call op args env then
     result_rreturn ans
   else
     result_rskip

  else result_rskip in
  run%success Rf_checkArityCall globals runs op args call in

  ifb args_cdr = R_NilValue then   (* one argument <==> !(arg1) *)
    let%success arg1_isScalar := IS_SCALAR arg1 LglSxp in
    ifb not attr1 /\ arg1_isScalar then
        read%Logical v := arg1 at 0 in
        result_success (ScalarLogical globals (ifb v = NA_LOGICAL then v else
                          ifb v = 0 then 1 else 0))
    else
      lunary globals runs call op arg1
  else (* two arguments *)
    lbinary globals runs call op args.

Definition do_logic2 (call op args env : SEXP)  :=
  add%stack "do_logic2" in
  let%success args_length := R_length globals runs args in
  ifb args_length <> 2 then
    result_error "operator requires 2 arguments"
  else
    read%list args_car, args_cdr, _ := args in
    let s1 := args_car in
    read%list args_cdr_car, _, _ := args_cdr in
    let s2 := args_cdr_car in
    let%success s1 := eval globals runs s1 env in
    let%success s1_isNumber := isNumber globals runs s1 in
    if negb s1_isNumber then
      result_error "invalid type for first argument ‘x’."
    else
      let%success x1 := asLogical globals s1 in
      let%success op_primval := PRIMVAL runs op in
      let get_2nd :=
        let%success s2 := eval globals runs s2 env in
        let%success s2_isNumber := isNumber globals runs s2 in
        if negb s2_isNumber then
          result_error "invalid type for second argument ‘y’."
        else
          asLogical globals s2 in
      let%success ans :=
      match Z.to_nat op_primval with
      (** && **)
      | 1 => ifb x1 = false then
              result_success (false : int)
             else
              let%success x2 := get_2nd in
              ifb x1 = NA_LOGICAL then
                result_success
                  (ifb x2 = NA_LOGICAL \/ x2 = true then NA_LOGICAL else x2)
              else
                result_success x2
      (** || **)
      | 2 => ifb x1 = true then
               result_success (true : int)
             else
              let%success x2 := get_2nd in
              ifb x1 = NA_LOGICAL then
                result_success
                  (ifb x2 = NA_LOGICAL \/ x2 = false then NA_LOGICAL else x2)
              else
                result_success x2
      | _ => result_impossible "Switch without default: unknown boolean operator."
      end
      in
      result_success (ScalarLogical globals ans).

End Parameters.
