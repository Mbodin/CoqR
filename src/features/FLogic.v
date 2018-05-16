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
Require Import Rcore.


Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition do_logic2 S (call op args env : SEXP)  :=
  add%stack "do_logic2" in
    let%success args_length := R_length globals runs S args using S in
    ifb args_length <> 2 then
        result_error S "operator requires 2 arguments"
    else
        read%list args_car, args_cdr, _ := args using S in
        let s1 := args_car in
        read%list args_cdr_car, _, _ := args_cdr using S in
        let s2 := args_cdr_car in
        let%success s1 := eval globals runs S s1 env using S in
        let%success s1_isNumber := isNumber globals runs S s1 using S in
        if negb s1_isNumber then
            result_error S "invalid type for first argument ‘x’."
        else
            let%success x1 := asLogical globals S s1 using S in
            let%success op_primval := PRIMVAL runs S op using S in
            let get_2nd S :=
              let%success s2 := eval globals runs S s2 env using S in
              let%success s2_isNumber := isNumber globals runs S s2 using S in
              if negb s2_isNumber then
                result_error S "invalid type for second argument ‘y’."
              else
                asLogical globals S s2 in
            let%success ans :=
            match Z.to_nat op_primval with
            (** && **)
            | 1 => ifb x1 = false then
                      result_success S (false : int)
                  else
                      let%success x2 := get_2nd S using S in
                      ifb x1 = NA_LOGICAL then
                        result_success S
                          (ifb x2 = NA_LOGICAL \/ x2 = true then NA_LOGICAL else x2)
                      else
                          result_success S x2
            (** || **)
            | 2 => ifb x1 = true then
                      result_success S (true : int)
                  else
                      let%success x2 := get_2nd S using S in
                      ifb x1 = NA_LOGICAL then
                        result_success S
                          (ifb x2 = NA_LOGICAL \/ x2 = false then NA_LOGICAL else x2)
                      else
                          result_success S x2
            | _ => result_impossible S "Switch without default: unknown boolean operator."
            end
            using S in
            result_success S (ScalarLogical globals ans).

End Parameters.
