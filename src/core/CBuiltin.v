(** Core.CBuiltin.
  The function names in this file correspond to the macro names
  in the file main/builtin.c. **)

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
Require Import CRmath.
Require Import CArithmetic.
Require Import CCoerce.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.
Local Coercion int_to_double : Z >-> double.


Definition asVecSize S (x : SEXP)  :=
  add%stack "asVecSize" in
    let%success x_isVectorAtomic := isVectorAtomic S x using S in
    let%success x_LENGTH := LENGTH globals S x using S in
    ifb x_isVectorAtomic /\ x_LENGTH >= 1 then
        let%success x_type := TYPEOF S x using S in
        match x_type with
        | IntSxp => read%Integer res := x at 0 using S in
                   ifb res = NA_INTEGER then
                       result_error S "vector size cannot be NA"
                   else
                       result_success S res
        | RealSxp => read%Real d := x at 0 using S in
                    if ISNAN d then
                        result_error S "vector size cannot be NA/NaN"
                    else if negb (R_FINITE d) then
                        result_error S "vector size cannot be infinite"
                    else ifb d > R_XLEN_T_MAX then
                        result_error S "vector size specified is too large"
                    else result_success S (Double.double_to_int_zero d)
         | StrSxp => let%success d := asReal globals S x using S in
                     if ISNAN d then
                         result_error S "vector size cannot be NA/NaN"
                     else if negb (R_FINITE d) then
                         result_error S "vector size cannot be infinite"
                     else ifb d > R_XLEN_T_MAX then
                         result_error S "vector size specified is too large"
                     else result_success S (Double.double_to_int_zero d)
         | _ => result_error S "invalid type for argument"
         end                   
    else
        result_error S "-999 code status".

Definition R_IsImportsEnv S env :=
  add%stack "R_IsImportsEnv" in
  let%success env_null := isNull S env using S in
  let%success env_env := isEnvironment S env using S in
  ifb env_null \/ ~ env_env then
    result_success S false
  else
    read%env _, env_env := env using S in
    ifb env_enclos env_env = R_BaseNamespace then
      result_success S false
    else
      let%success name := runs_getAttrib runs S env R_NameSymbol using S in
      let%success name_str := isString S name using S in
      let%success name_len := LENGTH globals S name using S in
      ifb ~ name_str \/ name_len <> 1 then
        result_success S false
      else
        let imports_prefix := "imports:"%string in
        let%success name_0 := STRING_ELT S name 0 using S in
        let%success name_string := CHAR S name_0 using S in
        ifb String.substring 0 (String.length imports_prefix) name_string = imports_prefix then
          result_success S true
        else result_success S false.

End Parameterised.

