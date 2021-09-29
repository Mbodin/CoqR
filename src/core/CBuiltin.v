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
From Lib Require Import Double.
From CoqR Require Import Loops.
From CoqR.core Require Import CRinternals CMemory CRinlinedfuns CRmath.
From CoqR.core Require Import CArithmetic CCoerce.

Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.
Local Coercion int_to_double : Z >-> double.


Definition asVecSize (x : _SEXP) :=
  add%stack "asVecSize" in
  let%success x_isVectorAtomic := isVectorAtomic x in
  let%success x_LENGTH := LENGTH x in
  ifb x_isVectorAtomic /\ x_LENGTH >= 1 then
    let%success x_type := TYPEOF x in
    match x_type with
    | IntSxp => read%Integer res := x at 0 in
                ifb res = NA_INTEGER then
                  result_error "vector size cannot be NA"
                else
                  result_success res
    | RealSxp => read%Real d := x at 0 in
                if ISNAN d then
                  result_error "vector size cannot be NA/NaN"
                else if negb (R_FINITE d) then
                  result_error "vector size cannot be infinite"
                else ifb d > R_XLEN_T_MAX then
                  result_error "vector size specified is too large"
                else result_success (Double.double_to_int_zero d)
     | StrSxp => let%success d := asReal x in
                 if ISNAN d then
                   result_error "vector size cannot be NA/NaN"
                 else if negb (R_FINITE d) then
                   result_error "vector size cannot be infinite"
                 else ifb d > R_XLEN_T_MAX then
                   result_error "vector size specified is too large"
                 else result_success (Double.double_to_int_zero d)
     | _ => result_error "invalid type for argument"
     end
  else
    result_error "-999 code status".

Definition R_IsImportsEnv env : result_bool :=
  add%stack "R_IsImportsEnv" in
  let%success env_null := isNull env in
  let%success env_env := isEnvironment env in
  ifb env_null \/ ~ env_env then
    result_success false
  else
    read%env _, env_env := env in
    ifc env_enclos env_env '== R_BaseNamespace then
      result_success false
    else
      let%success name := runs_getAttrib runs env R_NameSymbol in
      let%success name_str := isString name in
      let%success name_len := LENGTH name in
      ifb ~ name_str \/ name_len <> 1 then
        result_success false
      else
        let imports_prefix := "imports:"%string in
        let%success name_0 := STRING_ELT name 0 in
        let%success name_string := CHAR name_0 in
        ifb String.substring 0 (String.length imports_prefix) name_string = imports_prefix then
          result_success true
        else result_success false.

End Parameterised.

