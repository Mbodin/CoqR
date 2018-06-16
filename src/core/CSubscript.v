(** Core.CSubscript.
  The function names in this file correspond to the function names
  in the file main/subscript.c. **)

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
Require Import CRinlinedfuns.
Require Import CAttrib.
Require Import CDuplicate.


Section Parameterised.

(** Global Variables **)

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.



Definition makeSubscript S (x s call : SEXP)  :=
  add%stack "makeSubscript" in
    let%success x_isVector := isVector S x using S in
    let%success x_isList := isList globals S x using S in
    let%success x_isLanguage := isLanguage globals S x using S in
    ifb ~ (x_isVector \/ x_isList \/ x_isLanguage) then
        result_error S "subscripting on non-vector"
    else
    
    let%success nx := xlength globals runs S x using S in  


    let%success s_isScalar := IS_SCALAR S s IntSxp using S in
    run%exit
    (* special case for simple indices -- does not duplicate *)
    if s_isScalar then
        let%success i := SCALAR_IVAL S s using S in
        ifb 0%Z < i /\ i <= nx then
            result_rreturn S (s, 0)
        else
            result_rskip S
    else
        let%success s_isScalar := IS_SCALAR S s RealSxp using S in
        if s_isScalar then
            let%success di := SCALAR_DVAL S s using S in
            ifb 1%Z <= (Double.double_to_int_zero di) /\ di <= nx then
                result_rreturn S (s, 0)
        else
            result_rskip S
        else result_rskip S
    using S in

    let%success ns := xlength globals runs S s using S in    
    let ans := (R_NilValue : SEXP) in
    let%success s_type := TYPEOF S s using S in
    let%success (ans, stretch) :=
    match s_type with
    | NilSxp =>
      let%success ans := allocVector globals S IntSxp 0 using S in
      result_success S (ans, 0)
    | LglSxp => unimplemented_function "logicalSubscript"  
    | IntSxp => unimplemented_function "integerSubscript"
    | RealSxp => unimplemented_function "realSubscript"
    | StrSxp =>
      let%success names := getAttrib globals runs S x R_NamesSymbol using S in
      unimplemented_function "stringSubscript"
    | SymSxp =>
      ifb s = R_MissingArg then
          unimplemented_function "nullSubscript"
      else
          result_success S (ans, 0)
    | _ => result_error S "invalid subscript type"
    end
    using S in
    result_success S (ans, stretch).


End Parameterised.