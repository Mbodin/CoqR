(** Features.FComplex.
  The function names of this file correspond to the function names
  in the file main/complex.c. **)

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
Require Import FUtil.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition complex_binary (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  unimplemented_function "complex_binary".

Definition complex_unary (code : int) s1 :=
  add%stack "complex_unary" in
  ifb code = PLUSOP then
    result_success s1
  else ifb code = MINUSOP then
    let%success ans :=
      if%success NO_REFERENCES s1 then
        result_success s1
      else duplicate globals runs s1 in
    read%VectorComplex s1_ := s1 in
    let px := VecSxp_data s1_ in
    let pa := ArrayListExtra.map (fun x =>
      make_Rcomplex (Double.opp (Rcomplex_r x)) (Double.opp (Rcomplex_i x))) px in
    write%VectorComplex ans := pa in
    result_success ans
    else result_error "Invalid unary operator.".

Definition complex_math1 (S : state) (call op args env : SEXP) : result SEXP :=
  unimplemented_function "complex_math1".

End Parameters.

