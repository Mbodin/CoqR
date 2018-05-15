(** Core.CNames.
  The function names in this file correspond to the function names
  in the file main/names.c. **)

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
Require Import Conflicts.
Require Import CRinternals.
Require Import CMemory.
Require Import CDstruct.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.
Local Coercion int_to_double : Z >-> double.


Definition mkSymMarker S pname :=
  add%stack "mkSymMarker" in
  let (S, ans) := alloc_SExp S (make_SExpRec_sym R_NilValue pname NULL R_NilValue) in
  write%defined ans := make_SExpRec_sym R_NilValue pname ans R_NilValue using S in
  result_success S ans.

Definition install S name_ : result SEXP :=
  add%stack "install" in
  (** As said in the description of [InitNames] in Rinit.v,
    the hash table present in [R_SymbolTable] has not been
    formalised as such.
    Instead, it is represented as a single list, and not
    as [HSIZE] different lists.
    This approach is slower, but equivalent. **)
  fold%return
  along R_SymbolTable S
  as sym_car, _ do
    let%success str_sym := PRINTNAME S sym_car using S in
    let%success str_name_ := CHAR S str_sym using S in
    ifb name_ = str_name_ then
      result_rreturn S sym_car
    else result_rskip S using S, runs, globals in
  ifb name_ = ""%string then
    result_error S "Attempt to use zero-length variable name."
  else
    let (S, str) := mkChar globals S name_ in
    let%success sym := mkSYMSXP globals S str R_UnboundValue using S in
    let (S, SymbolTable) := CONS globals S sym (R_SymbolTable S) in
    let S := update_R_SymbolTable S SymbolTable in
    result_success S sym.

(** We here choose to model [installChar] as its specification
  given by the associated comment in the C source file. **)
Definition installChar S charSXP :=
  add%stack "installChar" in
  let%success str := CHAR S charSXP using S in
  install S str.

End Parameterised.

