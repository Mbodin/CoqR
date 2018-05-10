(** Core.Conflicts.
  Due to some circular dependencies between C files
  (which is accepted in C, but not in Coq),
  not all functions could have been put in its specific file
  corresponding to how functions where ordered in the C source of R.
  This file thus regroups some functions that had to be put apart
  for the Coq compilation. **)

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
Require Import CRinternals.
Require Import CRinlinedfuns.
Require Import CMemory.
Require Import CDuplicate.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

(** ** Rinlinedfuns.c **)

(** The function names of this section correspond to the function names
  in the file include/Rinlinedfuns.c. **)

Definition R_FixupRHS S x y :=
  add%stack "R_FixupRHS" in
  let%success y_named := NAMED S y using S in
  ifb y <> R_NilValue /\ y_named <> named_temporary then
    if%success R_cycle_detected globals runs S x y using S then
      duplicate globals runs S y
    else
      map%pointer y with set_named_plural using S in
      result_success S y
  else result_success S y.

Definition isVectorizable S (s : SEXP) :=
  add%stack "isVectorizable" in
  ifb s = R_NilValue then
    result_success S true
  else if%success isNewList globals S s using S then
    let%success n := XLENGTH S s using S in
    do%exit
    for i from 0 to n - 1 do
      let%success s_i := VECTOR_ELT S s i using S in
      let%success s_i_iv := isVector S s_i using S in
      let%success s_i_len := LENGTH globals S s_i using S in
      ifb ~ s_i_iv \/ s_i_len > 1 then
        result_rreturn S false
      else result_rskip S using S in
    result_success S true
  else if%success isList globals S s using S then
    fold%return
    along s
    as s_car, _ do
      let%success s_car_iv := isVector S s_car using S in
      let%success s_car_len := LENGTH globals S s_car using S in
      ifb ~ s_car_iv \/ s_car_len > 1 then
        result_rreturn S false
      else result_rskip S using S, runs, globals in
    result_success S true
  else result_success S false.

Definition isArray S s :=
  add%stack "isArray" in
  if%success isVector S s using S then
    let%success t := runs_getAttrib runs S s R_DimSymbol using S in
    let%success t_type := TYPEOF S t using S in
    let%success t_len := LENGTH globals S t using S in
    ifb t_type = IntSxp /\ t_len > 0 then
      result_success S true
    else result_success S false
  else result_success S false.

Definition isTs S s :=
  add%stack "isTs" in
  if%success isVector S s using S then
    let%success a := runs_getAttrib runs S s R_TspSymbol using S in
    result_success S (decide (a <> R_NilValue))
  else result_success S false.

Definition conformable S x y :=
  add%stack "conformable" in
  let%success x := runs_getAttrib runs S x R_DimSymbol using S in
  let%success y := runs_getAttrib runs S y R_DimSymbol using S in
  let%success x_len := R_length globals runs S x using S in
  let%success y_len := R_length globals runs S y using S in
  ifb x_len <> y_len then
    result_success S false
  else
    let n := x_len in
    do%exit
    for i from 0 to n - 1 do
      read%Integer x_i := x at i using S in
      read%Integer y_i := y at i using S in
      ifb x_i <> y_i then
        result_rreturn S false
      else result_rskip S using S in
    result_success S true.

Definition isValidString S x :=
  add%stack "isValidString" in
  let%success x_type := TYPEOF S x using S in
  let%success x_len := LENGTH globals S x using S in
  let%success x_0 := STRING_ELT S x 0 using S in
  let%success x_0_type := TYPEOF S x_0 using S in
  result_success S (decide (x_type = StrSxp /\ x_len > 0 /\ x_0_type <> NilSxp)).


(** ** util.c **)

(** The function names of this section correspond to the function names
  in the file main/util.c. **)

Definition type2rstr S (t : SExpType) :=
  add%stack "type2rstr" in
  let res := Type2Table_rstrName (ArrayList.read (global_Type2Table globals) t) in
  ifb res <> NULL then result_success S res
  else result_success S (R_NilValue : SEXP).

Definition nthcdr S s n :=
  add%stack "nthcdr" in
  let%success s_li := isList globals S s using S in
  let%success s_la := isLanguage globals S s using S in
  let%success s_fr := isFrame globals runs S s using S in
  let%success s_t := TYPEOF S s using S in
  ifb s_li \/ s_la \/ s_fr \/ s_t = DotSxp then
    do%success (s, n) := (s, n)
    whileb n > 0 do
      ifb s = R_NilValue then
        result_error S "List too short."
      else
        read%list _, s_cdr, _ := s using S in
        result_success S (s, n - 1) using S, runs in
    result_success S s
  else result_error S "No CDR.".

(** ** envir.c **)

(** The function names of this section correspond to the function names
  in the file main/envir.c. **)

(** The function [mkChar] from the R source code performs a lot of things.
  It deals with encoding, for embedded zero-characters, as well as avoid
  allocated twice the same string, by looking through the already
  allocated strings. We do none of the above. **)
(* FIXME: What is the difference between [intCHARSXP] and [CHARSXP]? *)
Definition mkChar S (str : string) : state * SEXP :=
  (* Note that values are not cached, in contrary to the original code. *)
  alloc_vector_char globals S (ArrayList.from_list (string_to_list str)).

Definition mkString S (str : string) : state * SEXP :=
  let (S, c) := mkChar S str in
  alloc_vector_str globals S (ArrayList.from_list [c]).
Definition BCCONSTS S e :=
  add%stack "BCCONSTS" in
  BCODE_CONSTS S e.


(** ** eval.c **)

(** The function names of this section correspond to the function names
  in the file main/eval.c. **)

Definition bytecodeExpr S e :=
  add%stack "bytecodeExpr" in
  if%success isByteCode S e using S then
    let%success e := BCCONSTS S e using S in
    let%success e_len := LENGTH globals S e using S in
    ifb e_len > 0 then
      VECTOR_ELT S e 0
    else result_success S (R_NilValue : SEXP)
  else result_success S e.

Definition R_PromiseExpr S p :=
  add%stack "R_PromiseExpr" in
  read%prom _, p_prom := p using S in
  bytecodeExpr S (prom_expr p_prom).

Definition PREXPR S e :=
  add%stack "PREXPR" in
  R_PromiseExpr S e.

End Parameterised.

