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
From CoqR Require Import Loops.
From CoqR.core Require Import CRinternals CRinlinedfuns CMemory CDuplicate.

Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.
Local Coercion int_to_double : Z >-> double.

(** ** Rinlinedfuns.c **)

(** The function names of this section correspond to the function names
  in the file include/Rinlinedfuns.c. **)

Definition R_FixupRHS x y : result_SEXP :=
  add%stack "R_FixupRHS" in
  let%success y_named := NAMED y in
  ifc (y '!= R_NilValue) '&& 'decide (y_named <> named_temporary) then
    if%success R_cycle_detected runs x y then
      duplicate runs y
    else
      set%named y := named_plural in
      (y : result_SEXP)
  else (y : result_SEXP).

Definition isVectorizable (s : _SEXP) : result_bool :=
  add%stack "isVectorizable" in
  ifc s '== R_NilValue then
    result_success true
  else if%success isNewList s then
    let%success n := XLENGTH s in
    do%exit
    for i from 0 to n - 1 do
      let%success s_i := VECTOR_ELT s i in
      let%success s_i_iv := isVector s_i in
      let%success s_i_len := LENGTH s_i in
      ifb ~ s_i_iv \/ s_i_len > 1 then
        result_rreturn false
      else result_rskip in
    result_success true
  else if%success isList s then
    fold%return
    along s
    as s_car, _ do
      let%success s_car_iv := isVector s_car in
      let%success s_car_len := LENGTH s_car in
      ifb ~ s_car_iv \/ s_car_len > 1 then
        result_rreturn false
      else result_rskip using runs in
    result_success true
  else result_success false.

Definition isArray s : result_bool :=
  add%stack "isArray" in
  if%success isVector s then
    let%success t := runs_getAttrib runs s R_DimSymbol in
    let%success t_type := TYPEOF t in
    let%success t_len := LENGTH t in
    ifb t_type = IntSxp /\ t_len > 0 then
      result_success true
    else result_success false
  else result_success false.

Definition isTs s : result_bool :=
  add%stack "isTs" in
  if%success isVector s then
    let%success a := runs_getAttrib runs s R_TspSymbol in
    (a '!= R_NilValue : result_bool)
  else result_success false.

Definition conformable x y : result_bool :=
  add%stack "conformable" in
  let%success x := runs_getAttrib runs x R_DimSymbol in
  let%success y := runs_getAttrib runs y R_DimSymbol in
  let%success x_len := R_length runs x in
  let%success y_len := R_length runs y in
  ifb x_len <> y_len then
    result_success false
  else
    let n := x_len in
    do%exit
    for i from 0 to n - 1 do
      read%Integer x_i := x at i in
      read%Integer y_i := y at i in
      ifb x_i <> y_i then
        result_rreturn false
      else result_rskip in
    result_success true.

Definition isValidString x : result_bool :=
  add%stack "isValidString" in
  let%success x_type := TYPEOF x in
  let%success x_len := LENGTH x in
  let%success x_0 := STRING_ELT x 0 in
  let%success x_0_type := TYPEOF x_0 in
  result_success (decide (x_type = StrSxp /\ x_len > 0 /\ x_0_type <> NilSxp)).


(** ** util.c **)

(** The function names of this section correspond to the function names
  in the file main/util.c. **)

Definition type2rstr (t : SExpType) : result_SEXP :=
  add%stack "type2rstr" in
  get%globals globals in
  let res := Type2Table_rstrName (ArrayList.read (global_Type2Table globals) t) in
  ifb res <> NULL then result_success res
  else (R_NilValue : result_SEXP).

Definition nthcdr s n : result_SEXP :=
  add%stack "nthcdr" in
  let%success s_li := isList s in
  let%success s_la := isLanguage s in
  let%success s_fr := isFrame runs s in
  let%success s_t := TYPEOF s in
  ifb s_li \/ s_la \/ s_fr \/ s_t = DotSxp then
    do%success (s, n) := (s, contextual_ret n)
    whileb n > 0 do
      ifc s '== R_NilValue then
        result_error "List too short."
      else
        read%list _, s_cdr, _ := s in
        result_success (s_cdr, n - 1) using runs in
    result_success s
  else result_error "No CDR.".


(** ** envir.c **)

(** The function names of this section correspond to the function names
  in the file main/envir.c. **)

(** The function [mkChar] from the R source code performs a lot of things.
  It deals with encoding, for embedded zero-characters, as well as avoid
  allocated twice the same string, by looking through the already
  allocated strings. We do none of the above. **)
(* FIXME: What is the difference between [intCHARSXP] and [CHARSXP]? *)
Definition mkChar (str : string) : result_SEXP :=
  (* Note that values are not cached, in contrary to the original code. *)
  alloc_vector_char (ArrayList.from_list (string_to_list str)).

Definition mkString (str : string) : result_SEXP :=
  let%success c := mkChar str in
  alloc_vector_str (ArrayList.from_list [c]).

Definition BCCONSTS e : result_SEXP :=
  add%stack "BCCONSTS" in
  BCODE_CONSTS e.


(** ** eval.c **)

(** The function names of this section correspond to the function names
  in the file main/eval.c. **)

Definition bytecodeExpr e : result_SEXP :=
  add%stack "bytecodeExpr" in
  if%success isByteCode e then
    let%success e := BCCONSTS e in
    let%success e_len := LENGTH e in
    ifb e_len > 0 then
      VECTOR_ELT e 0
    else (R_NilValue : result_SEXP)
  else (e : result_SEXP).

Definition R_PromiseExpr p : result_SEXP :=
  add%stack "R_PromiseExpr" in
  read%prom _, p_prom := p in
  bytecodeExpr (prom_expr p_prom).

Definition PREXPR e : result_SEXP :=
  add%stack "PREXPR" in
  R_PromiseExpr e.

Definition R_ClosureExpr p : result_SEXP :=
  add%stack "R_ClosureExpr" in
  read%clo _, p_clo := p in
  bytecodeExpr (clo_body p_clo).

Definition BODY_EXPR e : result_SEXP :=
  add%stack "BODY_EXPR" in
  R_ClosureExpr e.


(** ** attrib.c **)

(** The function names of this section correspond to the function names
  in the file main/attrib.c. **)

Definition R_data_class  (obj : _SEXP) (singleString : bool) : result_SEXP :=
  add%stack "R_data_class" in
  result_not_implemented "R_data_class".

Definition R_data_class2 (obj : _SEXP) : result_SEXP :=
  add%stack "R_data_class2" in
  result_not_implemented "R_data_class2".


(** ** objects.c **)

(** The function names of this section correspond to the function names
  in the file main/objects.c. **)

Definition inherits2 x what : result_bool :=
  add%stack "inherits2" in
  if%success OBJECT x then
    let%success klass :=
    if%success IS_S4_OBJECT x then
      R_data_class2 x
    else
      R_data_class x false
    in
    let%success nclass := R_length runs klass in
    do%exit
    for i from 0 to nclass - 1 do
      let%success klass_i := STRING_ELT klass i in
      let%success klass_i_char := CHAR klass_i in
      ifb klass_i_char = what then
        result_rreturn true
      else
        result_rskip
    in
    result_success false
  else
    result_success false.

End Parameterised.

