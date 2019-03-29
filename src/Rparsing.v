(** Rparsing.
  This file formalises functions for parsing R expressions. **)

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
Require Export Rcore.

(** * gram.y **)

(** The function names of this section corresponds to the function names
  in the file main/gram.y. **)

(** This modules corresponds to all functions used in the grammar of the file main/gram.y. **)

Module Parsing.

(** The following functions create R expressions.
  They are only used in the parser. **)

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.

Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.


Definition xxunary op arg :=
  add%stack "xxunary" in
  lang2 globals op arg.

Definition xxbinary n1 n2 n3 :=
  add%stack "xxbinary" in
  lang3 globals n1 n2 n3.

Definition xxparen n1 n2 :=
  add%stack "xxparen" in
  lang2 globals n1 n2.

Definition xxdefun fname formals body :=
  add%stack "xxdefun" in
  read%list _, formals_cdr, _ := formals in
  let srcref := R_NilValue : SEXP in
  lang4 globals fname formals_cdr body srcref.

Definition xxexprlist a1 a2 :=
  add%stack "xxexprlist" in
  set%type a2 := LangSxp in
  set%car a2 := a1 in
  result_success a2.

Definition xxexprlist0 :=
  add%stack "xxexprlist0" in
  NewList globals.

Definition xxexprlist1 expr :=
  add%stack "xxexprlist1" in
  let%success tmp := NewList globals in
  GrowList globals tmp expr.

Definition xxexprlist2 exprlist expr :=
  add%stack "xxexprlist2" in
  GrowList globals exprlist expr.

Definition xxfuncall expr args :=
  add%stack "xxfuncall" in
  let%success expr :=
    if%success isString expr then
      let%success expr_0 := STRING_ELT expr 0 in
      installTrChar globals runs expr_0
    else result_success expr in
  read%list _, args_cdr, _ := args in
  read%list args_cdr_car, _, args_cdr_tag := args_cdr in
  let%success args_len := R_length globals runs args_cdr in
  ifb args_len = 1 /\ args_cdr_car = R_MissingArg /\ args_cdr_tag = R_NilValue then
    lang1 globals expr
  else
    lcons globals expr args_cdr.

Definition xxcond expr : result SEXP :=
  add%stack "xxcond" in
  result_success expr.

Definition xxifcond expr : result SEXP :=
  add%stack "xxifcond" in
  result_success expr.

Definition xxif ifsym cond expr :=
  add%stack "xxif" in
  lang3 globals ifsym cond expr.

Definition xxifelse ifsym cond ifexpr elseexpr :=
  add%stack "xxifelse" in
  lang4 globals ifsym cond ifexpr elseexpr.

Definition xxforcond sym expr :=
  add%stack "xxforcond" in
  lcons globals sym expr.

Definition xxfor forsym forcond body :=
  add%stack "xxfor" in
  read%list forcond_car, forcond_cdr, _ := forcond in
  lang4 globals forsym forcond_car forcond_cdr body.

Definition xxwhile whilesym cond body :=
  add%stack "xxwhile" in
  lang3 globals whilesym cond body.

Definition xxrepeat repeatsym body :=
  add%stack "xxrepeat" in
  lang2 globals repeatsym body.

Definition xxnxtbrk keyword :=
  add%stack "xxnxtbrk" in
  lang1 globals keyword.

Definition xxsubscript a1 a2 a3 :=
  add%stack "xxsubscript" in
  read%list _, a3_cdr, _ := a3 in
  let%success l := CONS globals a1 a3_cdr in
  lcons globals a2 l.

Definition xxsub0 :=
  add%stack "xxsub0" in
  lang2 globals R_MissingArg R_NilValue.

Definition xxsub1 expr :=
  add%stack "xxsub1" in
  TagArg globals runs expr R_NilValue.

Definition xxsymsub0 sym :=
  add%stack "xxsymsub0" in
  TagArg globals runs R_MissingArg sym.

Definition xxsymsub1 sym expr :=
  add%stack "xxsymsub1" in
  TagArg globals runs expr sym.

Definition xxnullsub0 :=
  add%stack "xxnullsub0" in
  let%success ans := install globals runs "NULL" in
  TagArg globals runs R_MissingArg ans.

Definition xxnullsub1 expr :=
  add%stack "xxnullsub1" in
  let%success ans := install globals runs "NULL" in
  TagArg globals runs expr ans.

Definition xxnullformal :=
  add%stack "xxnullformal" in
  result_success (R_NilValue : SEXP).

Definition xxfirstformal0 sym :=
  add%stack "xxfirstformal0" in
  FirstArg globals R_MissingArg sym.

Definition xxfirstformal1 sym expr :=
  add%stack "xxfirstformal1" in
  FirstArg globals expr sym.

Definition xxaddformal0 formlist sym :=
  add%stack "xxaddformal0" in
  let%success _ := CheckFormalArgs globals runs formlist sym in
  NextArg globals formlist R_MissingArg sym.

Definition xxaddformal1 formlist sym expr :=
  add%stack "xxaddformal1" in
  let%success _ := CheckFormalArgs globals runs formlist sym in
  NextArg globals formlist expr sym.

Definition xxsublist1 sub :=
  add%stack "xxsublist1" in
  read%list sub_car, sub_cdr, _ := sub in
  read%list sub_cdr_car, _, _ := sub_cdr in
  FirstArg globals sub_car sub_cdr_car.

Definition xxsublist2 sublist sub :=
  add%stack "xxsublist2" in
  read%list sub_car, sub_cdr, _ := sub in
  read%list sub_cdr_car, _, _ := sub_cdr in
  NextArg globals sublist sub_car sub_cdr_car.

End Parameters.

End Parsing.

