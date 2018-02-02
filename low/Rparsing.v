(** Rparsing.
  This file formalises functions for parsing R expressions. **)

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


Definition xxunary S op arg :=
  add%stack "xxunary" in
  lang2 globals S op arg.

Definition xxbinary S n1 n2 n3 :=
  add%stack "xxbinary" in
  lang3 globals S n1 n2 n3.

Definition xxparen S n1 n2 :=
  add%stack "xxparen" in
  lang2 globals S n1 n2.

Definition xxdefun S fname formals body :=
  add%stack "xxdefun" in
  read%list _, formals_cdr, _ := formals using S in
  let srcref := R_NilValue : SEXP in
  lang4 globals S fname formals_cdr body srcref.

Definition xxexprlist S a1 a2 :=
  add%stack "xxexprlist" in
  map%pointer a2 with set_type LangSxp using S in
  set%car a2 := a1 using S in
  result_success S a2.

Definition xxexprlist0 S :=
  add%stack "xxexprlist0" in
  NewList globals S.

Definition xxexprlist1 S expr :=
  add%stack "xxexprlist1" in
  let%success tmp := NewList globals S using S in
  GrowList globals S tmp expr.

Definition xxexprlist2 S exprlist expr :=
  add%stack "xxexprlist2" in
  GrowList globals S exprlist expr.

Definition xxfuncall S expr args :=
  add%stack "xxfuncall" in
  let%success expr :=
    read%defined expr_ := expr using S in
    ifb type expr_ = StrSxp then
      let%success expr_ := STRING_ELT S expr 0 using S in
      installTrChar globals runs S expr_
    else result_success S expr using S in
  read%list _, args_cdr, _ := args using S in
  read%list args_cdr_car, _, args_cdr_tag := args_cdr using S in
  let%success args_len := R_length globals runs S args_cdr using S in
  ifb args_len = 1 /\ args_cdr_car = R_MissingArg /\ args_cdr_tag = R_NilValue then
    lang1 globals S expr
  else
    lcons globals S expr args_cdr.

Definition xxcond S expr : result SEXP :=
  add%stack "xxcond" in
  result_success S expr.

Definition xxifcond S expr : result SEXP :=
  add%stack "xxifcond" in
  result_success S expr.

Definition xxif S ifsym cond expr :=
  add%stack "xxif" in
  lang3 globals S ifsym cond expr.

Definition xxifelse S ifsym cond ifexpr elseexpr :=
  add%stack "xxifelse" in
  lang4 globals S ifsym cond ifexpr elseexpr.

Definition xxforcond S sym expr :=
  add%stack "xxforcond" in
  lcons globals S sym expr.

Definition xxfor S forsym forcond body :=
  add%stack "xxfor" in
  read%list forcond_car, forcond_cdr, _ := forcond using S in
  lang4 globals S forsym forcond_car forcond_cdr body.

Definition xxwhile S whilesym cond body :=
  add%stack "xxwhile" in
  lang3 globals S whilesym cond body.

Definition xxrepeat S repeatsym body :=
  add%stack "xxrepeat" in
  lang2 globals S repeatsym body.

Definition xxnxtbrk S keyword :=
  add%stack "xxnxtbrk" in
  lang1 globals S keyword.

Definition xxsubscript S a1 a2 a3 :=
  add%stack "xxsubscript" in
  read%list _, a3_cdr, _ := a3 using S in
  let (S, l) := CONS globals S a1 a3_cdr in
  lcons globals S a2 l.

Definition xxsub0 S :=
  add%stack "xxsub0" in
  lang2 globals S R_MissingArg R_NilValue.

Definition xxsub1 S expr :=
  add%stack "xxsub1" in
  TagArg globals runs S expr R_NilValue.

Definition xxsymsub0 S sym :=
  add%stack "xxsymsub0" in
  TagArg globals runs S R_MissingArg sym.

Definition xxsymsub1 S sym expr :=
  add%stack "xxsymsub1" in
  TagArg globals runs S expr sym.

Definition xxnullsub0 S :=
  add%stack "xxnullsub0" in
  let%success ans := install globals runs S "NULL" using S in
  TagArg globals runs S R_MissingArg ans.

Definition xxnullsub1 S expr :=
  add%stack "xxnullsub1" in
  let%success ans := install globals runs S "NULL" using S in
  TagArg globals runs S expr ans.

Definition xxnullformal S :=
  add%stack "xxnullformal" in
  result_success S (R_NilValue : SEXP).

Definition xxfirstformal0 S sym :=
  add%stack "xxfirstformal0" in
  FirstArg globals S R_MissingArg sym.

Definition xxfirstformal1 S sym expr :=
  add%stack "xxfirstformal1" in
  FirstArg globals S expr sym.

Definition xxaddformal0 S formlist sym :=
  add%stack "xxaddformal0" in
  let%success _ := CheckFormalArgs globals runs S formlist sym using S in
  NextArg globals S formlist R_MissingArg sym.

Definition xxaddformal1 S formlist sym expr :=
  add%stack "xxaddformal1" in
  let%success _ := CheckFormalArgs globals runs S formlist sym using S in
  NextArg globals S formlist expr sym.

Definition xxsublist1 S sub :=
  add%stack "xxsublist1" in
  read%list sub_car, sub_cdr, _ := sub using S in
  read%list sub_cdr_car, _, _ := sub_cdr using S in
  FirstArg globals S sub_car sub_cdr_car.

Definition xxsublist2 S sublist sub :=
  add%stack "xxsublist2" in
  read%list sub_car, sub_cdr, _ := sub using S in
  read%list sub_cdr_car, _, _ := sub_cdr using S in
  NextArg globals S sublist sub_car sub_cdr_car.

End Parameters.

End Parsing.

