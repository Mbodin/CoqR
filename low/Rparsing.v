(** Rparsing.
 * This file contains functions for parsing R expressions. **)

Set Implicit Arguments.
Require Export Reval.

(** * gram.y **)

(** The function names of this section corresponds to the function names
 * in the file main/gram.y. **)

(** This modules corresponds to all functions used in the grammar of the file main/gram.y. **)

Module Parsing.

(** The following functions create R expressions.
 * They are only used in the parser. **)

Section Parameters.

Variable globals : Globals.

Let read_globals : GlobalVariable -> SExpRec_pointer := globals.

Local Coercion read_globals : GlobalVariable >-> SExpRec_pointer.

Variable runs : runs_type.


Definition xxunary S op arg :=
  lang2 globals S op arg.

Definition xxbinary S n1 n2 n3 :=
  lang3 globals S n1 n2 n3.

Definition xxparen S n1 n2 :=
  lang2 globals S n1 n2.

Definition xxdefun S fname formals body :=
  read%list _, formals_list := formals using S in
  let srcref := R_NilValue : SExpRec_pointer in
  lang4 globals S fname (list_cdrval formals_list) body srcref.

Definition xxexprlist S a1 a2 :=
  map%pointer a2 with set_type LangSxp using S in
  set%car a2 := a1 using S in
  result_success S a2.

Definition xxexprlist0 S :=
  NewList globals S.

Definition xxexprlist1 S expr :=
  let%success tmp := NewList globals S using S in
  GrowList globals S tmp expr.

Definition xxexprlist2 S exprlist expr :=
  GrowList globals S exprlist expr.

Definition xxfuncall S expr args :=
  let%success expr :=
    read%defined expr_ := expr using S in
    ifb type expr_ = StrSxp then
      let%success expr_ := STRING_ELT S expr 0 using S in
      installTrChar globals runs S expr_
    else result_success S expr using S in
  read%list _, args_list := args using S in
  let args_cdr := list_cdrval args_list in
  read%list _, args_cdr_list := args_cdr using S in
  let%success args_len := R_length globals runs S args_cdr using S in
  ifb args_len = 1 /\ list_carval args_cdr_list = R_MissingArg /\ list_tagval args_cdr_list = R_NilValue then
    lang1 globals S expr
  else
    lcons globals S expr args_cdr.

Definition xxcond S expr : result SExpRec_pointer :=
  result_success S expr.

Definition xxifcond S expr : result SExpRec_pointer :=
  result_success S expr.

Definition xxif S ifsym cond expr :=
  lang3 globals S ifsym cond expr.

Definition xxifelse S ifsym cond ifexpr elseexpr :=
  lang4 globals S ifsym cond ifexpr elseexpr.

Definition xxforcond S sym expr :=
  lcons globals S sym expr.

Definition xxfor S forsym forcond body :=
  read%list _, forcond_list := forcond using S in
  lang4 globals S forsym (list_carval forcond_list) (list_cdrval forcond_list) body.

Definition xxwhile S whilesym cond body :=
  lang3 globals S whilesym cond body.

Definition xxrepeat S repeatsym body :=
  lang2 globals S repeatsym body.

Definition xxnxtbrk S keyword :=
  lang1 globals S keyword.

Definition xxsubscript S a1 a2 a3 :=
  read%list _, a3_list := a3 using S in
  let (S, l) := CONS globals S a1 (list_cdrval a3_list) in
  lcons globals S a2 l.

Definition xxsub0 S :=
  lang2 globals S R_MissingArg R_NilValue.

Definition xxsub1 S expr :=
  TagArg globals runs S expr R_NilValue.

Definition xxsymsub0 S sym :=
  TagArg globals runs S R_MissingArg sym.

Definition xxsymsub1 S sym expr :=
  TagArg globals runs S expr sym.

Definition xxnullsub0 S :=
  let%success ans := install globals runs S "NULL" using S in
  TagArg globals runs S R_MissingArg ans.

Definition xxnullsub1 S expr :=
  let%success ans := install globals runs S "NULL" using S in
  TagArg globals runs S expr ans.

Definition xxnullformal S :=
  result_success S (R_NilValue : SExpRec_pointer).

Definition xxfirstformal0 S sym :=
  FirstArg globals S R_MissingArg sym.

Definition xxfirstformal1 S sym expr :=
  FirstArg globals S expr sym.

Definition xxaddformal0 S formlist sym :=
  let%success _ := CheckFormalArgs globals runs S formlist sym using S in
  NextArg globals S formlist R_MissingArg sym.

Definition xxaddformal1 S formlist sym expr :=
  let%success _ := CheckFormalArgs globals runs S formlist sym using S in
  NextArg globals S formlist expr sym.

Definition xxsublist1 S sub :=
  read%list _, sub_list := sub using S in
  read%list _, sub_cdr_list := list_cdrval sub_list using S in
  FirstArg globals S (list_carval sub_list) (list_carval sub_cdr_list).

Definition xxsublist2 S sublist sub :=
  read%list _, sub_list := sub using S in
  read%list _, sub_cdr_list := list_cdrval sub_list using S in
  NextArg globals S sublist (list_carval sub_list) (list_carval sub_cdr_list).

End Parameters.

End Parsing.

