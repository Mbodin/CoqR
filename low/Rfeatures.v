(** Rfeatures.
 * A Coq formalisation of additionnal functions of R from its C code. **)

Set Implicit Arguments.
Require Export Reval.


Section Parameters.

Variable globals : Globals.

Let read_globals : GlobalVariable -> SExpRec_pointer := globals.

Local Coercion read_globals : GlobalVariable >-> SExpRec_pointer.

Variable runs : runs_type.

(** * eval.c **)

(** The function names of this section corresponds to the function names
 * in the file main/eval.c. **)

Definition do_set S (call op args rho : SExpRec_pointer) : result SExpRec_pointer :=
  let wrong S := result_error S "[do_set] Wrong argument count." in
  ifb args = R_NilValue then wrong S
  else read%list args_, args_list := args using S in
  ifb list_cdrval args_list = R_NilValue then wrong S
  else read%list args_cdr_, args_cdr_list := list_cdrval args_list using S in
  ifb list_cdrval args_cdr_list = R_NilValue then wrong S
  else
    read%defined lhs_ := list_carval args_list using S in
    let symcase S :=
      let%success rhs := runs_eval runs (list_carval args_cdr_list) rho using S in
      let%success _ := INCREMENT_NAMED S rhs using S in
      result_not_implemented "[do_set] TODO" in
    match type lhs_ with
    | StrSxp =>
      let%success lhs_char := STRING_ELT S lhs 0 using S in
      let%success lhs := installTrChar lhs_char using S in
      symcase S
    | SymSxp => symcase S
    | LangSxp => result_not_implemented "[do_set] TODO"
    | _ => result_error S "[do_set] Invalid left-hand side to assignment."
    end.


End Parameters.

