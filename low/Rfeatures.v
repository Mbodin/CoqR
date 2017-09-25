(** Rfeatures.
 * A Coq formalisation of additionnal functions of R from its C code. **)

Set Implicit Arguments.
Require Export Reval.


Section Parameters.

Variable globals : Globals.

Let read_globals : GlobalVariable -> SExpRec_pointer := globals.

Local Coercion read_globals : GlobalVariable >-> SExpRec_pointer.

Variable runs : runs_type.

(** * Defn.h **)

(** This section defines the FUNTAB structure, which is used to store primitive
  and internal functions, as well as some constructs to evaluate it. **)

(** To represent functions of any arity, we use the following inductive.
  See report for more details. **)
Inductive function_code : nat -> Prop :=
  | function_code_0 : SExpRec_pointer -> function_code 0
  | function_code_next : forall n,
    (SExpRec_pointer -> function_code n) -> function_code (S n)
  .

(** FUNTAB **)
Record funtab_cell := make_funtab_cell {
    fun_name : string ;
    fun_arity : nat ;
    fun_code : function_code fun_arity ;
    fun_eval : bool
  }.

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
    let lhs := list_carval args_list in
    read%defined lhs_ := lhs using S in
    let symcase S :=
      let%success rhs := runs_eval runs S (list_carval args_cdr_list) rho using S in
      let%success _ := INCREMENT_NAMED S rhs using S in
      result_not_implemented "[do_set] TODO" in
    match type lhs_ with
    | StrSxp =>
      let%success lhs_char := STRING_ELT S lhs 0 using S in
      let%success lhs := installTrChar globals runs S lhs_char using S in
      symcase S
    | SymSxp => symcase S
    | LangSxp => result_not_implemented "[do_set] TODO"
    | _ => result_error S "[do_set] Invalid left-hand side to assignment."
    end.


(** * [R_FunTabs] **)

(** In R source code, [R_FunTabs] is an array accessed by offset. We
 * here make the choice to define it as a function accessed by
 * [primitive_construction]. See report for more details. **)

Local Instance funtab_cell_Inhab : Inhab funtab_cell.
  apply prove_Inhab. constructors; try typeclass.
  apply (function_code_0 arbitrary).
Qed.

Definition funtab := primitive_construction -> funtab_cell.

Definition R_FunTabs : funtab := fun c =>
  match c with
  | _ => arbitrary
  end.

End Parameters.

