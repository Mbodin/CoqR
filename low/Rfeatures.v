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

(** All function in the array [R_FunTab] have the same type. **)
Definition function_code :=
  state ->
  SExpRec_pointer -> (** call **)
  SExpRec_pointer -> (** op **)
  SExpRec_pointer -> (** args **)
  SExpRec_pointer -> (** rho **)
  result SExpRec_pointer.

(** The following type is represented in C as an integer, each of its figure
 * (in base 10) representing a different bit of information. **)
Record funtab_eval_arg := make_funtab_eval_arg {
    funtab_eval_arg_internal : bool ; (** Is it stored in the array [.Internals] or directly visible? **)
    funtab_eval_arg_eval : bool (** Should we evaluate arguments before calling? **)
  }.

(** FUNTAB **)
Record funtab_cell := make_funtab_cell {
    fun_name : string ;
    fun_cfun : function_code ;
    fun_code : nat ;
    fun_eval : funtab_eval_arg ;
    fun_arity : int
  }.

Definition funtab := option (list funtab_cell).

Section Parameter_R_FunTab.

Variable R_FunTab : funtab.

Definition read_R_FunTab S n :=
  match R_FunTab with
  | None => result_bottom S
  | Some f =>
    match nth_option n f with
    | None => result_impossible S "[read_R_FunTab] Out of bounds."
    | Some c => result_success S c
    end
  end.



(** ** dstruct.c **)

Definition mkPRIMSXP (S : state) (offset : nat) (type_ : bool) : result SExpRec_pointer :=
  let type_ :=
    ifb type_ then BuiltinSxp else SpecialSxp in
  let%defined FunTabSize := LibOption.map length R_FunTab using S in
  (** The initialisation of the array is performed in [mkPRIMSXP_init] in [Rinit]. **)
  ifb offset >= FunTabSize then
    result_error S "[mkPRIMSXP] Offset is out of range"
  else
    read%VectorPointers primCache_ := mkPRIMSXP_primCache using S in
    let%defined result := nth_option offset primCache_ using S in
    ifb result = R_NilValue then
      (*TODO: let (S, result) := alloc_SExp S _ in*)
      result_not_implemented "[mkPRIMSXP] TODO"
    else
      read%defined result_ := result using S in
      ifb type result_ <> type_ then
        result_error S "[mkPRIMSXP] Requested primitive type is not consistent with cached value."
      else result_success S result.


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
      read%prim op_, op_prim := op using S in
      let%success c := read_R_FunTab S (prim_offset op_prim) using S in
      ifb fun_code c = 2 then
        result_not_implemented "[do_set] setVar"
      else
        let%success _ := defineVar globals runs S lhs rhs rho using S in
        result_success S rhs in
    match type lhs_ with
    | StrSxp =>
      let%success lhs_char := STRING_ELT S lhs 0 using S in
      let%success lhs := installTrChar globals runs S lhs_char using S in
      symcase S
    | SymSxp => symcase S
    | LangSxp => result_not_implemented "[do_set] applydefine"
    | _ => result_error S "[do_set] Invalid left-hand side to assignment."
    end.


(** * names.c **)

(** The function names of this section corresponds to the function names
 * in the file main/names.c. **)

(** In contrary to the original C, this function here takes as argument
 * the structure of type [funtab_cell] in addition to its range in the
 * array [R_FunTab]. **)
Definition installFunTab S c offset : result unit :=
  let%success prim := mkPRIMSXP S offset (funtab_eval_arg_eval (fun_eval c)) using S in
  let%success p := install globals runs S (fun_name c) using S in
  read%sym p_, p_sym := p using S in
  let p_sym :=
    if funtab_eval_arg_internal (fun_eval c) then {|
        sym_pname := sym_pname p_sym ;
        sym_value := sym_value p_sym ;
        sym_internal := prim
      |}
    else {|
        sym_pname := sym_pname p_sym ;
        sym_value := prim ;
        sym_internal := sym_internal p_sym
      |} in
  let p_ := {|
      NonVector_SExpRec_header := NonVector_SExpRec_header p_ ;
      NonVector_SExpRec_data := p_sym
    |} in
  write%defined p := p_ using S in
  result_success S tt.

End Parameter_R_FunTab.


(** * Closing the Loop: [R_FunTab] **)

(** In R source code, [R_FunTab] is an array accessed by offset. We
 * here make the choice to define it as a function accessed by
 * [primitive_construction]. See report for more details. **)

Local Instance funtab_cell_Inhab : Inhab funtab_cell.
  apply prove_Inhab. constructors; try typeclass; constructors; typeclass.
Qed.

Fixpoint R_FunTab max_step : funtab :=
  let eval0 := make_funtab_eval_arg false false in
  let eval1 := make_funtab_eval_arg false true in
  let eval10 := make_funtab_eval_arg true false in
  let eval11 := make_funtab_eval_arg true true in
  let eval100 := make_funtab_eval_arg false false in
  let eval101 := make_funtab_eval_arg false true in
  let eval110 := make_funtab_eval_arg true false in
  let eval111 := make_funtab_eval_arg true true in
  let eval200 := make_funtab_eval_arg false false in
  let eval201 := make_funtab_eval_arg false true in
  let eval210 := make_funtab_eval_arg true false in
  let eval211 := make_funtab_eval_arg true true in
  match max_step with
  | O => None
  | S max_step =>
    let decl name cfun code eval arity :=
      make_funtab_cell name cfun code eval arity in
    let wrap f S call op args rho :=
      (** This function waits that all arguments are given before starting
        * the computation of the next [R_FunTab]. **)
      f (R_FunTab max_step) S call op args rho in
    let rdecl name cfun code eval arity :=
      decl name (wrap cfun) code eval arity in
    Some [
        rdecl "<-" do_set 1 eval100 (-1)%Z ;
        rdecl "=" do_set 3 eval100 (-1)%Z ;
        rdecl "<<-" do_set 2 eval100 (-1)%Z
      ]%string
  end.

End Parameters.

