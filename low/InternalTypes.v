(** InternalTypes.
  This file describes various internal data types used in the source of R. **)

Require Import Rinternals Monads.


(** * FUNTAB **)

(** This section defines the FUNTAB structure, which is used to store
  primitive and internal functions, as well as some constructs to
  evaluate it. Most of these constructs can be found in
  include/Defn.h. **)

(** All function in the array [R_FunTab] have the same type. **)
Definition function_code :=
  state ->
  SExpRec_pointer -> (** call **)
  SExpRec_pointer -> (** op **)
  SExpRec_pointer -> (** args **)
  SExpRec_pointer -> (** rho **)
  result SExpRec_pointer.

(** The following type is represented in C as an integer, each of its figure
  (in base 10) representing a different bit of information. **)
Record funtab_eval_arg := make_funtab_eval_arg {
    funtab_eval_arg_internal : bool ; (** Whether it is stored in the array [.Internals] or directly visible. **)
    funtab_eval_arg_eval : bool (** Whether its arguments should be evaluated before calling (that is, whether it is a [BuiltinSxp] or a [SpecialSxp]). **)
  }.

Instance funtab_eval_arg_Inhab : Inhab funtab_eval_arg.
  apply prove_Inhab. constructors; typeclass.
Qed.

(** PPkind **)
Inductive PPkind :=
  | PP_INVALID
  | PP_ASSIGN
  | PP_ASSIGN2
  | PP_BINARY
  | PP_BINARY2
  | PP_BREAK
  | PP_CURLY
  | PP_FOR
  | PP_FUNCALL
  | PP_FUNCTION
  | PP_IF
  | PP_NEXT
  | PP_PAREN
  | PP_RETURN
  | PP_SUBASS
  | PP_SUBSET
  | PP_WHILE
  | PP_UNARY
  | PP_DOLLAR
  | PP_FOREIGN
  | PP_REPEAT
  .

Instance PPkind_Comparable : Comparable PPkind.
  prove_comparable_trivial_inductive.
Defined.

Instance PPkind_Inhab : Inhab PPkind.
  apply prove_Inhab. constructors~.
Qed.

(** PPprec **)
Inductive PPprec :=
  | PREC_FN
  | PREC_EQ
  | PREC_LEFT
  | PREC_RIGHT
  | PREC_TILDE
  | PREC_OR
  | PREC_AND
  | PREC_NOT
  | PREC_COMPARE
  | PREC_SUM
  | PREC_PROD
  | PREC_PERCENT
  | PREC_COLON
  | PREC_SIGN
  | PREC_POWER
  | PREC_SUBSET
  | PREC_DOLLAR
  | PREC_NS
  .

Instance PPprec_Comparable : Comparable PPprec.
  prove_comparable_trivial_inductive.
Defined.

Instance PPprecd_Inhab : Inhab PPprec.
  apply prove_Inhab. constructors~.
Qed.

(** PPinfo **)
Record PPinfo := make_PPinfo {
    PPinfo_kind : PPkind ;
    PPinfo_precedence : PPprec ;
    PPinfo_rightassoc : bool
  }.

Instance PPinfo_Inhab : Inhab PPinfo.
  apply prove_Inhab. constructors; typeclass.
Qed.

(** FUNTAB **)
Record funtab_cell := make_funtab_cell {
    fun_name : string ;
    fun_cfun : function_code ;
    fun_code : int ; (** The number stored here can be quite large. We thus use [int] instead of [nat] here. **)
    fun_eval : funtab_eval_arg ;
    fun_arity : int ;
    fun_gram : PPinfo
  }.

Instance funtab_cell_Inhab : Inhab funtab_cell.
  apply prove_Inhab. constructors; apply arbitrary.
Qed.

Definition funtab := option (ArrayList.array funtab_cell).


(** * Type2Table **)

(** These definitions can be found in the file main/util.c. **)

Record Type2Table_type := make_Type2Table_type {
    Type2Table_cstrName : string ;
    Type2Table_rcharName : SExpRec_pointer ;
    Type2Table_rstrName : SExpRec_pointer ;
    Type2Table_rsymName : SExpRec_pointer ;
  }.

Instance Type2Table_type_Inhab : Inhab Type2Table_type.
  apply prove_Inhab. constructors; apply arbitrary.
Qed.


(** * BindData **)

(** These definitions can be found in the file main/bind.c. **)

Record BindData := make_BindData {
    BindData_ans_flags : nbits 10 ;
    BindData_ans_ptr : SExpRec_pointer ;
    BindData_ans_length : nat ;
    BindData_ans_names : SExpRec_pointer ;
    BindData_ans_nnames : nat
  }.

Definition BindData_with_ans_flags d f := {|
    BindData_ans_flags := f ;
    BindData_ans_ptr := BindData_ans_ptr d ;
    BindData_ans_length := BindData_ans_length d ;
    BindData_ans_names := BindData_ans_names d ;
    BindData_ans_nnames := BindData_ans_nnames d
  |}.

Definition BindData_with_ans_ptr d p := {|
    BindData_ans_flags := BindData_ans_flags d ;
    BindData_ans_ptr := p ;
    BindData_ans_length := BindData_ans_length d ;
    BindData_ans_names := BindData_ans_names d ;
    BindData_ans_nnames := BindData_ans_nnames d
  |}.

Definition BindData_with_ans_length d l := {|
    BindData_ans_flags := BindData_ans_flags d ;
    BindData_ans_ptr := BindData_ans_ptr d ;
    BindData_ans_length := l ;
    BindData_ans_names := BindData_ans_names d ;
    BindData_ans_nnames := BindData_ans_nnames d
  |}.

Definition BindData_with_ans_names d n := {|
    BindData_ans_flags := BindData_ans_flags d ;
    BindData_ans_ptr := BindData_ans_ptr d ;
    BindData_ans_length := BindData_ans_length d ;
    BindData_ans_names := n ;
    BindData_ans_nnames := BindData_ans_nnames d
  |}.

Definition BindData_with_ans_nnames d n := {|
    BindData_ans_flags := BindData_ans_flags d ;
    BindData_ans_ptr := BindData_ans_ptr d ;
    BindData_ans_length := BindData_ans_length d ;
    BindData_ans_names := BindData_ans_names d ;
    BindData_ans_nnames := n
  |}.
