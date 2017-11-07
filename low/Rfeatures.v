(** Rfeatures.
  A Coq formalisation of additionnal functions of R from its C code. **)

Set Implicit Arguments.
Require Export Rcore.


Section Parameters.

Variable globals : Globals.

Let read_globals : GlobalVariable -> SExpRec_pointer := globals.

Local Coercion read_globals : GlobalVariable >-> SExpRec_pointer.

Variable runs : runs_type.


Definition dummy_function name (S : state) (call op args rho : SExpRec_pointer) : result SExpRec_pointer :=
  result_not_implemented ("[" ++ name ++ "]").


(** * errors.c **)

(** The function names of this section corresponds to the function names
  in the file main/errors.c. **)

Definition WrongArgCount A S s : result A :=
  result_error S ("[WrongArgCount] Incorrect number of arguments to " ++ s ++ ".").
Arguments WrongArgCount [A].


(** * dstruct.c **)

(** The function names of this section corresponds to the function names
  in the file main/dstruct.c. **)

Definition mkPRIMSXP S (offset : nat) (type_ : bool) : result SExpRec_pointer :=
  let type_ :=
    ifb type_ then BuiltinSxp else SpecialSxp in
  let%defined FunTabSize := LibOption.map length (runs_R_FunTab runs) using S in
  (** The initialisation of the array is performed in [mkPRIMSXP_init] in [Rinit]. **)
  ifb offset >= FunTabSize then
    result_error S "[mkPRIMSXP] Offset is out of range"
  else
    read%Pointer result := mkPRIMSXP_primCache at offset using S in
    ifb result = R_NilValue then
      let (S, result) := alloc_SExp S (make_SExpRec_prim R_NilValue offset type_) in
      write%Pointer mkPRIMSXP_primCache at offset := result using S in
      result_success S result
    else
      read%defined result_ := result using S in
      ifb type result_ <> type_ then
        result_error S "[mkPRIMSXP] Requested primitive type is not consistent with cached value."
      else result_success S result.

Definition mkCLOSXP S (formals body rho : SExpRec_pointer) :=
  read%defined body_ := body using S in
  match type body_ with
  | CloSxp
  | BuiltinSxp
  | SpecialSxp
  | DotSxp
  | AnySxp =>
    result_error S "[mkCLOSXP] Invalid body argument."
  | _ =>
    let env :=
      ifb rho = R_NilValue then
        (R_GlobalEnv : SExpRec_pointer)
      else rho in
    let (S, c) := alloc_SExp S (make_SExpRec_clo R_NilValue formals body env) in
    result_success S c
  end.

(** * eval.c **)

(** The function names of this section corresponds to the function names
  in the file main/eval.c. **)

Definition CheckFormals S ls :=
  let error :=
    result_error S "[CheckFormals] invalid formal argument list." in
  let%success l := isList globals S ls using S in
  if l then
    fold%success
    along ls
    as _, ls_tag do
      read%defined ls_tag_ := ls_tag using S in
      ifb type ls_tag_ <> SymSxp then
        error
      else result_skip S using S, runs, globals in
      result_skip S
  else error.

Definition asym := [":=" ; "<-" ; "<<-" ; "-"]%string.

Definition PRIMVAL S x :=
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab runs S (prim_offset x_prim) using S in
  result_success S (fun_code x_fun).

Definition do_set S (call op args rho : SExpRec_pointer) : result SExpRec_pointer :=
  let wrong S :=
    let%success v := PRIMVAL S op using S in
    match nth_option v asym with
    | None => result_error S "[do_set] [PRIMVAL] out of bound in [asym]."
    | Some n => WrongArgCount S n
    end in
  ifb args = R_NilValue then wrong S
  else read%list _, args_list := args using S in
  ifb list_cdrval args_list = R_NilValue then wrong S
  else read%list _, args_cdr_list := list_cdrval args_list using S in
  ifb list_cdrval args_cdr_list <> R_NilValue then wrong S
  else
    let lhs := list_carval args_list in
    read%defined lhs_ := lhs using S in
    match type lhs_ with
    | StrSxp
    | SymSxp =>
      let%success lhs :=
        ifb type lhs_ = StrSxp then
          let%success lhs_char := STRING_ELT S lhs 0 using S in
          installTrChar globals runs S lhs_char
        else result_success S lhs using S in
      let%success rhs := eval globals runs S (list_carval args_cdr_list) rho using S in
      run%success INCREMENT_NAMED S rhs using S in
      read%prim _, op_prim := op using S in
      let%success c := read_R_FunTab runs S (prim_offset op_prim) using S in
      ifb fun_code c = 2 then
        read%env _, rho_env := rho using S in
        run%success setVar globals runs S lhs rhs (env_enclos rho_env) using S in
        result_success S rhs
      else
        run%success defineVar globals runs S lhs rhs rho using S in
        result_success S rhs
    | LangSxp => result_not_implemented "[do_set] applydefine"
    | _ => result_error S "[do_set] Invalid left-hand side to assignment."
    end.

Definition do_function S (call op args rho : SExpRec_pointer) : result SExpRec_pointer :=
  read%defined op_ := op using S in
  let%success op :=
    ifb type op_ = PromSxp then
      forcePromise globals runs S op
    else result_success S op using S in
  let%success len := R_length globals runs S args using S in
  ifb len < 2 then
    WrongArgCount S "function"
  else
    read%list _, args_list := args using S in
    run%success CheckFormals S (list_carval args_list) using S in
    read%list _, args_cdr_list := list_cdrval args_list using S in
    let%success rval :=
      mkCLOSXP S (list_carval args_list) (list_carval args_cdr_list) rho using S in
    read%list _, args_cdr_cdr_list := list_cdrval args_cdr_list using S in
    let srcref := list_carval args_cdr_cdr_list in
    read%defined srcref_ := srcref using S in
    run%success
      ifb type srcref_ = NilSxp then
        run%success
          setAttrib globals runs S rval R_SrcrefSymbol srcref using S in
        result_skip S
      else result_skip S using S in
    result_success S rval.


(** * names.c **)

(** The function names of this section corresponds to the function names
  in the file main/names.c. **)

(** In contrary to the original C, this function here takes as argument
  the structure of type [funtab_cell] in addition to its range in the
  array [R_FunTab]. **)
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

End Parameters.


(** * Closing the Loop **)

Local Instance funtab_cell_Inhab : Inhab funtab_cell.
  apply prove_Inhab. constructors; try typeclass; constructors; typeclass.
Defined.

Fixpoint runs max_step globals : runs_type :=
  match max_step with
  | O => {|
      runs_do_while := fun _ S _ _ _ => result_bottom S ;
      runs_eval := fun S _ _ => result_bottom S ;
      runs_inherits := fun S _ _ => result_bottom S ;
      runs_getAttrib := fun S _ _ => result_bottom S ;
      runs_R_cycle_detected := fun S _ _ => result_bottom S ;
      runs_stripAttrib := fun S _ _ => result_bottom S ;
      runs_R_FunTab := None
    |}
  | S max_step =>
    let wrap {A B : Type} (f : Globals -> runs_type -> B -> A) (x : B) : A :=
      (** It is important to take this additional parameter [x] as a parameter,
        to defer the computation of [runs max_step] when it is indeed needed.
        Without this, the application of [runs max_int] would overflow the
        stack. **)
      f globals (runs max_step globals) x in
    let wrap_dep {A : Type -> Type} (f : Globals -> runs_type -> forall B, A B) (T : Type) : A T :=
      (** A dependent version of [wrap]. **)
      f globals (runs max_step globals) T in {|
      runs_do_while := wrap_dep (fun _ => do_while) ;
      runs_eval := wrap eval ;
      runs_inherits := wrap inherits ;
      runs_getAttrib := wrap getAttrib ;
      runs_R_cycle_detected := wrap R_cycle_detected ;
      runs_stripAttrib := wrap stripAttrib ;
      runs_R_FunTab :=
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
              the computation of the next [R_FunTab]. **)
            f globals (runs max_step globals) S call op args rho in
          let rdecl name cfun code eval arity kind prec rightassoc :=
            decl name (wrap cfun) code eval arity (make_PPinfo kind prec rightassoc) in
          Some [
              rdecl "function" do_function 0 eval0 (-1)%Z PP_FUNCTION PREC_FN false ;
              rdecl "<-" do_set 1 eval100 (-1)%Z PP_ASSIGN PREC_LEFT true ;
              rdecl "=" do_set 3 eval100 (-1)%Z PP_ASSIGN PREC_EQ true ;
              rdecl "<<-" do_set 2 eval100 (-1)%Z PP_ASSIGN2 PREC_LEFT true
            ]%string
        end
    |}
  end.

