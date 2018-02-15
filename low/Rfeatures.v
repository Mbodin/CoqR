(** Rfeatures.
  A Coq formalisation of additionnal functions of R from its C code. **)

Set Implicit Arguments.
Require Import Ascii.
Require Export Rcore.


Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.

Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


(** * errors.c **)

(** The function names of this section corresponds to the function names
  in the file main/errors.c. **)

Definition WrongArgCount A S s : result A :=
  add%stack "WrongArgCount" in
  result_error S ("Incorrect number of arguments to " ++ s ++ ".").
Arguments WrongArgCount [A].


(** * util.c **)

(** The function names of this section corresponds to the function names
  in the file main/util.c. **)

(** There is a macro replacing every call to [checkArity (a, b)] to
  [Rf_checkArityCall (a, b, call)]. This macro is not convertible in
  Coq as the [call] argument is not available in scope. We thus unfold
  this macro during the translation. **)
Definition Rf_checkArityCall S (op args call : SEXP) :=
  add%stack "Rf_checkArityCall" in
  let%success arity := PRIMARITY runs S op using S in
  let%success len := R_length globals runs S args using S in
  ifb arity >= 0 /\ arity <> len then
    if%success PRIMINTERNAL runs S op using S then
      result_error S "An argument has been passed to an element of .Internal without its requirements."
    else result_error S "An argument has been passed to something without its requirements."
  else result_skip S.

Definition Rf_check1arg S (arg call : SEXP) formal :=
  add%stack "Rf_check1arg" in
  read%list _, _, arg_tag := arg using S in
  ifb arg_tag = R_NilValue then
    result_skip S
  else
    let%success printname := PRINTNAME S arg_tag using S in
    let%success supplied := CHAR S printname using S in
    ifb supplied <> formal then
     result_error S "Supplied argument name does not match expected name."
    else result_skip S.


(** * attrib.c **)

(** The function names of this section corresponds to the function names
  in the file main/attrib.c. **)

(** This enumeration is used in a local definition. **)
Inductive enum_none_partial_partial2_full :=
  | enum_none
  | enum_partial
  | enum_partial2
  | enum_full.

Instance enum_none_partial_partial2_full_Comparable : Comparable enum_none_partial_partial2_full.
  prove_comparable_trivial_inductive.
Defined.

Definition do_attr S (call op args env : SEXP) : result SEXP :=
  add%stack "do_attr" in
  (** The initialisation of [do_attr_formals] is done in [do_attr_init] in Rinit. **)
  let%success nargs := R_length globals runs S args using S in
  let%success argList := matchArgs globals runs S do_attr_do_attr_formals args call using S in
  ifb nargs < 2 \/ nargs > 3 then
    result_error S "Either 2 or 3 arguments are required."
  else
    read%list argList_car, argList_cdr, _ := argList using S in
    let s := argList_car in
    read%list argList_cdr_car, _, _ := argList_cdr using S in
    let t := argList_cdr_car in
    let%success t_str := isString S t using S in
    if negb t_str then
      result_error S "‘which’ must be of mode character."
    else
      let%success t_len := R_length globals runs S t using S in
      ifb t_len <> 1 then
        result_error S "Exactly one attribute ‘which’ must be given."
      else
        let%success s_type := TYPEOF S s using S in
        ifb s_type = EnvSxp then
          result_not_implemented "R_checkStack"
        else
          let%success exact :=
            ifb nargs = 3 then
              read%list _, args_cdr, _ := args using S in
              read%list _, args_cdr_cdr, _ := args_cdr using S in
              read%list args_cdr_cdr_car, _, _ := args_cdr_cdr using S in
              let%success exact := asLogical globals S args_cdr_cdr_car using S in
              ifb exact = NA_LOGICAL then
                result_success S false
              else result_success S (decide (exact <> 0))
            else result_success S false using S in
          let%success t_0 := STRING_ELT S t 0 using S in
          ifb t_0 = NA_STRING then
            result_success S (R_NilValue : SEXP)
          else
            let%success str := translateChar S t_0 using S in
            let%success alist := ATTRIB S s using S in
            let%success (vmatch, tag) :=
              fold%return (vmatch, tag) := (enum_none, R_NilValue : SEXP)
              along alist
              as _, alist_tag do
                let tmp := alist_tag in
                let%success tmp_name := PRINTNAME S tmp using S in
                let%success s := CHAR S tmp_name using S in
                ifb s = str then
                  result_rreturn S (enum_full, tmp)
                else if String.prefix str s then
                  ifb vmatch = enum_partial \/ vmatch = enum_partial2 then
                    result_rsuccess S (enum_partial2, tag)
                  else result_rsuccess S (enum_partial, tmp)
                else result_rsuccess S (vmatch, tag) using S, runs, globals in
              result_success S (vmatch, tag) using S in
            ifb vmatch = enum_partial2 then
              result_success S (R_NilValue : SEXP)
            else
              let%exit (vmatch, tag) :=
                ifb vmatch <> enum_full /\ str = "names"%string then
                  result_rsuccess S (enum_full, R_NamesSymbol : SEXP)
                else ifb vmatch <> enum_full /\ String.prefix "names" str then
                  ifb vmatch = enum_none /\ ~ exact then
                    let tag := R_NamesSymbol : SEXP in
                    let%success t := getAttrib globals runs S s tag using S in
                    (* A potential warning has been formalised out here. *)
                    result_rreturn S t
                  else
                    let%success tag_name := PRINTNAME S tag using S in
                    let%success tag_name_ := CHAR S tag_name using S in
                    ifb vmatch = enum_partial /\ tag_name_ = "names"%string then
                      let%success t := getAttrib globals runs S s R_NamesSymbol using S in
                      ifb t <> R_NilValue then
                        result_rreturn S (R_NilValue : SEXP)
                      else result_rsuccess S (vmatch, tag)
                    else result_rsuccess S (vmatch, tag)
                else result_rsuccess S (vmatch, tag) using S in
              ifb vmatch = enum_none \/ (exact /\ vmatch <> enum_full) then
                result_success S (R_NilValue : SEXP)
              else
                (* A potential warning has been formalised out here. *)
                getAttrib globals runs S s tag.

Definition do_attrgets S (call op args env : SEXP) : result SEXP :=
  add%stack "do_attrgets" in
  run%success Rf_checkArityCall S op args call using S in
  let%success op_val := PRIMVAL runs S op using S in
  ifb op_val <> 0 then
    let%success input := allocVector globals S StrSxp 1 using S in
    read%list _, args_cdr, _ := args using S in
    read%list args_cdr_car, _, _ := args_cdr using S in
    let nlist := args_cdr_car in
    run%success
      if%success isSymbol S nlist using S then
        let%success nlist_name := PRINTNAME S nlist using S in
        SET_STRING_ELT S input 0 nlist_name
      else if%success isString S nlist using S then
        let%success nlist_0 := STRING_ELT S nlist 0 using S in
        SET_STRING_ELT S input 0 nlist_0
      else result_error S "Invalid type for slot name." using S in
    set%car args_cdr := input using S in
    let%success (disp, ans) :=
      DispatchOrEval globals runs S call op "@<-" args env false false using S in
    if disp then
      result_success S ans
    else
      read%list ans_car, ans_cdr, _ := ans using S in
      let obj := ans_car in
      read%list _, ans_cdr_cdr, _ := ans_cdr using S in
      read%list ans_cdr_cdr_car, _, _ := ans_cdr_cdr using S in
      let value := ans_cdr_cdr_car in
      result_not_implemented "check_slot_assign"
  else
    read%list args_car, args_cdr, _ := args using S in
    let obj := args_car in
    let%success obj :=
      if%success MAYBE_SHARED S obj using S then
        shallow_duplicate globals runs S obj
      else result_success S obj using S in
    (** The initialisation of [do_attrgets_formals] is done in [do_attrgets_init] in Rinit. **)
    let%success argList :=
      matchArgs globals runs S do_attrgets_do_attrgets_formals args call using S in
    read%list _, argList_cdr, _ := argList using S in
    read%list argList_cdr_car, _, _ := argList_cdr using S in
    let name := argList_cdr_car in
    let%success name_valid := isValidString globals S name using S in
    let%success name_0 := STRING_ELT S name 0 using S in
    ifb ~ name_valid \/ name_0 = NA_STRING then
      result_error S "‘name’ must be non-null character string."
    else
      read%list _, args_cdr_cdr, _ := args_cdr using S in
      read%list args_cdr_cdr_car, _, _ := args_cdr_cdr using S in
      run%success setAttrib globals runs S obj name args_cdr_cdr_car using S in
      run%success SETTER_CLEAR_NAMED S obj using S in
      result_success S obj.


(** * coerce.c **)

(** The function names of this section corresponds to the function names
  in the file main/coerce.c. **)

Definition do_typeof S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_typeof" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, _, _ := args using S in
  let%success t := TYPEOF S args_car using S in
  type2rstr globals S t.

Definition do_is S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_is" in
  run%success Rf_checkArityCall S op args call using S in
  run%success Rf_check1arg S args call "x" using S in
  let%success op_val := PRIMVAL runs S op using S in
  read%list args_car, _, _ := args using S in
  let%success args_car_obj := isObject S args_car using S in
  run%exit
    ifb op_val >= 100 /\ op_val < 200 /\ args_car_obj then
      let nm :=
        (ifb op_val = 100 then "is.numeric"
        else ifb op_val = 101 then "is.matrix"
        else ifb op_val = 102 then "is.array"
        else "")%string in
      let%success (disp, ans) :=
        DispatchOrEval globals runs S call op nm args rho false true using S in
      if disp then
        result_rreturn S ans
      else result_rskip S
    else result_rskip S using S in
  let%success ans := allocVector globals S LglSxp 1 using S in
  run%success
    ifb op_val = NilSxp then
      let%success isn := isNull S args_car using S in
      write%Logical ans at 0 := isn using S in
      result_skip S
    else ifb op_val = LglSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = LglSxp) using S in
      result_skip S
    else ifb op_val = IntSxp then
      let%success t := TYPEOF S args_car using S in
      let%success inh := inherits globals runs S args_car "factor" using S in
      write%Logical ans at 0 := decide (t = IntSxp /\ ~ inh) using S in
      result_skip S
    else ifb op_val = RealSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = RealSxp) using S in
      result_skip S
    else ifb op_val = CplxSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = CplxSxp) using S in
      result_skip S
    else ifb op_val = StrSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = StrSxp) using S in
      result_skip S
    else ifb op_val = SymSxp then
      let%success s4 := IS_S4_OBJECT S args_car using S in
      let%success t := TYPEOF S args_car using S in
      ifb s4 /\ t = S4Sxp then
        result_not_implemented "R_getS4DataSlot"
      else
        write%Logical ans at 0 := decide (t = SymSxp) using S in
        result_skip S
    else ifb op_val = EnvSxp then
      let%success s4 := IS_S4_OBJECT S args_car using S in
      let%success t := TYPEOF S args_car using S in
      ifb s4 /\ t = S4Sxp then
        result_not_implemented "R_getS4DataSlot"
      else
        write%Logical ans at 0 := decide (t = EnvSxp) using S in
        result_skip S
    else ifb op_val = VecSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = VecSxp \/ t = ListSxp) using S in
      result_skip S
    else ifb op_val = ListSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = ListSxp \/ t = NilSxp) using S in
      result_skip S
    else ifb op_val = ExprSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = ExprSxp) using S in
      result_skip S
    else ifb op_val = RawSxp then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = RawSxp) using S in
      result_skip S
    else ifb op_val = 50 then
      let%success obj := OBJECT S args_car using S in
      write%Logical ans at 0 := obj using S in
      result_skip S
    else ifb op_val = 51 then
      let%success s4 := IS_S4_OBJECT S args_car using S in
      write%Logical ans at 0 := s4 using S in
      result_skip S
    else ifb op_val = 100 then
      let%success isn := isNumeric globals runs S args_car using S in
      let%success isl := isLogical S args_car using S in
      write%Logical ans at 0 := decide (isn /\ ~ isl) using S in
      result_skip S
    else ifb op_val = 101 then
      result_not_implemented "is.matrix."
    else ifb op_val = 102 then
      let%success ia := isArray globals runs S args_car using S in
      write%Logical ans at 0 := ia using S in
      result_skip S
    else ifb op_val = 200 then
      let%success t := TYPEOF S args_car using S in
      match t with
        | NilSxp
        | CharSxp
        | LglSxp
        | IntSxp
        | RealSxp
        | CplxSxp
        | StrSxp
        | RawSxp =>
          write%Logical ans at 0 := true using S in
          result_skip S
        | _ =>
          write%Logical ans at 0 := false using S in
          result_skip S
      end
    else ifb op_val = 201 then
      let%success t := TYPEOF S args_car using S in
      match t with
        | VecSxp
        | ListSxp
        | CloSxp
        | EnvSxp
        | PromSxp
        | LangSxp
        | SpecialSxp
        | BuiltinSxp
        | DotSxp
        | AnySxp
        | ExprSxp =>
          write%Logical ans at 0 := true using S in
          result_skip S
        | _ =>
          write%Logical ans at 0 := false using S in
          result_skip S
      end
    else ifb op_val = 300 then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = LangSxp) using S in
      result_skip S
    else ifb op_val = 301 then
      let%success t := TYPEOF S args_car using S in
      write%Logical ans at 0 := decide (t = SymSxp \/ t = LangSxp \/ t = ExprSxp) using S in
      result_skip S
    else ifb op_val = 302 then
      result_not_implemented "is.function."
    else ifb op_val = 999 then
      result_error S "Unimplemented type single."
    else result_error S "Unimplemented predicate." using S in
  result_success S ans.

Definition do_isna S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_isna" in
  run%success Rf_checkArityCall S op args call using S in
  run%success Rf_check1arg S args call "x" using S in
  let%success (disp, ans) :=
    DispatchOrEval globals runs S call op "is.na" args rho true true using S in
  if disp then
    result_success S ans
  else
    let args := ans in
    read%list args_car, _, _ := args using S in
    let x := args_car in
    let%success n := xlength globals runs S x using S in
    let%success ans := allocVector globals S LglSxp n using S in
    let%success x_type := TYPEOF S x using S in
    run%success
      let LIST_VEC_NA S s i :=
        let%success s_vec := isVector S s using S in
        let%success s_len := R_length globals runs S s using S in
        ifb ~ s_vec \/ s_len <> 1 then
          write%Logical ans at i := false using S in
          result_skip S
        else
          let%success s_type := TYPEOF S s using S in
          match s_type with
          | LglSxp
          | IntSxp =>
            let%success s_0 := INTEGER_ELT S s 0 using S in
            write%Logical ans at i := decide (s_0 = NA_INTEGER) using S in
            result_skip S
          | RealSxp =>
            let%success s_0 := REAL_ELT S s 0 using S in
            write%Logical ans at i := ISNAN s_0 using S in
            result_skip S
          | StrSxp =>
            let%success s_0 := STRING_ELT S s 0 using S in
            write%Logical ans at i := decide (s_0 = NA_STRING) using S in
            result_skip S
          | CplxSxp =>
            let%success v := COMPLEX_ELT S s 0 using S in
            write%Logical ans at i := ISNAN (Rcomplex_r v) || ISNAN (Rcomplex_i v) using S in
            result_skip S
          | _ =>
            write%Logical ans at i := false using S in
            result_skip S
          end in
      match x_type with
      | LglSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := LOGICAL_ELT S x i using S in
          write%Logical ans at i := decide (x_i = NA_LOGICAL) using S in
          result_skip S using S
      | IntSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := INTEGER_ELT S x i using S in
          write%Logical ans at i := decide (x_i = NA_INTEGER) using S in
          result_skip S using S
      | RealSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := REAL_ELT S x i using S in
          write%Logical ans at i := ISNAN x_i using S in
          result_skip S using S
      | CplxSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := COMPLEX_ELT S x i using S in
          write%Logical ans at i := ISNAN (Rcomplex_r x_i) || ISNAN (Rcomplex_i x_i) using S in
          result_skip S using S
      | StrSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := STRING_ELT S x i using S in
          write%Logical ans at i := decide (x_i = NA_STRING) using S in
          result_skip S using S
      | ListSxp =>
        do%success x := x
        for i from 0 to n - 1 do
          read%list x_car, x_cdr, _ := x using S in
          run%success LIST_VEC_NA S x_car i using S in
          result_success S x_cdr using S in
        result_skip S
      | VecSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success s := VECTOR_ELT S x i using S in
          LIST_VEC_NA S s i using S
      | RawSxp =>
        do%let
        for i from 0 to n - 1 do
          write%Logical ans at i := false using S in
          result_skip S using S
      | NilSxp => result_skip S
      | _ => result_error S "Non-(list or vector)."
      end using S in
    run%success copyDimAndNames globals runs S x ans using S in
    result_success S ans.


Definition do_isnan S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_isnan" in
  run%success Rf_checkArityCall S op args call using S in
  run%success Rf_check1arg S args call "x" using S in
  let%success (disp, ans) :=
    DispatchOrEval globals runs S call op "is.na" args rho true true using S in
  if disp then
    result_success S ans
  else
    let args := ans in
    read%list args_car, _, _ := args using S in
    let x := args_car in
    let%success n := xlength globals runs S x using S in
    let%success ans := allocVector globals S LglSxp n using S in
    let%success x_type := TYPEOF S x using S in
    run%success
      match x_type with
      | StrSxp
      | RawSxp
      | NilSxp
      | LglSxp
      | IntSxp =>
        do%let
        for i from 0 to n - 1 do
          write%Logical ans at i := false using S in
          result_skip S using S
      | RealSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := REAL_ELT S x i using S in
          write%Logical ans at i := R_IsNaN x_i using S in
          result_skip S using S
      | CplxSxp =>
        do%let
        for i from 0 to n - 1 do
          let%success x_i := COMPLEX_ELT S x i using S in
          write%Logical ans at i := R_IsNaN (Rcomplex_r x_i) || R_IsNaN (Rcomplex_i x_i) using S in
          result_skip S using S
      | _ => result_error S "Default method not implemented for this type."
      end using S in
    run%success copyDimAndNames globals runs S x ans using S in
    result_success S ans.

Definition do_isvector S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_isvector" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  let x := args_car in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let%success args_cdr_car_str := isString S args_cdr_car using S in
  let%success args_cdr_car_len := LENGTH globals S args_cdr_car using S in
  ifb ~ args_cdr_car_str \/ args_cdr_car_len <> 1 then
    result_error S "Invalid ‘mode’ argument."
  else
    let%success args_cdr_car_0 := STRING_ELT S args_cdr_car 0 using S in
    let%success stype := CHAR S args_cdr_car_0 using S in
    let stype := ifb stype = "name"%string then "symbol"%string else stype in
    let%success ans := allocVector globals S LglSxp 1 using S in
    run%success
      ifb stype = "any"%string then
        let%success x_vec := isVector S x using S in
        write%Logical ans at 0 := x_vec using S in
        result_skip S
      else ifb stype = "numeric"%string then
        let%success x_vec := isVector S x using S in
        let%success x_lgl := isLogical S x using S in
        write%Logical ans at 0 := x_vec && negb x_lgl using S in
        result_skip S
      else result_not_implemented "type2char" using S in
    run%success
      read%Logical ans_0 := ans at 0 using S in
      let%success args_car_attr := ATTRIB S args_car using S in
      ifb ans_0 <> 0 /\ args_car_attr <> R_NilValue then
        let a := args_car_attr in
        fold%let
        along a
        as _, a_tag do
          ifb a_tag <> R_NamesSymbol then
            write%Logical ans at 0 := false using S in
            result_skip S
          else result_skip S using S, runs, globals
      else result_skip S using S in
    result_success S ans.


(** * envir.c **)

(** The function names of this section corresponds to the function names
  in the file main/envir.c. **)

Definition do_missing S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_missing" in
  run%success Rf_checkArityCall S op args call using S in
  run%success Rf_check1arg S args call "x" using S in
  read%list args_car, _, _ := args using S in
  let%success sym :=
    let sym := args_car in
    let%success sym_str := isString S sym using S in
    let%success sym_len := R_length globals runs S sym using S in
    ifb sym_str /\ sym_len = 1 then
      read%Pointer args_car_0 := args_car at 0 using S in
      installTrChar globals runs S args_car_0
    else result_success S sym using S in
  let s := sym in
  let%success sym_sym := isSymbol S sym using S in
  if negb sym_sym then
    result_error S "Invalid use."
  else
    let%success (ddv, sym) :=
      if%success DDVAL S sym using S then
        let%success ddv := ddVal S sym using S in
        result_success S (ddv, R_DotsSymbol : SEXP)
      else result_success S (0, sym) using S in
    let%success t := findVarLocInFrame globals runs S rho sym using S in
    let%success rval := allocVector globals S LglSxp 1 using S in
    ifb t <> R_NilValue then
      read%list t_car, _, _ := t using S in
      let%exit t :=
        if%success DDVAL S s using S then
          let%success t_car_len := R_length globals runs S t_car using S in
          ifb t_car_len < ddv \/ t_car = R_MissingArg then
            write%Logical rval at 0 := 1 using S in
            result_rreturn S rval
          else
            let%success t := nthcdr globals runs S t_car (ddv - 1) using S in
            result_rsuccess S t
        else result_rsuccess S t using S in
      run%exit
        let%success t_mis := MISSING S t using S in
        ifb t_mis <> 0 \/ t_car = R_MissingArg then
          write%Logical rval at 0 := 1 using S in
          result_rreturn S rval
        else result_rskip S using S in
      (** This is the translation of the [havebinding] label. **)
      let t := t_car in
      let%success t_type := TYPEOF S t using S in
      ifb t_type <> PromSxp then
        write%Logical rval at 0 := 0 using S in
        result_success S rval
      else
        let%success t := findRootPromise globals runs S t using S in
        let%success t_is :=
          let%success t := PREXPR globals S t using S in
          isSymbol S t using S in
        if negb t_is then
          write%Logical rval at 0 := 0 using S in
          result_success S rval
        else
          let%success t_expr := PREXPR globals S t using S in
          let%success t_env :=
             read%prom _, t_prom := t using S in
             result_success S (prom_env t_prom) using S in
          let%success ism := R_isMissing globals runs S t_expr t_env using S in
          write%Logical rval at 0 := ism using S in
          result_success S rval
    else result_error S "It can only be used for arguments.".


(** * bind.c **)

(** The function names of this section corresponds to the function names
  in the file main/bind.c. **)

Definition HasNames S x :=
  add%stack "HasNames" in
  if%success isVector S x using S then
    let%success att := getAttrib globals runs S x R_NamesSymbol using S in
    let%success att_n := isNull S att using S in
    if negb att_n then
      result_success S true
    else result_success S false
  else if%success isList globals S x using S then
    do%return x := x
    while
        let%success x_n := isNull S x using S in
        result_success S (negb x_n) do
      read%list _, x_cdr, x_tag := x using S in
      let%success x_tag_n := isNull S x_tag using S in
      if negb x_tag_n then
        result_rreturn S true
      else result_rsuccess S x_cdr using S, runs in
    result_success S false
  else result_success S false.

Definition AnswerType S x (recurse usenames : bool) data (call : SEXP) :=
  add%stack "AnswerType" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp =>
    result_success S data
  | RawSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 0 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | LglSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 1 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | IntSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 4 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | RealSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 5 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | CplxSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 6 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | StrSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 7 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let%success len := XLENGTH S x using S in
    let data :=
      BindData_with_ans_length data (BindData_ans_length data + len) in
    result_success S data
  | SymSxp
  | LangSxp =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let data :=
      BindData_with_ans_length data (1 + BindData_ans_length data) in
    result_success S data
  | VecSxp
  | ExprSxp =>
    if recurse then
      let%success n := XLENGTH S x using S in
      let%success data :=
        let%success attr := getAttrib globals runs S x R_NamesSymbol using S in
        let%success attr_n := isNull S attr using S in
        ifb usenames /\ BindData_ans_nnames data = 0 /\ ~ attr_n then
          result_success S (BindData_with_ans_nnames data 1)
        else result_success S data using S in
      do%let data := data
      for i from 0 to n - 1 do
        let%success x_i := VECTOR_ELT S x i using S in
        let%success data :=
          ifb usenames /\ BindData_ans_nnames data = 0 then
            let%success hn := HasNames S x_i using S in
            result_success S (BindData_with_ans_nnames data hn)
          else result_success S data using S in
        runs_AnswerType runs S x_i recurse usenames data call using S
    else
      let data :=
        ifb x_t = ExprSxp then
          BindData_with_ans_flags data
            (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data))
        else
          BindData_with_ans_flags data
            (@write_nbit 10 8 ltac:(nbits_ok) true (BindData_ans_flags data)) in
      let%success len := XLENGTH S x using S in
      let data :=
        BindData_with_ans_length data (BindData_ans_length data + len) in
      result_success S data
  | ListSxp =>
    if recurse then
      fold%let data := data
      along x
      as x_car, x_tag do
        let%success data :=
          ifb usenames /\ BindData_ans_nnames data = 0 then
            let%success x_tag_n := isNull S x_tag using S in
            if negb x_tag_n then
              result_success S (BindData_with_ans_nnames data 1)
            else
              let%success hn := HasNames S x_car using S in
              result_success S (BindData_with_ans_nnames data hn)
          else result_success S data using S in
        runs_AnswerType runs S x_car recurse usenames data call using S, runs, globals
    else
      let data :=
        BindData_with_ans_flags data
          (@write_nbit 10 8 ltac:(nbits_ok) true (BindData_ans_flags data)) in
      let%success len := XLENGTH S x using S in
      let data :=
        BindData_with_ans_length data (BindData_ans_length data + len) in
      result_success S data
  | _ =>
    let data :=
      BindData_with_ans_flags data
        (@write_nbit 10 9 ltac:(nbits_ok) true (BindData_ans_flags data)) in
    let data :=
      BindData_with_ans_length data (1 + BindData_ans_length data) in
    result_success S data
  end.

Definition c_Extract_opt S (ans call : SEXP) :=
  add%stack "c_Extract_opt" in
  fold%success (recurse, usenames, ans, last, n_recurse, n_usenames) := (false, true, ans, NULL, 0, 0)
  along ans as a, a_, a_list do
    let n := list_tagval a_list in
    let next := list_cdrval a_list in
    let a_car := list_carval a_list in
    if%success
        ifb n <> R_NilValue then
          pmatch S R_RecursiveSymbol n true
        else result_success S false using S then
      ifb n_recurse = 1 then
        result_error S "Repeated argument ‘recursive’."
      else
        let n_recurse := 1 + n_recurse in
        let%success v := asLogical globals S a_car using S in
        let%success recurse :=
          ifb v <> NA_INTEGER then
            result_success S (decide (v <> 0))
          else result_success S recurse using S in
        let%success ans :=
          ifb last = NULL then
            result_success S next
          else
            set%cdr last := next using S in
            result_success S ans using S in
        result_success S (recurse, usenames, ans, last, n_recurse, n_usenames)
    else if%success
        ifb n <> R_NilValue then
          pmatch S R_UseNamesSymbol n true
        else result_success S false using S then
      ifb n_usenames = 1 then
        result_error S "Repeated argument ‘use.names’."
      else
        let n_usenames := 1 + n_usenames in
        let%success v := asLogical globals S a_car using S in
        let%success usenames :=
          ifb v <> NA_INTEGER then
            result_success S (decide (v <> 0))
          else result_success S usenames using S in
        let%success ans :=
          ifb last = NULL then
            result_success S next
          else
            set%cdr last := next using S in
            result_success S ans using S in
        result_success S (recurse, usenames, ans, last, n_recurse, n_usenames)
    else result_success S (recurse, usenames, ans, a, n_recurse, n_usenames) using S, runs, globals in
  result_success S (ans, recurse, usenames).

Definition ListAnswer S x (recurse : bool) data call :=
  add%stack "ListAnswer" in
  let LIST_ASSIGN S data x :=
    run%success SET_VECTOR_ELT S (BindData_ans_ptr data) (BindData_ans_length data) x using S in
    result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i using S in
      LIST_ASSIGN S data (ScalarLogical globals x_i) using S
  | RawSxp => result_not_implemented "Raw case."
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer x_i := x at i using S in
      let (S, si) := ScalarInteger globals S x_i in
      LIST_ASSIGN S data si using S
  | RealSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i using S in
      let (S, sr) := ScalarReal globals S x_i in
      LIST_ASSIGN S data sr using S
  | CplxSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Complex x_i := x at i using S in
      let (S, sc) := ScalarComplex globals S x_i in
      LIST_ASSIGN S data sc using S
  | StrSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := STRING_ELT S x i using S in
      let%success ss := ScalarString globals S x_i using S in
      LIST_ASSIGN S data ss using S
  | VecSxp
  | ExprSxp =>
    let%success len := XLENGTH S x using S in
    if recurse then
      do%let data := data
      for i from 0 to len - 1 do
        let%success x_i := VECTOR_ELT S x i using S in
        runs_ListAnswer runs S x_i recurse data call using S
    else
      do%let data := data
      for i from 0 to len - 1 do
        let%success x_i := VECTOR_ELT S x i using S in
        let%success x_i := lazy_duplicate S x_i using S in
        LIST_ASSIGN S data x_i using S
  | ListSxp =>
    if recurse then
      fold%let data := data
      along x
      as x_car, _ do
        runs_ListAnswer runs S x_car recurse data call using S, runs, globals
    else
      fold%let data := data
      along x
      as x_car, _ do
        let%success x_car := lazy_duplicate S x_car using S in
        LIST_ASSIGN S data x_car using S, runs, globals
  | _ =>
    let%success x := lazy_duplicate S x using S in
    LIST_ASSIGN S data x
  end.

Definition StringAnswer S x data call :=
  add%stack "StringAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_StringAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_StringAnswer runs S x_i data call using S
  | _ =>
    let%success x := coerceVector globals runs S x StrSxp using S in
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := STRING_ELT S x i using S in
      run%success SET_STRING_ELT S (BindData_ans_ptr data) (BindData_ans_length data) x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  end.

Definition LogicalAnswer S x data call :=
  add%stack "LogicalAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_LogicalAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_LogicalAnswer runs S x_i data call using S
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i using S in
      write%Logical BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer v := x at i using S in
      write%Logical BindData_ans_ptr data at BindData_ans_length data :=
        ifb v = NA_INTEGER then NA_LOGICAL else decide (v <> 0) using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition IntegerAnswer S x data call :=
  add%stack "IntegerAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_IntegerAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_IntegerAnswer runs S x_i data call using S
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical x_i := x at i using S in
      write%Integer BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer x_i := x at i using S in
      write%Integer BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition RealAnswer S x data call :=
  add%stack "RealAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_RealAnswer runs S x_car data call using S, runs, globals
  | VecSxp
  | ExprSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_RealAnswer runs S x_i data call using S
  | RealSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i using S in
      write%Real BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical xi := x at i using S in
      ifb xi = NA_LOGICAL then
        write%Real BindData_ans_ptr data at BindData_ans_length data := NA_REAL using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Real BindData_ans_ptr data at BindData_ans_length data := xi using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer xi := x at i using S in
      ifb xi = NA_INTEGER then
        write%Real BindData_ans_ptr data at BindData_ans_length data := NA_REAL using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Real BindData_ans_ptr data at BindData_ans_length data := xi using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition ComplexAnswer S x data call :=
  add%stack "ComplexAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_ComplexAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_ComplexAnswer runs S x_i data call using S
  | RealSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Real x_i := x at i using S in
      write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex x_i 0 using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | CplxSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Complex x_i := x at i using S in
      write%Complex BindData_ans_ptr data at BindData_ans_length data := x_i using S in
      result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | LglSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Logical xi := x at i using S in
      ifb xi = NA_LOGICAL then
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex NA_REAL NA_REAL using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex xi 0 using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | IntSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      read%Integer xi := x at i using S in
      ifb xi = NA_INTEGER then
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex NA_REAL NA_REAL using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data))
      else
        write%Complex BindData_ans_ptr data at BindData_ans_length data := make_Rcomplex xi 0 using S in
        result_success S (BindData_with_ans_length data (1 + BindData_ans_length data)) using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition RawAnswer S x data call :=
  add%stack "RawAnswer" in
  let%success x_t := TYPEOF S x using S in
  match x_t with
  | NilSxp => result_success S data
  | ListSxp =>
    fold%let data := data
    along x
    as x_car, _ do
      runs_RawAnswer runs S x_car data call using S, runs, globals
  | ExprSxp
  | VecSxp =>
    let%success len := XLENGTH S x using S in
    do%let data := data
    for i from 0 to len - 1 do
      let%success x_i := VECTOR_ELT S x i using S in
      runs_RawAnswer runs S x_i data call using S
  | RawSxp => result_not_implemented "Raw case."
  | _ => result_error S "Unimplemented type."
  end.

Definition do_c_dftl S (call op args env : SEXP) : result SEXP :=
  add%stack "do_c_dftl" in
  let%success (ans, recurse, usenames) := c_Extract_opt S args call using S in
  let data := make_BindData (@nat_to_nbits 10 0 ltac:(nbits_ok)) NULL 0 NULL 0 in
  fold%success data := data
  along args
  as t_car, t_tag do
    let%success data :=
      ifb usenames /\ BindData_ans_nnames data = 0 then
        let%success t_tag_n := isNull S t_tag using S in
        if negb t_tag_n then
          result_success S (BindData_with_ans_nnames data 1)
        else
          let%success hn := HasNames S t_car using S in
          result_success S (BindData_with_ans_nnames data hn)
      else result_success S data using S in
    AnswerType S t_car recurse usenames data call using S, runs, globals in
  let mode :=
    if nth_bit 9 (BindData_ans_flags data) ltac:(nbits_ok) then ExprSxp
    else if nth_bit 8 (BindData_ans_flags data) ltac:(nbits_ok) then VecSxp
    else if nth_bit 7 (BindData_ans_flags data) ltac:(nbits_ok) then StrSxp
    else if nth_bit 6 (BindData_ans_flags data) ltac:(nbits_ok) then CplxSxp
    else if nth_bit 5 (BindData_ans_flags data) ltac:(nbits_ok) then RealSxp
    else if nth_bit 4 (BindData_ans_flags data) ltac:(nbits_ok) then IntSxp
    else if nth_bit 1 (BindData_ans_flags data) ltac:(nbits_ok) then LglSxp
    else if nth_bit 0 (BindData_ans_flags data) ltac:(nbits_ok) then RawSxp
    else NilSxp in
  let%success ans := allocVector globals S mode (BindData_ans_length data) using S in
  let data := BindData_with_ans_ptr data ans in
  let data := BindData_with_ans_length data 0 in
  let t := args in
  let%success data :=
    ifb mode = VecSxp \/ mode = ExprSxp then
      let%success data :=
        if negb recurse then
          fold%let data := data
          along args
          as args_car, _ do
            ListAnswer S args_car false data call using S, runs, globals
        else ListAnswer S args recurse data call using S in
      let%success len := xlength globals runs S ans using S in
      result_success S (BindData_with_ans_length data len)
    else ifb mode = StrSxp then
      StringAnswer S args data call
    else ifb mode = CplxSxp then
      ComplexAnswer S args data call
    else ifb mode = RealSxp then
      RealAnswer S args data call
    else ifb mode = RawSxp then
      RawAnswer S args data call
    else ifb mode = LglSxp then
      LogicalAnswer S args data call
    else IntegerAnswer S args data call using S in
  let args := t in
  let%success data :=
    ifb BindData_ans_nnames data <> 0 /\ BindData_ans_length data > 0 then
      let%success data_ans_names := allocVector globals S StrSxp (BindData_ans_length data) using S in
      let data := BindData_with_ans_names data data_ans_names in
      fold%success (nameData, data) := (tt, data)
      along args
      as args_car, _ do
        result_not_implemented "NewExtractNames" using S, runs, globals in
      run%success setAttrib globals runs S ans R_NamesSymbol (BindData_ans_names data) using S in
      result_success S data
    else result_success S data using S in
  result_success S ans.

Definition do_c S (call op args env : SEXP) : result SEXP :=
  add%stack "do_c" in
  run%success Rf_checkArityCall S op args call using S in
  let%success (disp, ans) :=
    DispatchAnyOrEval globals runs S call op "c" args env true true using S in
  if disp then result_success S ans
  else do_c_dftl S call op ans env.



(** * eval.c **)

(** The function names of this section corresponds to the function names
  in the file main/eval.c. **)

Definition CheckFormals S ls :=
  add%stack "CheckFormals" in
  if%success isList globals S ls using S then
    fold%success
    along ls
    as _, ls_tag do
      let%success ls_tag_type := TYPEOF S ls_tag using S in
      ifb ls_tag_type <> SymSxp then
        result_error S "Invalid formal argument list (not a symbol)."
      else result_skip S using S, runs, globals in
    result_skip S
  else result_error S "Invalid formal argument list (not a list).".

Definition asym := [":=" ; "<-" ; "<<-" ; "="]%string.

Definition lookupAssignFcnSymbol S vfun :=
  add%stack "lookupAssignFcnSymbol" in
  findVarInFrame globals runs S R_ReplaceFunsTable vfun.

Definition enterAssignFcnSymbol S vfun val :=
  add%stack "enterAssignFcnSymbol" in
  defineVar globals runs S vfun val R_ReplaceFunsTable.

Definition installAssignFcnSymbol S vfun :=
  add%stack "installAssignFcnSymbol" in
  let%success fu_name := PRINTNAME S vfun using S in
  let%success fu_name_ := CHAR S fu_name using S in
  let%success val := install globals runs S (fu_name_ ++ "<-") using S in
  run%success enterAssignFcnSymbol S vfun val using S in
  result_success S val.

Definition getAssignFcnSymbol S (vfun : SEXP) :=
  add%stack "getAssignFcnSymbol" in
  ifb vfun = R_SubsetSym then
    result_success S (R_SubassignSym : SEXP)
  else ifb vfun = R_Subset2Sym then
    result_success S (R_Subassign2Sym : SEXP)
  else ifb vfun = R_DollarSymbol then
    result_success S (R_DollarGetsSymbol : SEXP)
  else
    let%success val := lookupAssignFcnSymbol S vfun using S in
    ifb val <> R_UnboundValue then
      result_success S val
    else installAssignFcnSymbol S vfun.

Definition SET_TEMPVARLOC_FROM_CAR S loc lhs :=
  add%stack "SET_TEMPVARLOC_FROM_CAR" in
  read%list lhs_car, _, _ := lhs using S in
  let v := lhs_car in
  if%success MAYBE_SHARED S v using S then
    let%success v := shallow_duplicate globals runs S v using S in
    run%success ENSURE_NAMED S v using S in
    set%car lhs := v using S in
    result_skip S in
  R_SetVarLocValue globals runs S loc v.

Definition applydefine S (call op args rho : SEXP) : result SEXP :=
  add%stack "applydefine" in
  read%list args_car, args_cdr, _ := args using S in
  let expr := args_car in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let%success rhs := eval globals runs S args_cdr_car rho using S in
  let saverhs := rhs in
  ifb rho = R_BaseNamespace then
    result_error S "Can’t do complex assignments in base namespace."
  else ifb rho = R_BaseEnv then
    result_error S "Can’t do complex assignments in base environment."
  else
    run%success defineVar globals runs S R_TmpvalSymbol R_NilValue rho using S in
    let%success tmploc := R_findVarLocInFrame globals runs S rho R_TmpvalSymbol using S in
    let%success cntxt :=
      begincontext globals S Ctxt_CCode call R_BaseEnv R_BaseEnv R_NilValue R_NilValue using S in
    let%success op_val := PRIMVAL runs S op using S in
    let%success lhs :=
      read%list _, expr_cdr, _ := expr using S in
      read%list expr_cdr_car, _, _ := expr_cdr using S in
      evalseq globals runs S expr_cdr_car rho (decide (op_val = 1 \/ op_val = 3)) tmploc using S in
    let%success rhsprom := mkRHSPROMISE globals S args_cdr_car rhs using S in
    do%success (rhs, lhs, expr) := (rhs, lhs, expr)
    while
        read%list _, expr_cdr, _ := expr using S in
        read%list expr_cdr_car, _, _ := expr_cdr using S in
        isLanguage globals S expr_cdr_car do
      read%list expr_car, expr_cdr, _ := expr using S in
      read%list expr_cdr_car, expr_cdr_cdr, _ := expr_cdr using S in
      let%success tmp :=
        let%success expr_car_type := TYPEOF S expr_car using S in
        ifb expr_car_type = SymSxp then
          getAssignFcnSymbol S expr_car
        else
          let%success expr_car_type := TYPEOF S expr_car using S in
          read%list expr_car_car, expr_car_cdr, _ := expr_car using S in
          let%success expr_car_len := R_length globals runs S expr_car using S in
          read%list expr_car_cdr_car, expr_car_cdr_cdr, _ := expr_car_cdr using S in
          read%list expr_car_cdr_cdr_car, _, _ := expr_car_cdr_cdr using S in
          let%success expr_car_cdr_cdr_car_type := TYPEOF S expr_car_cdr_cdr_car using S in
          ifb expr_car_type = LangSxp
              /\ (expr_car_car = R_DoubleColonSymbol \/ expr_car_car = R_TripleColonSymbol)
              /\ expr_car_len = 3 /\ expr_car_cdr_cdr_car_type = SymSxp then
            let%success tmp := getAssignFcnSymbol S expr_car_cdr_cdr_car using S in
            let%success tmp := lang3 globals S expr_car_car expr_car_cdr_car tmp using S in
            result_success S tmp
          else result_error S "Invalid function in complex assignment." using S in
      run%success SET_TEMPVARLOC_FROM_CAR S tmploc lhs using S in
      let%success rhs :=
        replaceCall globals runs S tmp R_TmpvalSymbol expr_cdr_cdr rhsprom using S in
      let%success rhs := eval globals runs S rhs rho using S in
      run%success SET_PRVALUE S rhsprom rhs using S in
      run%success SET_PRCODE S rhsprom rhs using S in
      read%list _, lhs_cdr, _ := lhs using S in
      result_success S (rhs, lhs_cdr, expr_cdr_car) using S, runs in
    read%list expr_car, expr_cdr, _ := expr using S in
    let%success afun :=
      let%success expr_car_type := TYPEOF S expr_car using S in
      ifb expr_car_type = SymSxp then
        getAssignFcnSymbol S expr_car
      else
        let%success expr_car_type := TYPEOF S expr_car using S in
        read%list expr_car_car, expr_car_cdr, _ := expr_car using S in
        let%success expr_car_len := R_length globals runs S expr_car using S in
        read%list expr_car_cdr_car, expr_car_cdr_cdr, _ := expr_car_cdr using S in
        read%list expr_car_cdr_cdr_car, _, _ := expr_car_cdr_cdr using S in
        let%success expr_car_cdr_cdr_car_type := TYPEOF S expr_car_cdr_cdr_car using S in
        ifb expr_car_type = LangSxp
            /\ (expr_car_car = R_DoubleColonSymbol \/ expr_car_car = R_TripleColonSymbol)
            /\ expr_car_len = 3 /\ expr_car_cdr_cdr_car_type = SymSxp then
          let%success afun := getAssignFcnSymbol S expr_car_cdr_cdr_car using S in
          let%success afun := lang3 globals S expr_car_car expr_car_cdr_car afun using S in
          result_success S afun
        else result_error S "Invalid function in complex assignment (after the loop)." using S in
    run%success SET_TEMPVARLOC_FROM_CAR S tmploc lhs using S in
    let%success R_asymSymbol_op :=
      ifb op_val < 0 \/ op_val >= length (R_asymSymbol S) then
        result_error S "Out of bound access to R_asymSymbol."
      else
        let%defined sym := nth_option (Z.to_nat op_val) (R_asymSymbol S) using S in
        result_success S sym using S in
    read%list _, lhs_cdr, _ := lhs using S in
    let%success expr :=
      read%list _, expr_cdr_cdr, _ := expr_cdr using S in
      assignCall globals runs S R_asymSymbol_op lhs_cdr afun R_TmpvalSymbol expr_cdr_cdr rhsprom using S in
    let%success expr := eval globals runs S expr rho using S in
    run%success endcontext globals runs S cntxt using S in
    run%success unbindVar globals runs S R_TmpvalSymbol rho using S in
    run%success INCREMENT_NAMED S saverhs using S in
    result_success S saverhs.

Definition do_set S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_set" in
  let%success op_val := PRIMVAL runs S op using S in
  let wrong S :=
    ifb op_val < 0 then
      result_error S "Negative offset."
    else
      let%defined n := nth_option (Z.to_nat op_val) asym using S in
      WrongArgCount S n in
  ifb args = R_NilValue then wrong S
  else read%list args_car, args_cdr, _ := args using S in
  ifb args_cdr = R_NilValue then wrong S
  else read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
  ifb args_cdr_cdr <> R_NilValue then wrong S
  else
    let lhs := args_car in
    let%success lhs_type := TYPEOF S lhs using S in
    match lhs_type with
    | StrSxp
    | SymSxp =>
      let%success lhs :=
        ifb lhs_type = StrSxp then
          let%success lhs_char := STRING_ELT S lhs 0 using S in
          installTrChar globals runs S lhs_char
        else result_success S lhs using S in
      let%success rhs := eval globals runs S args_cdr_car rho using S in
      run%success INCREMENT_NAMED S rhs using S in
      run%success
        ifb op_val = 2 then
          read%env _, rho_env := rho using S in
          setVar globals runs S lhs rhs (env_enclos rho_env)
        else
          defineVar globals runs S lhs rhs rho using S in
      result_success S rhs
    | LangSxp => applydefine S call op args rho
    | _ => result_error S "Invalid left-hand side to assignment."
    end.

Definition do_function S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_function" in
  let%success op :=
    let%success op_type := TYPEOF S op using S in
    ifb op_type = PromSxp then
      let%success op := forcePromise globals runs S op using S in
      map%pointer op with set_named_plural using S in
      result_success S op
    else result_success S op using S in
  let%success len := R_length globals runs S args using S in
  ifb len < 2 then
    WrongArgCount S "function"
  else
    read%list args_car, args_cdr, _ := args using S in
    run%success CheckFormals S args_car using S in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
    let%success rval :=
      mkCLOSXP globals S args_car args_cdr_car rho using S in
    read%list args_cdr_cdr_car, _, _ := args_cdr_cdr using S in
    let srcref := args_cdr_cdr_car in
    let%success srcref_type := TYPEOF S srcref using S in
    run%success
      ifb srcref_type = NilSxp then
        run%success
          setAttrib globals runs S rval R_SrcrefSymbol srcref using S in
        result_skip S
      else result_skip S using S in
    result_success S rval.

Definition do_break S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_break" in
  run%success Rf_checkArityCall S op args call using S in
  let%success op_val := PRIMVAL runs S op using S in
  match int_to_nbits_check op_val with
  | None => result_impossible S "The variable “op_val” should be of type “context_type”."
  | Some c => findcontext globals runs _ S c rho R_NilValue
  end.

Definition do_paren S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_paren" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, _, _ := args using S in
  result_success S args_car.

Definition getBlockSrcrefs S call : result SEXP :=
  add%stack "getBlockSrcrefs" in
  let%success srcrefs := getAttrib globals runs S call R_SrcrefSymbol using S in
  let%success srcrefs_type := TYPEOF S srcrefs using S in
  ifb srcrefs_type = VecSxp then
    result_success S srcrefs
  else result_success S (R_NilValue : SEXP).

Definition do_begin S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_begin" in
  ifb args <> R_NilValue then
    let%success srcrefs := getBlockSrcrefs S call using S in
    fold%success s := R_NilValue : SEXP
    along args
    as args_car, _ do
      let%success s := eval globals runs S args_car rho using S in
      result_success S s using S, runs, globals in
    result_success S s
  else result_success S (R_NilValue : SEXP).

Definition do_return S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_return" in
  let%success v :=
    ifb args = R_NilValue then
      result_success S (R_NilValue : SEXP)
    else
      read%list args_car, args_cdr, _ := args using S in
      ifb args_cdr = R_NilValue then
        eval globals runs S args_car rho
      else result_error S "Multi-argument returns are not permitted." using S in
  findcontext globals runs _ S (context_type_merge Ctxt_Browser Ctxt_Function) rho v.

Definition BodyHasBraces S body :=
  add%stack "BodyHasBraces" in
  if%success isLanguage globals S body using S then
    read%list body_car, _, _ := body using S in
    result_success S (decide (body_car = R_BraceSymbol))
  else result_success S false.

Definition do_if S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_if" in
  read%list args_car, args_cdr, _ := args using S in
  let%success Cond := eval globals runs S args_car rho using S in
  let%success (Stmt, vis) :=
    let%success asLogical := asLogicalNoNA globals runs S Cond call using S in
    read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
    ifb asLogical <> 0 then
      result_success S (args_cdr_car, false)
    else
      let%success l := R_length globals runs S args using S in
      ifb l > 2 then
        read%list args_cdr_cdr_car, _, _ := args_cdr_cdr using S in
        result_success S (args_cdr_cdr_car, false)
      else result_success S (R_NilValue : SEXP, true) using S in
  if vis then
    result_success S Stmt
  else eval globals runs S Stmt rho.

Definition do_while S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_while" in
  run%success Rf_checkArityCall S op args call using S in
  read%list _, args_cdr, _ := args using S in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let body := args_cdr_car in
  let%success bgn := BodyHasBraces S body using S in
  let%success cntxt :=
    begincontext globals S Ctxt_Loop R_NilValue rho R_BaseEnv R_NilValue R_NilValue using S in
  set%longjump context_cjmpbuf cntxt as jmp using S, runs in
  run%success
    ifb jmp <> Ctxt_Break then
      do%let while
        read%list args_car, _, _ := args using S in
        let%success ev := eval globals runs S args_car rho using S in
        let%success al := asLogicalNoNA globals runs S ev call using S in
        result_success S (decide (al <> 0))
      do
        run%success eval globals runs S body rho using S in
        result_skip S using S, runs
    else result_skip S using S in
  run%success endcontext globals runs S cntxt using S in
  result_success S (R_NilValue : SEXP).

Definition do_repeat S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_repeat" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, _, _ := args using S in
  let body := args_car in
  let%success cntxt :=
    begincontext globals S Ctxt_Loop R_NilValue rho R_BaseEnv R_NilValue R_NilValue using S in
  set%longjump context_cjmpbuf cntxt as jmp using S, runs in
  run%success
    ifb jmp <> Ctxt_Break then
      do%let whileb True do
        run%success eval globals runs S body rho using S in
        result_skip S using S, runs
    else result_skip S using S in
  run%success endcontext globals runs S cntxt using S in
  result_success S (R_NilValue : SEXP).

Definition simple_as_environment S arg :=
  add%stack "simple_as_environment" in
  let%success arg_s4 := IS_S4_OBJECT S arg using S in
  let%success arg_type := TYPEOF S arg using S in
  ifb arg_s4 /\ arg_type = S4Sxp then
    result_not_implemented "R_getS4DataSlot"
  else result_success S (R_NilValue : SEXP).

Definition do_eval S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_eval" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  let expr := args_car in
  read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
  let env := args_cdr_car in
  read%list args_cdr_cdr_car, _, _ := args_cdr_cdr using S in
  let encl := args_cdr_cdr_car in
  let%success tEncl := TYPEOF S encl using S in
  let%success encl :=
    if%success isNull S encl using S then
      result_success S (R_BaseEnv : SEXP)
    else
      let%success encl_ie := isEnvironment S encl using S in
      ifb negb encl_ie then
        let%success encl := simple_as_environment S encl using S in
        let%success encl_ie := isEnvironment S encl using S in
        if negb encl_ie then
          result_error S "Invalid argument."
        else result_success S encl
      else result_success S encl using S in
  let%success env :=
    let%success env_s4 := IS_S4_OBJECT S env using S in
    let%success env_type := TYPEOF S env using S in
    ifb env_s4 /\ env_type = S4Sxp then
      result_not_implemented "R_getS4DataSlot"
    else result_success S env using S in
  let%success env_type := TYPEOF S env using S in
  let%success env :=
    match env_type with
    | NilSxp =>
      result_success S encl
    | EnvSxp =>
      result_success S env
    | ListSxp =>
      let%success d := duplicate globals runs S args_cdr_car using S in
      NewEnvironment globals runs S R_NilValue d encl
    | VecSxp =>
      result_not_implemented "VectorToPairListNamed"
    | IntSxp
    | RealSxp =>
      let%success env_len := R_length globals runs S env using S in
      ifb env_len <> 1 then
        result_error S "Numeric ‘envir’ argument not of length one."
      else
        let%success frame := asInteger globals S env using S in
        ifb frame = NA_INTEGER then
          result_error S "Invalid argument ‘envir’ after convertion."
        else result_not_implemented "R_sysframe"
    | _ => result_error S "Invalid argument ‘envir’."
    end using S in
  let%success expr :=
    let%success expr_type := TYPEOF S expr using S in
    let%success expr_bc := isByteCode S expr using S in
    ifb expr_type = LangSxp \/ expr_type = SymSxp \/ expr_bc then
      let%success cntxt :=
        begincontext globals S Ctxt_Return (context_call (R_GlobalContext S)) env rho args op using S in
      set%longjump context_cjmpbuf cntxt as jmp using S, runs in
      let%success expr :=
        ifb jmp <> empty_context_type then
          eval globals runs S expr env
        else
          let expr := R_ReturnedValue S in
          ifb expr = R_RestartToken then
            let S := state_with_context S (context_with_callflag cntxt Ctxt_Return) in
            result_error S "Restarts not supported in ‘eval’."
          else result_success S expr using S in
      run%success endcontext globals runs S cntxt using S in
      result_success S expr
    else ifb expr_type = ExprSxp then
      let%success srcrefs := getBlockSrcrefs S expr using S in
      let%success n := LENGTH globals S expr using S in
      let%success cntxt :=
        begincontext globals S Ctxt_Return (context_call (R_GlobalContext S)) env rho args op using S in
      set%longjump context_cjmpbuf cntxt as jmp using S, runs in
      let%success tmp :=
        ifb jmp <> empty_context_type then
          do%let tmp := R_NilValue : SEXP
          for i from 0 to n - 1 do
            result_not_implemented "getSrcref" using S
        else
          let tmp := R_ReturnedValue S in
          ifb tmp = R_RestartToken then
            let S := state_with_context S (context_with_callflag cntxt Ctxt_Return) in
            result_error S "Restarts not supported in ‘eval’."
          else result_success S tmp using S in
      run%success endcontext globals runs S cntxt using S in
      result_success S tmp
    else ifb expr_type = PromSxp then
      eval globals runs S expr rho
    else result_success S expr using S in
  result_success S expr.


(** * connections.c **)

(** The function names of this section corresponds to the function names
  in the file main/connections.c. **)

Definition getConnection S (n : int) :=
  add%stack "getConnection" in
  ifb n < 0 \/ n >= length (R_Connections S) \/ n = NA_INTEGER then
    result_error S "Invalid connection."
  else
    let%defined c := nth_option (Z.to_nat n) (R_Connections S) using S in
    result_success S c.

(** The following six functions execute the interpretation function
  for each action, then replaces the corresponding connection in the
  global state.  These functions are not in the original C code of R.
  They correspond to a non-pure call to the corresponding methods of
  the given connection. **)

Definition putConnection S (n : int) c :=
  add%stack "putConnection" in
  ifb n < 0 \/ n >= length (R_Connections S) \/ n = NA_INTEGER then
    result_error S "Invalid connection."
  else
    let S := update_R_Connections S (update (Z.to_nat n) c (R_Connections S)) in
    result_skip S.

Definition run_open S n :=
  add%stack "run_open" in
  let%success con := getConnection S n using S in
  let%defined (c, r) := interpret_open (Rconnection_open con) con using S in
  run%success putConnection S n c using S in
  result_success S r.

Definition run_close S n :=
  add%stack "run_close" in
  let%success con := getConnection S n using S in
  let%defined c := interpret_close (Rconnection_close con) con using S in
  run%success putConnection S n c using S in
  result_skip S.

Definition run_destroy S n :=
  add%stack "run_destroy" in
  let%success con := getConnection S n using S in
  let%defined c := interpret_destroy (Rconnection_destroy con) con using S in
  run%success putConnection S n c using S in
  result_skip S.

Definition run_print S n str :=
  add%stack "run_print" in
  let%success con := getConnection S n using S in
  let%defined c := interpret_print (Rconnection_print con) con str using S in
  run%success putConnection S n c using S in
  result_skip S.

Definition run_flush S n :=
  add%stack "run_flush" in
  let%success con := getConnection S n using S in
  let%defined c := interpret_flush (Rconnection_fflush con) con using S in
  run%success putConnection S n c using S in
  result_skip S.

(** We now continue with functions translated from main/connections.c. **)

Definition do_getconnection S (call op args env : SEXP) : result SEXP :=
  add%stack "do_getconnection" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, _, _ := args using S in
  let%success what := asInteger globals S args_car using S in
  ifb what = NA_INTEGER then
    result_error S "There is no connection NA."
  else ifb what < 0 \/ what >= length (R_Connections S) then
    result_error S "There is no such connection."
  else
    let%defined con := nth_option (Z.to_nat what) (R_Connections S) using S in
    let (S, ans) := ScalarInteger globals S what in
    let%success class := allocVector globals S StrSxp 2 using S in
    let (S, class0) := mkChar globals S (Rconnection_class con) in
    write%Pointer class at 0 := class0 using S in
    let (S, class1) := mkChar globals S "connection" in
    write%Pointer class at 1 := class1 using S in
    run%success classgets S ans class using S in
    run%success
      ifb what > 2 then
        let%success ex_ptr := result_not_implemented "External pointer." using S in
        run%success setAttrib globals runs S ans R_ConnIdSymbol ex_ptr using S in
        result_skip S
      else result_skip S using S in
    result_success S ans.


(** * printutils.c **)

(** The function names of this section corresponds to the function names
  in the file main/printutils.c. **)

(** This function is inspired from [Rprintf]. **)
Definition Rprint S str :=
  add%stack "Rprint" in
  let con_num := R_OutputCon S in
  run_print S con_num str.


(** * builtin.c **)

(** The function names of this section corresponds to the function names
  in the file main/builtin.c. **)

Definition do_makelist S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_makelist" in
  fold%success (n, havenames) := (0, false)
  along args
  as _, args_tag do
    ifb args_tag <> R_NilValue then
      result_success S (1 + n, true)
    else result_success S (1 + n, havenames) using S, runs, globals in
  let%success list := allocVector globals S VecSxp n using S in
  let%success names :=
    if havenames then
      allocVector globals S StrSxp n
    else result_success S (R_NilValue : SEXP) using S in
  do%success args := args
  for i from 0 to n - 1 do
    read%list args_car, args_cdr, args_tag := args using S in
    run%success
      if havenames then
        ifb args_tag <> R_NilValue then
          let%success str := PRINTNAME S args_tag using S in
          SET_STRING_ELT S names i str
        else SET_STRING_ELT S names i R_BlankString
      else result_skip S using S in
    run%success
      let%success args_car_named := NAMED S args_car using S in
      ifb args_car_named <> named_temporary then
        map%pointer op with set_named_plural using S in
        result_skip S
      else result_skip S using S in
    run%success SET_VECTOR_ELT S list i args_car using S in
    result_success S args_cdr using S in
  run%success
    if havenames then
      run%success setAttrib globals runs S list R_NamesSymbol names using S in
      result_skip S
    else result_skip S using S in
  result_success S list.

Definition trChar S x :=
  add%stack "trChar" in
  (** We ignore any encoding issue here. **)
  CHAR S x.

Definition cat_printsep S sep ntot :=
  add%stack "cat_printsep" in
  let%success len := LENGTH globals S sep using S in
  ifb sep = R_NilValue \/ len = 0 then
    result_skip S
  else
    let%success str := STRING_ELT S sep (ntot mod len) using S in
    let%success sepchar := trChar S str using S in
    Rprint S sepchar.

Definition cat_cleanup S con_num :=
  add%stack "cat_cleanup" in
  run_flush S con_num.

Definition do_cat S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_cat" in
  run%success Rf_checkArityCall S op args call using S in
  (* Call to [PrintDefaults] formalised out. *)
  read%list args_car, args_cdr, _ := args using S in
  let objs := args_car in
  let args := args_cdr in
  read%list args_car, args_cdr, _ := args using S in
  let file := args_car in
  let%success ifile := asInteger globals S file using S in
  let%success con := getConnection S ifile using S in
  if negb (Rconnection_canwrite con) then
    result_error S "Cannot write to this connection."
  else
    let args := args_cdr in
    read%list args_car, args_cdr, _ := args using S in
    let sepr := args_car in
    let%success sepr_is := isString S sepr using S in
    if negb sepr_is then
      result_error S "Invalid sep specification."
    else
      let%success seprlen := LENGTH globals S sepr using S in
      do%success nlsep := false
      for i from 0 to seprlen - 1 do
        let%success sepri := STRING_ELT S sepr i using S in
        let%success sepristr := CHAR S sepri using S in
        result_success S (decide (nlsep \/ sepristr = ("010"%char)%string (** '\n' **))) using S in
      let args := args_cdr in
      read%list args_car, args_cdr, _ := args using S in
      let fill := args_car in
      let%success isNum := isNumeric globals runs S fill using S in
      let%success isLog := isLogical S fill using S in
      let%success len := LENGTH globals S fill using S in
      ifb ~ isNum /\ ~ isLog /\ len <> 1 then
        result_error S "Invalid fill argument."
      else
        let%success pwidth :=
          if%success isLogical S fill using S then
            let%success asLog := asLogical globals S fill using S in
            ifb asLog = 1 then
              result_success S INT_MAX (* [R_print.width] formalised out. *)
            else result_success S INT_MAX
          else asInteger globals S fill using S in
        let pwidth :=
          ifb pwidth <= 0 then
            (* A warning has been formalised out here. *)
            INT_MAX
          else pwidth in
        let args := args_cdr in
        read%list args_car, args_cdr, _ := args using S in
        let labs := args_car in
        let%success isStr := isString S labs using S in
        ifb ~ isStr /\ labs <> R_NilValue then
          result_error S "Invalid labels argument."
        else
          let%success lablen := R_length globals runs S labs using S in
          let args := args_cdr in
          read%list args_car, args_cdr, _ := args using S in
          let%success append := asLogical globals S args_car using S in
          ifb append = NA_LOGICAL then
            result_error S "Invalid append specification."
          else
            let%success cntxt :=
              begincontext globals S Ctxt_CCode R_NilValue R_BaseEnv R_BaseEnv R_NilValue R_NilValue using S in
            let%success nobjs := R_length globals runs S objs using S in
            do%success (ntot, nlines) := (0, 0)
            for iobj from 0 to nobjs - 1 do
              read%Pointer s := objs at iobj using S in
              let%success isn := isNull S s using S in
              let%success ntot :=
                ifb iobj <> 0 /\ ~ isn then
                  run%success cat_printsep S sepr ntot using S in
                  result_success S (1 + ntot)
                else result_success S ntot using S in
              let%success n := R_length globals runs S s using S in
              ifb n > 0 then
                let%success fill_in := asInteger globals S fill using S in
                let%success nlines :=
                  ifb labs <> R_NilValue /\ iobj = 0 /\ fill_in > 0 then
                    let%success str := STRING_ELT S labs (nlines mod lablen) using S in
                    let%success str := trChar S str using S in
                    run%success Rprint S str using S in
                    result_success S (1 + nlines)
                  else result_success S nlines using S in
                let%success p :=
                  if%success isString S s using S then
                    let%success str := STRING_ELT S s 0 using S in
                    trChar S str
                  else if%success isSymbol S s using S then
                    let%success str := PRINTNAME S s using S in
                    CHAR S str
                  else if%success isVectorAtomic S s using S then
                    result_not_implemented "EncodeElement0 (First step)"
                  else if%success isVectorList S s using S then
                    result_success S ""%string
                  else result_error S "Argument can not be handled by cat." using S in
                do%success (ntot, nlines, p) := (ntot, nlines, p)
                for i from 0 to n - 1 do
                  run%success Rprint S p using S in
                  ifb i < n - 1 then
                    run%success cat_printsep S sepr ntot using S in
                    let%success p :=
                      if%success isString S s using S then
                        let%success str := STRING_ELT S s (1 + i) using S in
                        trChar S str
                      else
                        result_not_implemented "EncodeElement0 (Second loop)"
                      using S in
                    result_success S (ntot, nlines, p)
                  else result_success S (ntot - 1, nlines, p) using S in
                result_success S (ntot, nlines)
              else result_success S (ntot, nlines) using S in
            run%success
              ifb pwidth <> INT_MAX \/ nlsep then
                Rprint S ("010"%char (** '\n' **))
              else result_skip S using S in
            run%success endcontext globals runs S cntxt using S in
            run%success cat_cleanup S ifile using S in
            result_success S (R_NilValue : SEXP).


(** * seq.c **)

(** The function names of this section corresponds to the function names
  in the file main/seq.c. **)

Definition cross_colon (S : state) (call s t : SEXP) : result SEXP :=
  add%stack "cross_colon" in
  result_not_implemented "".

Definition seq_colon S n1 n2 (call : SEXP) : result SEXP :=
  add%stack "seq_colon" in
  let r := Double.fabs (Double.sub n2 n1) in
  ifb r >= (R_XLEN_T_MAX : double) then
    result_error S "Result would be too large a vector."
  else
    let n := Z.to_nat (Double.double_to_int_zero (Double.add (Double.add r (1 : double)) (Double.FLT_EPSILON))) in
    let useInt := decide (n1 <= (INT_MAX : double) /\ n1 = ((Double.double_to_int_zero n1) : double)) in
    let useInt :=
      ifb n1 <= (INT_MIN : double) \/ n1 > (INT_MAX : double) then false
      else
        let dn := n : double in
        let r :=
          Double.add n1
            (ifb n1 <= n2 then Double.sub dn (1 : double) else Double.opp (Double.sub dn (1 : double))) in
        decide (r <= (INT_MIN : double) \/ r > (INT_MAX : double)) in
    let%success ans :=
      if useInt then
        let in1 := Double.double_to_int_zero n1 in
        let%success ans := allocVector globals S IntSxp n using S in
        run%success
          ifb n1 <= n2 then
            do%let for i from 0 to n - 1 do
              write%Integer ans at i := in1 + i using S in
              result_skip S using S
          else
            do%let for i from 0 to n - 1 do
              write%Integer ans at i := in1 - i using S in
              result_skip S using S using S in
        result_success S ans
      else
        let%success ans := allocVector globals S RealSxp n using S in
        run%success
          ifb n1 <= n2 then
            do%let for i from 0 to n - 1 do
              write%Real ans at i := Double.add n1 (i : double) using S in
              result_skip S using S
          else
            do%let for i from 0 to n - 1 do
              write%Real ans at i := Double.sub n1 (i : double) using S in
              result_skip S using S using S in
        result_success S ans
      using S in
    result_success S ans.

Definition do_colon S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_colon" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, args_cdr, _ := args using S in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let%success args_car_in := inherits globals runs S args_car "factor" using S in
  let%success args_cdr_car_in := inherits globals runs S args_cdr_car "factor" using S in
  ifb args_car_in /\ args_cdr_car_in then
    cross_colon S call args_car args_cdr_car
  else
    let s1 := args_car in
    let s2 := args_cdr_car in
    let%success n1 := R_length globals runs S s1 using S in
    let%success n2 := R_length globals runs S s2 using S in
    ifb n1 = 0 \/ n2 = 0 then
      result_error S "Argument of length 0."
    else
      (* Warnings have been formalised out here. *)
      let%success n1 := asReal globals S s1 using S in
      let%success n2 := asReal globals S s2 using S in
      ifb ISNAN n1 \/ ISNAN n2 then
        result_error S "NA or NaN argument."
      else seq_colon S n1 n2 call.


(** * sign.c **)

(** The function names of this section corresponds to the function names
  in the file nmath/sign.c. **)

Definition sign x :=
  ifb ISNAN x then x
  else ifb x > 0 then 1
  else ifb x = 0 then 0
  else (-1)%Z.


(** * complex.c **)

(** The function names of this section corresponds to the function names
  in the file main/complex.c. **)

Definition complex_binary (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  add%stack "complex_binary" in
  result_not_implemented "".

Definition complex_unary S (code : int) s1 :=
  add%stack "complex_unary" in
  ifb code = PLUSOP then
    result_success S s1
  else ifb code = MINUSOP then
    let%success ans :=
      if%success NO_REFERENCES S s1 using S then
        result_success S s1
      else duplicate globals runs S s1 using S in
    read%VectorComplex s1_ := s1 using S in
    let px := VecSxp_data s1_ in
    let pa := ArrayListExtra.map (fun x =>
      make_Rcomplex (Double.opp (Rcomplex_r x)) (Double.opp (Rcomplex_i x))) px in
    write%VectorComplex ans := pa using S in
    result_success S ans
    else result_error S "Invalid unary operator.".

Definition complex_math1 (S : state) (call op args env : SEXP) : result SEXP :=
  add%stack "complex_math1" in
  result_not_implemented "".


(** * arithmetic.c **)

(** The function names of this section corresponds to the function names
  in the file main/arithmetic.c. **)

Definition R_finite (x : double) :=
  decide (~ Double.isNaN x /\ x <> R_PosInf /\ x <> R_NegInf).

Definition R_FINITE := R_finite.

Definition real_binary (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  add%stack "real_binary" in
  result_not_implemented "".

Definition integer_binary (S : state) (code : int) (s1 s2 lcall : SEXP) : result SEXP :=
  add%stack "integer_binary" in
  result_not_implemented "".

Definition COERCE_IF_NEEDED S v tp :=
  add%stack "COERCE_IF_NEEDED" in
  let%success v_type := TYPEOF S v using S in
  ifb v_type <> tp then
    let%success vo := OBJECT S v using S in
    let%success v := coerceVector globals runs S v tp using S in
    run%success
      if vo then
        SET_OBJECT S v true
      else result_skip S using S in
    result_success S v
  else result_success S v.

Definition FIXUP_NULL_AND_CHECK_TYPES S v :=
  add%stack "FIXUP_NULL_AND_CHECK_TYPES" in
  let%success v_type := TYPEOF S v using S in
  match v_type with
  | NilSxp =>
    allocVector globals S IntSxp 0
  | CplxSxp
  | RealSxp
  | IntSxp
  | LglSxp =>
    result_success S v
  | _ =>
    result_error S "Non-numeric argument to binary operator."
  end.

Definition R_binary S (call op x y : SEXP) : result SEXP :=
  add%stack "R_binary" in
  let%success oper := PRIMVAL runs S op using S in
  let%success x := FIXUP_NULL_AND_CHECK_TYPES S x using S in
  let%success y := FIXUP_NULL_AND_CHECK_TYPES S y using S in
  let%success nx := XLENGTH S x using S in
  let%success ny := XLENGTH S y using S in
  let%success x_attrib := ATTRIB S x using S in
  let%success (xattr, xarray, xts, xS4) :=
    ifb x_attrib <> R_NilValue then
      let%success x_a := isArray globals runs S x using S in
      let%success x_ts := isTs globals runs S x using S in
      let%success x_s4 := isS4 S x using S in
      result_success S (true, x_a, x_ts, x_s4)
    else result_success S (false, false, false, false) using S in
  let%success y_attrib := ATTRIB S y using S in
  let%success (yattr, yarray, yts, yS4) :=
    ifb y_attrib <> R_NilValue then
      let%success y_a := isArray globals runs S y using S in
      let%success y_ts := isTs globals runs S y using S in
      let%success y_s4 := isS4 S y using S in
      result_success S (true, y_a, y_ts, y_s4)
    else result_success S (false, false, false, false) using S in
  run%success
    ifb xarray <> yarray then
      run%success
        ifb xarray /\ nx = 1 /\ ny <> 1 then
          ifb ny <> 0 then
            result_error S "Recycling array of length 1 in an array-vector arithmetic is depreciated."
          else
            let%success x := duplicate globals runs S x using S in
            run%success setAttrib globals runs S x R_DimSymbol R_NilValue using S in
            result_skip S
        else result_skip S using S in
      run%success
        ifb yarray /\ ny = 1 /\ nx <> 1 then
          ifb nx <> 0 then
            result_error S "Recycling array of length 1 in an array-vector arithmetic is depreciated."
          else
            let%success y := duplicate globals runs S y using S in
            run%success setAttrib globals runs S y R_DimSymbol R_NilValue using S in
            result_skip S
        else result_skip S using S in
      result_skip S
    else result_skip S using S in
  let%success (dims, xnames, ynames) :=
    ifb xarray \/ yarray then
      let%success dims :=
        ifb xarray /\ yarray then
          let%success c := conformable globals runs S x y using S in
          if negb c then
            result_error S "Non-conformable arrays."
          else getAttrib globals runs S x R_DimSymbol
        else ifb xarray /\ (ny <> 0 \/ nx = 0) then
          getAttrib globals runs S x R_DimSymbol
        else ifb yarray /\ (nx <> 0 \/ ny = 0) then
          getAttrib globals runs S y R_DimSymbol
        else result_success S (R_NilValue : SEXP) using S in
      let%success xnames :=
        if xattr then
          getAttrib globals runs S x R_DimNamesSymbol
        else result_success S (R_NilValue : SEXP) using S in
      let%success ynames :=
        if yattr then
          getAttrib globals runs S y R_DimNamesSymbol
        else result_success S (R_NilValue : SEXP) using S in
      result_success S (dims, xnames, ynames)
    else
      let dims := R_NilValue : SEXP in
      let%success xnames :=
        if xattr then
          getAttrib globals runs S x R_NamesSymbol
        else result_success S (R_NilValue : SEXP) using S in
      let%success ynames :=
        if yattr then
          getAttrib globals runs S y R_NamesSymbol
        else result_success S (R_NilValue : SEXP) using S in
      result_success S (dims, xnames, ynames) using S in
  let%success (tsp, klass) :=
    ifb xts \/ yts then
      ifb xts /\ yts then
        let%success c := tsConform globals runs S x y using S in
        if negb c then
          result_error S "Non conformable time-series."
        else
          let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
          let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
          result_success S (tsp, klass)
      else if xts then
        ifb nx < ny then
          result_error S "Time-series/vector length mismatch."
        else
          let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
          let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
          result_success S (tsp, klass)
      else
        ifb ny < nx then
          result_error S "Time-series/vector length mismatch."
        else
          let%success tsp := getAttrib globals runs S y R_TspSymbol using S in
          let%success klass := getAttrib globals runs S y R_ClassSymbol using S in
          result_success S (tsp, klass)
    else result_success S (NULL, NULL) using S in
  (* A warning has been formalised out here. *)
  let%success x_type := TYPEOF S x using S in
  let%success y_type := TYPEOF S y using S in
  let%success val :=
    ifb x_type = CplxSxp \/ y_type = CplxSxp then
      let%success x := COERCE_IF_NEEDED S x CplxSxp using S in
      let%success y := COERCE_IF_NEEDED S y CplxSxp using S in
      complex_binary S oper x y
    else ifb x_type = RealSxp \/ y_type = RealSxp then
      let%success x :=
        ifb x_type <> IntSxp then
          COERCE_IF_NEEDED S x RealSxp
        else result_success S x using S in
      let%success y :=
        ifb y_type <> IntSxp then
          COERCE_IF_NEEDED S y RealSxp
        else result_success S y using S in
      real_binary S oper x y
    else integer_binary S oper x y call using S in
  ifb ~ xattr /\ ~ yattr then
    result_success S val
  else
    run%success
      ifb dims <> R_NilValue then
        run%success setAttrib globals runs S val R_DimSymbol dims using S in
        ifb xnames <> R_NilValue then
          run%success setAttrib globals runs S val R_DimNamesSymbol xnames using S in
          result_skip S
        else ifb ynames <> R_NilValue then
          run%success setAttrib globals runs S val R_DimNamesSymbol ynames using S in
          result_skip S
        else result_skip S
      else
        let%success val_len := XLENGTH S val using S in
        let%success xnames_len := xlength globals runs S xnames using S in
        ifb val_len = xnames_len then
          run%success setAttrib globals runs S val R_NamesSymbol xnames using S in
          result_skip S
        else
          let%success ynames_len := xlength globals runs S ynames using S in
          ifb val_len = ynames_len then
            run%success setAttrib globals runs S val R_NamesSymbol ynames using S in
            result_skip S
          else result_skip S using S in
    run%success
      ifb xts \/ yts then
        run%success setAttrib globals runs S val R_TspSymbol tsp using S in
        run%success setAttrib globals runs S val R_ClassSymbol klass using S in
        result_skip S
      else result_skip S using S in
    let%success val :=
      ifb xS4 \/ yS4 then
        asS4 globals runs S val true true
      else result_success S val using S in
    result_success S val.

Definition logical_unary S (code : int) s1 :=
  add%stack "logical_unary" in
  let%success n := XLENGTH S s1 using S in
  let%success names := getAttrib globals runs S s1 R_NamesSymbol using S in
  let%success dim := getAttrib globals runs S s1 R_DimSymbol using S in
  let%success dimnames := getAttrib globals runs S s1 R_DimNamesSymbol using S in
  read%VectorInteger s1_ := s1 using S in
  let px := VecSxp_data s1_ in
  let%success pa :=
    ifb code = PLUSOP then
      result_success S px
    else ifb code = MINUSOP then
      result_success S (ArrayListExtra.map (fun x =>
        ifb x = NA_INTEGER then NA_INTEGER
        else ifb x = 0 then 0 else -x) px)
    else result_error S "Invalid unary operator." using S in
  let (S, ans) := alloc_vector_int globals S pa in
  run%success
    ifb names <> R_NilValue then
      run%success setAttrib globals runs S ans R_NamesSymbol names using S in
      result_skip S
    else result_skip S using S in
  run%success
    ifb dim <> R_NilValue then
      run%success setAttrib globals runs S ans R_DimSymbol dim using S in
      result_skip S
    else result_skip S using S in
  run%success
    ifb dimnames <> R_NilValue then
      run%success setAttrib globals runs S ans R_DimNamesSymbol dimnames using S in
      result_skip S
    else result_skip S using S in
  result_success S ans.

Definition integer_unary S (code : int) s1 :=
  add%stack "integer_unary" in
  ifb code = PLUSOP then
    result_success S s1
  else ifb code = MINUSOP then
    let%success ans :=
      if%success NO_REFERENCES S s1 using S then
        result_success S s1
      else duplicate globals runs S s1 using S in
    read%VectorInteger s1_ := s1 using S in
    let px := VecSxp_data s1_ in
    let pa := ArrayListExtra.map (fun x =>
      ifb x = NA_INTEGER then NA_INTEGER
      else ifb x = 0 then 0 else -x) px in
    write%VectorInteger ans := pa using S in
    result_success S ans
  else result_error S "Invalid unary operator.".

Definition real_unary S (code : int) s1 :=
  add%stack "real_unary" in
  ifb code = PLUSOP then
    result_success S s1
  else ifb code = MINUSOP then
    let%success ans :=
      if%success NO_REFERENCES S s1 using S then
        result_success S s1
      else duplicate globals runs S s1 using S in
    read%VectorReal s1_ := s1 using S in
    let px := VecSxp_data s1_ in
    let pa := ArrayListExtra.map (fun x => Double.opp x) px in
    write%VectorReal ans := pa using S in
    result_success S ans
  else result_error S "Invalid unary operator.".

Definition R_unary S (call op s1 : SEXP) : result SEXP :=
  add%stack "R_unary" in
  let%success operation := PRIMVAL runs S op using S in
  let%success s1_type := TYPEOF S s1 using S in
  match s1_type with
  | LglSxp => logical_unary S operation s1
  | IntSxp => integer_unary S operation s1
  | RealSxp => real_unary S operation s1
  | CplxSxp => complex_unary S operation s1
  | _ => result_error S "Invalid argument to unary operator."
  end.

Definition R_integer_plus S x y :=
  add%stack "R_integer_plus" in
  ifb x = NA_INTEGER \/ y = NA_INTEGER then
    result_success S NA_INTEGER
  else
    ifb (y < 0 /\ x > R_INT_MAX - y)%Z \/ (y > 0 /\ x < R_INT_MIN - y)%Z then
      (* A warning has been formalised out here. *)
      result_success S NA_INTEGER
    else result_success S (x + y)%Z.

Definition R_integer_minus S x y :=
  add%stack "R_integer_minus" in
  ifb x = NA_INTEGER \/ y = NA_INTEGER then
    result_success S NA_INTEGER
  else
    ifb (y < 0 /\ x > R_INT_MAX + y)%Z \/ (y > 0 /\ x < R_INT_MIN + y)%Z then
      (* A warning has been formalised out here. *)
      result_success S NA_INTEGER
    else result_success S (x - y)%Z.

Definition R_integer_times S x y :=
  add%stack "R_integer_times" in
  ifb x = NA_INTEGER \/ y = NA_INTEGER then
    result_success S NA_INTEGER
  else
    let z := (x * y)%Z in
    ifb Double.mult (x : double) (y : double) = (z : double) /\ z <> NA_INTEGER then
      result_success S z
    else
      (* A warning has been formalised out here. *)
      result_success S NA_INTEGER.

Definition R_integer_divide S x y :=
  add%stack "R_integer_divide" in
  ifb x = NA_INTEGER \/ y = NA_INTEGER then
    result_success S NA_REAL
  else result_success S (Double.div (x : double) (y : double)).

Definition do_arith S (call op args env : SEXP) : result SEXP :=
  add%stack "do_arith" in
  read%list args_car, args_cdr, _ := args using S in
  read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
  let%success argc :=
    ifb args = R_NilValue then
      result_success S 0
    else ifb args_cdr = R_NilValue then
      result_success S 1
    else ifb args_cdr_cdr = R_NilValue then
      result_success S 2
    else R_length globals runs S args using S in
  let arg1 := args_car in
  let arg2 := args_cdr_car in
  read%defined arg1_ := arg1 using S in
  read%defined arg2_ := arg1 using S in
  run%exit
    ifb attrib arg1_ <> R_NilValue \/ attrib arg2_ <> R_NilValue then
      if%defined ans := DispatchGroup globals S "Ops" call op args env using S then
        result_rreturn S ans
      else result_rskip S
    else ifb argc = 2 then
      let double_case S ans x1 x2 :=
        let%success op_val := PRIMVAL runs S op using S in
        ifb op_val = PLUSOP then
          run%success SET_SCALAR_DVAL S ans (Double.add x1 x2) using S in
          result_rreturn S ans
        else ifb op_val = MINUSOP then
          run%success SET_SCALAR_DVAL S ans (Double.sub x1 x2) using S in
          result_rreturn S ans
        else ifb op_val = TIMESOP then
          run%success SET_SCALAR_DVAL S ans (Double.mult x1 x2) using S in
          result_rreturn S ans
        else ifb op_val = DIVOP then
          run%success SET_SCALAR_DVAL S ans (Double.div x1 x2) using S in
          result_rreturn S ans
        else result_rskip S in
      if%success IS_SCALAR S arg1 RealSxp using S then
        let%success x1 := SCALAR_DVAL S arg1 using S in
        if%success IS_SCALAR S arg2 RealSxp using S then
          let%success x2 := SCALAR_DVAL S arg2 using S in
          let%success ans := ScalarValue2 globals S arg1 arg2 using S in
          double_case S ans x1 x2
        else
          if%success IS_SCALAR S arg2 IntSxp using S then
            let%success i2 := SCALAR_IVAL S arg2 using S in
            let x2 :=
              ifb i2 <> NA_INTEGER then
                (i2 : double)
              else NA_REAL in
            let%success ans := ScalarValue1 globals S arg1 using S in
            double_case S ans x1 x2
          else result_rskip S
      else
        if%success IS_SCALAR S arg1 IntSxp using S then
          let%success i1 := SCALAR_IVAL S arg1 using S in
          if%success IS_SCALAR S arg2 RealSxp using S then
            let x1 :=
              ifb i1 <> NA_INTEGER then
                (i1 : double)
              else NA_REAL in
            let%success x2 := SCALAR_DVAL S arg2 using S in
            let%success ans := ScalarValue1 globals S arg2 using S in
            double_case S ans x1 x2
          else
            if%success IS_SCALAR S arg2 IntSxp using S then
              let%success i2 := SCALAR_IVAL S arg2 using S in
              let%success op_val := PRIMVAL runs S op using S in
              ifb op_val = PLUSOP then
                let%success ans := ScalarValue2 globals S arg1 arg2 using S in
                let%success res := R_integer_plus S i1 i2 using S in
                run%success SET_SCALAR_IVAL S ans res using S in
                result_rreturn S ans
              else ifb op_val = MINUSOP then
                let%success ans := ScalarValue2 globals S arg1 arg2 using S in
                let%success res := R_integer_minus S i1 i2 using S in
                run%success SET_SCALAR_IVAL S ans res using S in
                result_rreturn S ans
              else ifb op_val = TIMESOP then
                let%success ans := ScalarValue2 globals S arg1 arg2 using S in
                let%success res := R_integer_times S i1 i2 using S in
                run%success SET_SCALAR_IVAL S ans res using S in
                result_rreturn S ans
              else ifb op_val = DIVOP then
                let%success res := R_integer_divide S i1 i2 using S in
                let (S, ans) := ScalarReal globals S res in
                result_rreturn S ans
              else result_rskip S
            else result_rskip S
        else result_rskip S
    else ifb argc = 1 then
      if%success IS_SCALAR S arg1 RealSxp using S then
        let%success op_val := PRIMVAL runs S op using S in
        ifb op_val = PLUSOP then
          result_rreturn S arg1
        else ifb op_val = MINUSOP then
          let%success ans := ScalarValue1 globals S arg1 using S in
          let%success v := SCALAR_DVAL S arg1 using S in
          run%success SET_SCALAR_DVAL S ans (Double.opp v) using S in
          result_rreturn S ans
        else result_rskip S
      else
        if%success IS_SCALAR S arg1 IntSxp using S then
          let%success op_val := PRIMVAL runs S op using S in
          ifb op_val = PLUSOP then
            result_rreturn S arg1
          else ifb op_val = MINUSOP then
            let%success ival := SCALAR_IVAL S arg1 using S in
            let%success ans := ScalarValue1 globals S arg1 using S in
            run%success SET_SCALAR_IVAL S ans (ifb ival = NA_INTEGER then NA_INTEGER else -ival) using S in
            result_rreturn S ans
          else result_rskip S
        else result_rskip S
    else result_rskip S using S in
  ifb argc = 2 then
    R_binary S call op arg1 arg2
  else ifb argc = 1 then
    R_unary S call op arg1
  else result_error S "Operator needs one or two arguments.".

Definition math1 S sa f (lcall : SEXP) :=
  add%stack "math1" in
  let%success sa_in := isNumeric globals runs S sa using S in
  if negb sa_in then
    result_error S "Non-numeric argument to mathematical function."
  else
    let%success n := XLENGTH S sa using S in
    let%success sa := coerceVector globals runs S sa RealSxp using S in
    let%success sy :=
      if%success NO_REFERENCES S sa using S then
        result_success S sa
      else allocVector globals S RealSxp n using S in
    do%success for i from 0 to n - 1 do
      read%Real x := sa at i using S in
      let fx := f x in
      write%Real sy at i := fx using S in
      if ISNAN fx then
        if ISNAN x then
          write%Real sy at i := x using S in
          result_skip S
        else result_skip S
      else result_skip S using S in
    (* A warning has been formalised out here. *)
    read%defined sa_ := sa using S in
    run%success
      ifb sa <> sy /\ attrib sa_ <> R_NilValue then
        SHALLOW_DUPLICATE_ATTRIB globals runs S sy sa
      else result_skip S using S in
    result_success S sy.

Definition do_math1 S (call op args env : SEXP) : result SEXP :=
  add%stack "do_math1" in
  run%success Rf_checkArityCall S op args call using S in
  run%success Rf_check1arg S args call "x" using S in
  if%defined ans := DispatchGroup globals S "Ops" call op args env using S then
    result_success S ans
  else
    read%list args_car, _, _ := args using S in
    if%success isComplex S args_car using S then
      complex_math1 S call op args env
    else
      let%success op_val := PRIMVAL runs S op using S in
      let MATH1 x := math1 S args_car x call in
      match Z.to_nat op_val with
      | 1 => MATH1 Double.floor
      | 2 => MATH1 Double.ceil
      | 3 => MATH1 Double.sqrt
      | 4 => MATH1 sign
      | 10 => MATH1 Double.exp
      | 11 => MATH1 Double.expm1
      | 12 => MATH1 Double.log1p
      | 20 => MATH1 Double.cos
      | 21 => MATH1 Double.sin
      | 22 => MATH1 Double.tan
      | 23 => MATH1 Double.acos
      | 24 => MATH1 Double.asin
      | 25 => MATH1 Double.atan
      | 30 => MATH1 Double.cosh
      | 31 => MATH1 Double.sinh
      | 32 => MATH1 Double.tanh
      | 33 => result_not_implemented "acosh"
      | 34 => result_not_implemented "asinh"
      | 35 => result_not_implemented "atanh"
      | 40 => result_not_implemented "lgammafn"
      | 41 => result_not_implemented "gammafn"
      | 42 => result_not_implemented "digamma"
      | 43 => result_not_implemented "trigamma"
      | 47 => result_not_implemented "cospi"
      | 48 => result_not_implemented "sinpi"
      | 49 => result_not_implemented "tanpi"
      | _ => result_error S "Unimplemented real function of 1 argument."
      end.


(** * subset.c **)

(** The function names of this section corresponds to the function names
  in the file main/subset.c. **)

Definition R_DispatchOrEvalSP S call op generic args rho :=
  add%stack "R_DispatchOrEvalSP" in
  read%list args_car, args_cdr, _ := args using S in
  let%exit (prom, args) :=
    ifb args <> R_NilValue /\ args_car <> R_DotsSymbol then
      let%success x := eval globals runs S args_car rho using S in
      run%success INCREMENT_LINKS S x using S in
      let%success x_obj := OBJECT S x using S in
      if negb x_obj then
        let%success elkm :=
          evalListKeepMissing globals runs S args_cdr rho using S in
        let (S, ans) := CONS_NR globals S x elkm in
        run%success DECREMENT_LINKS S x using S in
        result_rreturn S (false, ans)
      else result_not_implemented "R_mkEVPROMISE_NR"
    else result_rsuccess S (NULL, args) using S in
  let%success (disp, ans) :=
    DispatchOrEval globals runs S call op generic args rho false false using S in
  run%success
    ifb prom <> NULL then
      let%success prom_value := PRVALUE S prom using S in
      DECREMENT_LINKS S prom_value
    else result_skip S using S in
  result_success S (disp, ans).

Definition scalarIndex S s :=
  add%stack "scalarIndex" in
  let%success s_attr := ATTRIB S s using S in
  ifb s_attr = R_NilValue then
    if%success IS_SCALAR S s IntSxp using S then
      let%success ival := SCALAR_IVAL S s using S in
      ifb ival <> NA_INTEGER then
        result_success S ival
      else result_success S (-1)%Z
    else if%success IS_SCALAR S s RealSxp using S then
      let%success rval := SCALAR_DVAL S s using S in
      if R_FINITE rval then
        result_success S (Double.double_to_int_zero rval)
      else result_success S (-1)%Z
    else result_success S (-1)%Z
  else result_success S (-1)%Z.

Definition ExtractArg S args arg_sym :=
  add%stack "ExtractArg" in
  fold%return prev_arg := args
  along args
  as arg, _, arg_list do
    ifb list_tagval arg_list = arg_sym then
      run%success
        ifb arg = prev_arg then
          result_skip S
        else
          set%cdr prev_arg := list_cdrval arg_list using S in
          result_skip S using S in
      result_rreturn S (list_carval arg_list)
    else result_rsuccess S arg using S, runs, globals in
  result_success S (R_NilValue : SEXP).

Definition ExtractDropArg S el :=
  add%stack "ExtractDropArg" in
  let%success dropArg := ExtractArg S el R_DropSymbol using S in
  let%success drop := asLogical globals S dropArg using S in
  ifb drop = NA_LOGICAL then
    result_success S true
  else result_success S (decide (drop <> 0)).

Definition do_subset_dflt S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subset_dflt" in
  read%list args_car, args_cdr, _ := args using S in
  let cdrArgs := args_cdr in
  read%list cdrArgs_car, cdrArgs_cdr, cdrArgs_tag := cdrArgs using S in
  let cddrArgs := cdrArgs_cdr in
  read%list cddrArgs_car, cddrArgs_cdr, cddrArgs_tag := cddrArgs using S in
  run%exit
    ifb cdrArgs <> R_NilValue /\ cddrArgs = R_NilValue /\ cdrArgs_tag = R_NilValue then
      let x := args_car in
      let%success x_attr := ATTRIB S x using S in
      ifb x_attr = R_NilValue then
        let s := cdrArgs_car in
        let%success i := scalarIndex S s using S in
        let%success x_type := TYPEOF S x using S in
        match x_type with
        | RealSxp =>
          let%success len := XLENGTH S x using S in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := REAL_ELT S x (Z.to_nat (i - 1)) using S in
            let (S, r) := ScalarReal globals S x_imu in
            result_rreturn S r
          else result_rskip S
        | IntSxp =>
          let%success len := XLENGTH S x using S in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := INTEGER_ELT S x (Z.to_nat (i - 1)) using S in
            let (S, r) := ScalarInteger globals S x_imu in
            result_rreturn S r
          else result_rskip S
        | LglSxp =>
          let%success len := XLENGTH S x using S in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := LOGICAL_ELT S x (Z.to_nat (i - 1)) using S in
            result_rreturn S (ScalarLogical globals x_imu)
          else result_rskip S
        | CplxSxp =>
          let%success len := XLENGTH S x using S in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := COMPLEX_ELT S x (Z.to_nat (i - 1)) using S in
            let (S, r) := ScalarComplex globals S x_imu in
            result_rreturn S r
          else result_rskip S
        | RawSxp => result_not_implemented "Raw case."
        | _ => result_rskip S
        end
      else result_rskip S
    else ifb cddrArgs <> R_NilValue /\ cddrArgs_cdr = R_NilValue
          /\ cdrArgs_tag = R_NilValue /\ cddrArgs_tag = R_NilValue then
      let x := args_car in
      let%success attr := ATTRIB S x using S in
      read%list attr_car, attr_cdr, attr_tag := attr using S in
      ifb attr_tag = R_DimSymbol /\ attr_cdr = R_NilValue then
        let dim := attr_car in
        let%success dim_type := TYPEOF S dim using S in
        let%success dim_len := LENGTH globals S dim using S in
        ifb dim_type = IntSxp /\ dim_len = 2 then
          let si := cdrArgs_car in
          let sj := cddrArgs_car in
          let%success i := scalarIndex S si using S in
          let%success j := scalarIndex S sj using S in
          let%success nrow := INTEGER_ELT S dim 0 using S in
          let%success ncol := INTEGER_ELT S dim 1 using S in
          ifb i > 0 /\ j > 0 /\ i <= nrow /\ j <= ncol then
            let k := (i - 1 + nrow * (j - 1))%Z in
            let%success x_type := TYPEOF S x using S in
            match x_type with
            | RealSxp =>
              let%success len := XLENGTH S x using S in
              ifb k <= len then
                let%success x_k := REAL_ELT S x (Z.to_nat k) using S in
                let (S, r) := ScalarReal globals S x_k in
                result_rreturn S r
              else result_rskip S
            | IntSxp =>
              let%success len := XLENGTH S x using S in
              ifb k <= len then
                let%success x_k := INTEGER_ELT S x (Z.to_nat k) using S in
                let (S, r) := ScalarInteger globals S x_k in
                result_rreturn S r
              else result_rskip S
            | LglSxp =>
              let%success len := XLENGTH S x using S in
              ifb k <= len then
                let%success x_k := LOGICAL_ELT S x (Z.to_nat k) using S in
                result_rreturn S (ScalarLogical globals x_k)
              else result_rskip S
            | CplxSxp =>
              let%success len := XLENGTH S x using S in
              ifb k <= len then
                let%success x_k := COMPLEX_ELT S x (Z.to_nat k) using S in
                let (S, r) := ScalarComplex globals S x_k in
                result_rreturn S r
              else result_rskip S
            | RawSxp => result_not_implemented "Raw case."
            | _ => result_rskip S
            end
          else result_rskip S
        else result_rskip S
      else result_rskip S
    else result_rskip S using S in
  let%success drop := ExtractDropArg S args using S in
  let x := args_car in
  ifb x = R_NilValue then
    result_success S x
  else
    let subs := args_cdr in
    let%success nsubs := R_length globals runs S subs using S in
    let%success type := TYPEOF S x using S in
    let%success ax :=
      if%success isVector S x using S then
        result_success S x
      else if%success isPairList S x using S then
        let%success dim := getAttrib globals runs S x R_DimSymbol using S in
        let%success ndim := R_length globals runs S dim using S in
        let%success ax :=
          ifb ndim > 1 then
            result_not_implemented "allocArray"
          else
            let%success x_len := R_length globals runs S x using S in
            let%success ax := allocVector globals S VecSxp x_len using S in
            let%success x_names := getAttrib globals runs S x R_NamesSymbol using S in
            run%success setAttrib globals runs S ax R_NamesSymbol x_names using S in
            result_success S ax using S in
        fold%success i := 0
        along x
        as x_car, _ do
          run%success SET_VECTOR_ELT S ax i x_car using S in
          result_success S (1 + i) using S, runs, globals in
        result_success S ax
      else result_error S "Object is not subsettable." using S in
    result_not_implemented "VectorSubset".

Definition do_subset S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subset" in
  let%success (disp, ans) := R_DispatchOrEvalSP S call op "[" args rho using S in
  if disp then
    run%success
      let%success ans_named := NAMED S ans using S in
      ifb ans_named <> named_temporary then
        map%pointer ans with set_named_plural using S in
        result_skip S
      else result_skip S using S in
    result_success S ans
  else do_subset_dflt S call op ans rho.


(** * relop.c **)

(** The function names of this section corresponds to the function names
  in the file main/relop.c. **)

Definition DO_SCALAR_RELOP_int S (oper x y : int) :=
  add%stack "DO_SCALAR_RELOP_int" in
  ifb oper = EQOP then
    result_success S (ScalarLogical globals (decide (x = y)))
  else ifb oper = NEOP then
    result_success S (ScalarLogical globals (decide (x <> y)))
  else ifb oper = LTOP then
    result_success S (ScalarLogical globals (decide (x < y)))
  else ifb oper = GTOP then
    result_success S (ScalarLogical globals (decide (x > y)))
  else ifb oper = LEOP then
    result_success S (ScalarLogical globals (decide (x <= y)))
  else ifb oper = GEOP then
    result_success S (ScalarLogical globals (decide (x >= y)))
  else result_impossible S "Unknown constructor.".

Definition DO_SCALAR_RELOP_double S (oper : int) (x y : double) :=
  add%stack "DO_SCALAR_RELOP_double" in
  ifb oper = EQOP then
    result_success S (ScalarLogical globals (decide (x = y)))
  else ifb oper = NEOP then
    result_success S (ScalarLogical globals (decide (x <> y)))
  else ifb oper = LTOP then
    result_success S (ScalarLogical globals (decide (x < y)))
  else ifb oper = GTOP then
    result_success S (ScalarLogical globals (decide (x > y)))
  else ifb oper = LEOP then
    result_success S (ScalarLogical globals (decide (x <= y)))
  else ifb oper = GEOP then
    result_success S (ScalarLogical globals (decide (x >= y)))
  else result_impossible S "Unknown constructor.".

Definition ISNA_INT x :=
  decide (x = NA_INTEGER).

(** The next three functions are originally untyped as they are defined
  in preprocessor.  Their translations into Coq are thus more flexible. **)
Definition NR_HELPER T1 T2 S (op : T1 -> T2 -> bool) ans n n1 n2 read1 read2 (ISNA1 ISNA2 : _ -> bool) :=
  add%stack "NR_HELPER" in
  do%let for i from 0 to n - 1 do
    let i1 := i mod n1 in
    let i2 := i mod n2 in
    let%success x1 := read1 S i1 using S in
    let%success x2 := read2 S i2 using S in
    ifb ISNA1 x1 \/ ISNA2 x2 then
      write%Logical ans at i := NA_LOGICAL using S in
      result_skip S
    else
      write%Logical ans at i := op x1 x2 using S in
      result_skip S using S.

Definition NUMERIC_RELOP_int S (code : int) ans n n1 n2 read1 read2 (ISNA1 ISNA2 : int -> bool) :=
  add%stack "NUMERIC_RELOP_int" in
  ifb code = EQOP then
    NR_HELPER S (fun x1 x2 => decide (x1 = x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = NEOP then
    NR_HELPER S (fun x1 x2 => decide (x1 <> x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LTOP then
    NR_HELPER S (fun x1 x2 => decide (x1 < x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GTOP then
    NR_HELPER S (fun x1 x2 => decide (x1 > x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LEOP then
    NR_HELPER S (fun x1 x2 => decide (x1 <= x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GEOP then
    NR_HELPER S (fun x1 x2 => decide (x1 >= x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else result_impossible S "Unknown constructor.".

Definition NUMERIC_RELOP_double T1 T2 (id1 : T1 -> double) (id2 : T2 -> double) S
    (code : int) ans n n1 n2 read1 read2 ISNA1 ISNA2 :=
  add%stack "NUMERIC_RELOP_double" in
  ifb code = EQOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 = id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = NEOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 <> id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LTOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 < id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GTOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 > id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LEOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 <= id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GEOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 >= id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else result_impossible S "Unknown constructor.".

Definition numeric_relop S code s1 s2 :=
  add%stack "numeric_relop" in
  let%success n1 := XLENGTH S s1 using S in
  let%success n2 := XLENGTH S s2 using S in
  let n := ifb n1 > n2 then n1 else n2 in
  let%success ans := allocVector globals S LglSxp n using S in
  let%success s1_in := isInteger globals runs S s1 using S in
  let%success s1_lg := isLogical S s1 using S in
  let%success s2_in := isInteger globals runs S s2 using S in
  let%success s2_lg := isLogical S s2 using S in
  let readINTEGER s S i :=
    add%stack "readINTEGER" in
    read%Integer r := s at i using S in
    result_success S r in
  let readREAL s S i :=
    add%stack "readREAL" in
    read%Real r := s at i using S in
    result_success S r in
  run%success
    ifb s1_in \/ s1_lg then
      ifb s2_in \/ s2_lg then
        NUMERIC_RELOP_int S code ans n n1 n2 (readINTEGER s1) (readINTEGER s2) ISNA_INT ISNA_INT
      else
        NUMERIC_RELOP_double (id : int -> double) id S code ans n n1 n2 (readINTEGER s1) (readREAL s2) ISNA_INT ISNAN
    else ifb s2_in \/ s2_lg then
      NUMERIC_RELOP_double id (id : int -> double) S code ans n n1 n2 (readREAL s1) (readINTEGER s2) ISNAN ISNA_INT
    else
      NUMERIC_RELOP_double id id S code ans n n1 n2 (readREAL s1) (readREAL s2) ISNAN ISNAN using S in
  result_success S ans.

Definition string_relop (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  add%stack "string_relop" in
  result_not_implemented "".

Definition complex_relop (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  add%stack "complex_relop" in
  result_not_implemented "".

Definition raw_relop (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  add%stack "raw_relop" in
  result_not_implemented "".

Definition do_relop_dflt S (call op x y : SEXP) : result SEXP :=
  add%stack "do_relop_dflt" in
  let%success op_val := PRIMVAL runs S op using S in
  run%exit
    if%success IS_SIMPLE_SCALAR globals S x IntSxp using S then
      let%success ix := SCALAR_IVAL S x using S in
      if%success IS_SIMPLE_SCALAR globals S y IntSxp using S then
        let%success iy := SCALAR_IVAL S y using S in
        ifb ix = NA_INTEGER \/ iy = NA_INTEGER then
          result_rreturn S (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_int S op_val ix iy using S in
          result_rreturn S r
      else if%success IS_SIMPLE_SCALAR globals S y RealSxp using S then
        let%success dy := SCALAR_DVAL S y using S in
        ifb ix = NA_INTEGER \/ ISNAN dy then
          result_rreturn S (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double S op_val ix dy using S in
          result_rreturn S r
      else result_rskip S
    else if%success IS_SIMPLE_SCALAR globals S x RealSxp using S then
      let%success dx := SCALAR_DVAL S x using S in
      if%success IS_SIMPLE_SCALAR globals S y IntSxp using S then
        let%success iy := SCALAR_IVAL S y using S in
        ifb ISNAN dx \/ iy = NA_INTEGER then
          result_rreturn S (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double S op_val dx iy using S in
          result_rreturn S r
      else if%success IS_SIMPLE_SCALAR globals S y RealSxp using S then
        let%success dy := SCALAR_DVAL S y using S in
        ifb ISNAN dx \/ ISNAN dy then
          result_rreturn S (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double S op_val dx dy using S in
          result_rreturn S r
      else result_rskip S
    else result_rskip S using S in
  let%success nx := xlength globals runs S x using S in
  let%success ny := xlength globals runs S y using S in
  let%success typex := TYPEOF S x using S in
  let%success typey := TYPEOF S y using S in
  read%defined x_ := x using S in
  read%defined y_ := y using S in
  ifb attrib x_ = R_NilValue /\ attrib y_ = R_NilValue
      /\ (typex = RealSxp \/ typex = IntSxp)
      /\ (typey = RealSxp \/ typey = IntSxp)
      /\ nx > 0 /\ ny > 0 /\ (nx = 1 \/ ny = 1) then
    numeric_relop S op_val x y
  else
    let%success x :=
      let%success iS := isSymbol S x using S in
      let%success x_type := TYPEOF S x using S in
      ifb iS \/ x_type = LangSxp then
        let%success tmp := allocVector globals S StrSxp 1 using S in
        let%success tmp_0 :=
          if iS then
            PRINTNAME S x
          else result_not_implemented "deparse1" using S in
        run%success SET_STRING_ELT S tmp 0 tmp_0 using S in
        result_success S tmp
      else result_success S x using S in
    let%success y :=
      let%success iS := isSymbol S y using S in
      let%success y_type := TYPEOF S y using S in
      ifb iS \/ y_type = LangSxp then
        let%success tmp := allocVector globals S StrSxp 1 using S in
        let%success tmp_0 :=
          if iS then
            PRINTNAME S y
          else result_not_implemented "deparse1" using S in
        run%success SET_STRING_ELT S tmp 0 tmp_0 using S in
        result_success S tmp
      else result_success S y using S in
    let%success x :=
      if%success isNull S x using S then
        allocVector globals S IntSxp 0
      else result_success S x using S in
    let%success y :=
      if%success isNull S y using S then
        allocVector globals S IntSxp 0
      else result_success S y using S in
    let%success x_vector := isVector S x using S in
    let%success y_vector := isVector S y using S in
    ifb ~ x_vector \/ ~ y_vector then
      result_error S "Comparison is possible only for atomic and list types"
    else
      let%success x_type := TYPEOF S x using S in
      let%success y_type := TYPEOF S y using S in
      ifb x_type = ExprSxp \/ y_type = ExprSxp then
        result_error S "Comparison is now allowed for expressions"
      else
        let%success xarray := isArray globals runs S x using S in
        let%success yarray := isArray globals runs S y using S in
        let%success xts := isTs globals runs S x using S in
        let%success yts := isTs globals runs S y using S in
        let%success (dims, xnames, ynames) :=
          ifb xarray \/ yarray then
            let%success dims :=
              ifb xarray /\ yarray then
                let%success conf := conformable globals runs S x y using S in
                if negb conf then
                  result_error S "Non-conformable arrays."
                else getAttrib globals runs S x R_DimSymbol
              else ifb xarray /\ (ny <> 0 \/ nx = 0) then
                getAttrib globals runs S x R_DimSymbol
              else ifb yarray /\ (nx <> 0 \/ ny = 0) then
                getAttrib globals runs S y R_DimSymbol
              else result_success S (R_NilValue : SEXP) using S in
            let%success xnames := getAttrib globals runs S x R_DimNamesSymbol using S in
            let%success ynames := getAttrib globals runs S y R_DimNamesSymbol using S in
            result_success S (dims, xnames, ynames)
          else
            let%success xnames := getAttrib globals runs S x R_NamesSymbol using S in
            let%success ynames := getAttrib globals runs S y R_NamesSymbol using S in
            result_success S (R_NilValue : SEXP, xnames, ynames) using S in
        let%success (tsp, klass) :=
          ifb xts \/ yts then
            ifb xts /\ yts then
              let%success c := tsConform globals runs S x y using S in
              if negb c then
                result_error S "Non-conformable time-series."
              else
                let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
                let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
                result_success S (tsp, klass)
            else
              let%success x_len := xlength globals runs S x using S in
              let%success y_len := xlength globals runs S y using S in
              if xts then
                ifb x_len < y_len then
                  result_error S "Time-series/vector length mismatch."
                else
                  let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
                  let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
                  result_success S (tsp, klass)
              else
                ifb y_len < x_len then
                  result_error S "Time-series/vector length mismatch."
                else
                  let%success tsp := getAttrib globals runs S y R_TspSymbol using S in
                  let%success klass := getAttrib globals runs S y R_ClassSymbol using S in
                  result_success S (tsp, klass)
          else result_success S (NULL, NULL) using S in
        let%success x :=
          ifb nx > 0 /\ ny > 0 then
            (* A warning has been formalised out here. *)
            let%success x_str := isString S x using S in
            let%success y_str := isString S y using S in
            ifb x_str \/ y_str then
              let%success x := coerceVector globals runs S x StrSxp using S in
              let%success y := coerceVector globals runs S y StrSxp using S in
              string_relop S op_val x y
            else
              let%success x_cplx := isComplex S x using S in
              let%success y_cplx := isComplex S y using S in
              ifb x_cplx \/ y_cplx then
                let%success x := coerceVector globals runs S x CplxSxp using S in
                let%success y := coerceVector globals runs S y CplxSxp using S in
                complex_relop S op_val x y
              else
                let%success x_num := isNumeric globals runs S x using S in
                let%success y_num := isNumeric globals runs S y using S in
                let%success x_lgl := isLogical S x using S in
                let%success y_lgl := isLogical S y using S in
                ifb (x_num \/ x_lgl) /\ (y_num \/ y_lgl) then
                  numeric_relop S op_val x y
                else
                  let%success x_real := isReal S x using S in
                  let%success y_real := isReal S y using S in
                  ifb x_real \/ y_real then
                    let%success x := coerceVector globals runs S x RealSxp using S in
                    let%success y := coerceVector globals runs S y RealSxp using S in
                    numeric_relop S op_val x y
                  else
                    let%success x_int := isInteger globals runs S x using S in
                    let%success y_int := isInteger globals runs S y using S in
                    ifb x_int \/ y_int then
                      let%success x := coerceVector globals runs S x IntSxp using S in
                      let%success y := coerceVector globals runs S y IntSxp using S in
                      numeric_relop S op_val x y
                    else ifb x_lgl \/ y_lgl then
                      let%success x := coerceVector globals runs S x LglSxp using S in
                      let%success y := coerceVector globals runs S y LglSxp using S in
                      numeric_relop S op_val x y
                    else ifb x_type = RawSxp \/ y_type = RawSxp then
                      let%success x := coerceVector globals runs S x RawSxp using S in
                      let%success y := coerceVector globals runs S y RawSxp using S in
                      raw_relop S op_val x y
                    else result_error S "Comparison of these types is not implemented."
          else allocVector globals S LglSxp 0 using S in
        run%success
          ifb dims <> R_NilValue then
            run%success setAttrib globals runs S x R_DimSymbol dims using S in
            ifb xnames <> R_NilValue then
              run%success setAttrib globals runs S x R_DimNamesSymbol xnames using S in
              result_skip S
            else ifb ynames <> R_NilValue then
              run%success setAttrib globals runs S x R_DimNamesSymbol ynames using S in
              result_skip S
            else result_skip S
          else
            let%success x_len := xlength globals runs S x using S in
            let%success xnames_len := xlength globals runs S xnames using S in
            ifb xnames <> R_NilValue /\ x_len = xnames_len then
              run%success setAttrib globals runs S x R_NamesSymbol xnames using S in
              result_skip S
            else
              let%success ynames_len := xlength globals runs S ynames using S in
              ifb ynames <> R_NilValue /\ x_len = ynames_len then
                run%success setAttrib globals runs S x R_NamesSymbol ynames using S in
                result_skip S
              else result_skip S using S in
        run%success
          ifb xts \/ yts then
            run%success setAttrib globals runs S x R_TspSymbol tsp using S in
            run%success setAttrib globals runs S x R_ClassSymbol klass using S in
            result_skip S
          else result_skip S using S in
        result_success S x.

Definition do_relop S (call op args env : SEXP) : result SEXP :=
  add%stack "do_relop" in
  read%list args_car, args_cdr, _ := args using S in
  read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
  let%success argc :=
    ifb args <> R_NilValue then
      ifb args_cdr <> R_NilValue then
        ifb args_cdr_cdr = R_NilValue then
          result_success S 2
        else R_length globals runs S args
      else R_length globals runs S args
   else R_length globals runs S args using S in
  let arg1 := args_car in
  let arg2 := args_cdr_car in
  read%defined arg1_ := arg1 using S in
  read%defined arg2_ := arg1 using S in
  run%exit
    ifb attrib arg1_ <> R_NilValue \/ attrib arg2_ <> R_NilValue then
      if%defined ans := DispatchGroup globals S "Ops" call op args env using S then
        result_rreturn S ans
      else result_rskip S
    else result_rskip S using S in
  ifb argc <> 2 then
    result_error S "Operator needs two arguments."
  else do_relop_dflt S call op arg1 arg2.


(** * names.c **)

(** The function names of this section corresponds to the function names
  in the file main/names.c. **)

Definition do_internal S (call op args env : SEXP) : result SEXP :=
  add%stack "do_internal" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, _, _ := args using S in
  let s := args_car in
  let%success pl := isPairList S s using S in
  run%success
    ifb ~ pl then
      result_error S "Invalid .Internal() argument."
    else result_skip S using S in
  read%list s_car, s_cdr, _ := s using S in
  let sfun := s_car in
  let%success isym := isSymbol S sfun using S in
  run%success
    ifb ~ isym then
      result_error S "Invalid .Internal() argument."
    else result_skip S using S in
  read%sym _, sfun_sym := sfun using S in
  run%success
    ifb sym_internal sfun_sym = R_NilValue then
      result_error S "There is no such .Internal() function."
    else result_skip S using S in
  let%success args :=
    let%success sfun_internal_type := TYPEOF S (sym_internal sfun_sym) using S in
    ifb sfun_internal_type = BuiltinSxp then
      evalList globals runs S s_cdr env call 0
    else result_success S s_cdr using S in
  let%success f := PRIMFUN runs S (sym_internal sfun_sym) using S in
  let%success ans := f S s (sym_internal sfun_sym) args env using S in
  result_success S ans.


Fixpoint R_Primitive_loop S R_FunTab primname lmi :=
  let i := ArrayList.length R_FunTab - lmi in
  (** For termination, the loop variable has been reversed.
    In C, the loop variable is [i] and not [lmi = ArrayList.length R_FunTab - i]. **)
  match lmi with
  | 0 =>
    (** [i = ArrayList.length R_FunTab] **)
    result_success S (R_NilValue : SEXP)
  | S lmi =>
    let c := ArrayList.read R_FunTab i in
    ifb fun_name c = primname then
      if funtab_eval_arg_internal (fun_eval c) then
        result_success S (R_NilValue : SEXP)
      else
        let%success prim :=
          mkPRIMSXP globals runs S i (funtab_eval_arg_eval (fun_eval c)) using S in
        result_success S prim
    else R_Primitive_loop S R_FunTab primname lmi
  end.

Definition R_Primitive S primname :=
  add%stack "R_Primitive" in
  let%success R_FunTab := get_R_FunTab runs S using S in
  R_Primitive_loop S R_FunTab primname (ArrayList.length R_FunTab).

Definition do_primitive S (call op args env : SEXP) : result SEXP :=
  add%stack "do_primitive" in
  run%success Rf_checkArityCall S op args call using S in
  read%list args_car, _, _ := args using S in
  let name := args_car in
  let%success ist := isString S name using S in
  let%success len := LENGTH globals S name using S in
  ifb ~ ist \/ len <> 1 then
    result_error S "String argument required."
  else
    let%success strel := STRING_ELT S name 0 using S in
    ifb strel = R_NilValue then
      result_error S "String argument required."
    else
      let%success strel_ := CHAR S strel using S in
      let%success prim := R_Primitive S strel_ using S in
      ifb prim = R_NilValue then
        result_error S "No such primitive function."
      else result_success S prim.


(** In contrary to the original C, this function here takes as argument
  the structure of type [funtab_cell] in addition to its range in the
  array [R_FunTab]. **)
Definition installFunTab S c offset : result unit :=
  add%stack "installFunTab" in
  let%success prim :=
    mkPRIMSXP globals runs S offset (funtab_eval_arg_eval (fun_eval c)) using S in
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

Definition Spec_name :=
  [ "if" ; "while" ; "repeat" ; "for" ; "break" ; "next" ; "return" ; "function" ;
    "(" ; "{" ;
    "+" ; "-" ; "*" ; "/" ; "^" ; "%%" ; "%/%" ; "%*%" ; ":" ;
    "==" ; "!=" ; "<" ; ">" ; "<=" ; ">=" ;
    "&" ; "|" ; "&&" ; "||" ; "!" ;
    "<-" ; "<<-" ; "=" ;
    "$" ; "[" ; "[[" ;
    "$<-" ; "[<-" ; "[[<-" ]%string.

End Parameters.


(** * Closing the Loop **)

Definition dummy_function name (_ : Globals) (_ : runs_type)
    (S : state) (call op args rho : SEXP) : result SEXP :=
  add%stack name in
  result_not_implemented "".

Local Instance funtab_cell_Inhab : Inhab funtab_cell.
  apply prove_Inhab. constructors; try typeclass; constructors; typeclass.
Defined.

Fixpoint runs max_step globals : runs_type :=
  match max_step with
  | O => {|
      runs_while_loop := fun _ S _ _ _ => result_bottom S ;
      runs_set_longjump := fun _ S _ _ _ => result_bottom S ;
      runs_eval := fun S _ _ => result_bottom S ;
      runs_inherits := fun S _ _ => result_bottom S ;
      runs_getAttrib := fun S _ _ => result_bottom S ;
      runs_R_cycle_detected := fun S _ _ => result_bottom S ;
      runs_duplicate1 := fun S _ _ => result_bottom S ;
      runs_stripAttrib := fun S _ _ => result_bottom S ;
      runs_evalseq := fun S _ _ _ _ => result_bottom S ;
      runs_R_isMissing := fun S _ _ => result_bottom S ;
      runs_AnswerType := fun S _ _ _ _ _ => result_bottom S ;
      runs_ListAnswer := fun S _ _ _ _ => result_bottom S ;
      runs_StringAnswer := fun S _ _ _ => result_bottom S ;
      runs_LogicalAnswer := fun S _ _ _ => result_bottom S ;
      runs_IntegerAnswer := fun S _ _ _ => result_bottom S ;
      runs_RealAnswer := fun S _ _ _ => result_bottom S ;
      runs_ComplexAnswer := fun S _ _ _ => result_bottom S ;
      runs_RawAnswer := fun S _ _ _ => result_bottom S ;
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
      runs_while_loop := wrap_dep (fun _ => while_loop) ;
      runs_set_longjump := wrap_dep (fun _ => set_longjump) ;
      runs_eval := wrap eval ;
      runs_inherits := wrap inherits ;
      runs_getAttrib := wrap getAttrib ;
      runs_R_cycle_detected := wrap R_cycle_detected ;
      runs_duplicate1 := wrap duplicate1 ;
      runs_stripAttrib := wrap stripAttrib ;
      runs_evalseq := wrap evalseq ;
      runs_R_isMissing := wrap R_isMissing ;
      runs_AnswerType := wrap AnswerType ;
      runs_ListAnswer := wrap ListAnswer ;
      runs_StringAnswer := wrap StringAnswer ;
      runs_LogicalAnswer := wrap LogicalAnswer ;
      runs_IntegerAnswer := wrap IntegerAnswer ;
      runs_RealAnswer := wrap RealAnswer ;
      runs_ComplexAnswer := wrap ComplexAnswer ;
      runs_RawAnswer := wrap RawAnswer ;
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
          Some (ArrayList.from_list [

              rdecl "if" do_if (0)%Z eval200 (-1)%Z PP_IF PREC_FN true ;
              rdecl "while" do_while (0)%Z eval100 (2)%Z PP_WHILE PREC_FN false ;
              rdecl "for" (dummy_function "do_for") (0)%Z eval100 (3)%Z PP_FOR PREC_FN false ;
              rdecl "repeat" do_repeat (0)%Z eval100 (1)%Z PP_REPEAT PREC_FN false ;
              rdecl "break" do_break CTXT_BREAK eval0 (0)%Z PP_BREAK PREC_FN false ;
              rdecl "next" do_break CTXT_NEXT eval0 (0)%Z PP_NEXT PREC_FN false ;
              rdecl "return" do_return (0)%Z eval0 (-1)%Z PP_RETURN PREC_FN false ;
              rdecl "function" do_function 0 eval0 (-1)%Z PP_FUNCTION PREC_FN false ;
              rdecl "<-" do_set 1 eval100 (-1)%Z PP_ASSIGN PREC_LEFT true ;
              rdecl "=" do_set 3 eval100 (-1)%Z PP_ASSIGN PREC_EQ true ;
              rdecl "<<-" do_set 2 eval100 (-1)%Z PP_ASSIGN2 PREC_LEFT true ;
              rdecl "{" do_begin (0)%Z eval200 (-1)%Z PP_CURLY PREC_FN false ;
              rdecl "(" do_paren (0)%Z eval1 (1)%Z PP_PAREN PREC_FN false ;
              rdecl ".subset" do_subset_dflt (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".subset2" (dummy_function "do_subset2_dflt") (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "[" do_subset (1)%Z eval0 (-1)%Z PP_SUBSET PREC_SUBSET false ;
              rdecl "[[" (dummy_function "do_subset2") (2)%Z eval0 (-1)%Z PP_SUBSET PREC_SUBSET false ;
              rdecl "$" (dummy_function "do_subset3") (3)%Z eval0 (2)%Z PP_DOLLAR PREC_DOLLAR false ;
              rdecl "@" (dummy_function "do_AT") (0)%Z eval0 (2)%Z PP_DOLLAR PREC_DOLLAR false ;
              rdecl "[<-" (dummy_function "do_subassign") (0)%Z eval0 (3)%Z PP_SUBASS PREC_LEFT true ;
              rdecl "[[<-" (dummy_function "do_subassign2") (1)%Z eval0 (3)%Z PP_SUBASS PREC_LEFT true ;
              rdecl "$<-" (dummy_function "do_subassign3") (1)%Z eval0 (3)%Z PP_SUBASS PREC_LEFT true ;
              rdecl "switch" (dummy_function "do_switch") (0)%Z eval200 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "browser" (dummy_function "do_browser") (0)%Z eval101 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".primTrace" (dummy_function "do_trace") (0)%Z eval101 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".primUntrace" (dummy_function "do_trace") (1)%Z eval101 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".Internal" do_internal (0)%Z eval200 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".Primitive" do_primitive (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "call" (dummy_function "do_call") (0)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "quote" (dummy_function "do_quote") (0)%Z eval0 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "substitute" (dummy_function "do_substitute") (0)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "missing" do_missing (1)%Z eval0 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "nargs" (dummy_function "do_nargs") (1)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "on.exit" (dummy_function "do_onexit") (0)%Z eval100 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "forceAndCall" (dummy_function "do_forceAndCall") (0)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "stop" (dummy_function "do_stop") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "warning" (dummy_function "do_warning") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gettext" (dummy_function "do_gettext") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ngettext" (dummy_function "do_ngettext") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bindtextdomain" (dummy_function "do_bindtextdomain") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".addCondHands" (dummy_function "do_addCondHands") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".resetCondHands" (dummy_function "do_resetCondHands") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".signalCondition" (dummy_function "do_signalCondition") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".dfltStop" (dummy_function "do_dfltStop") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".dfltWarn" (dummy_function "do_dfltWarn") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".addRestart" (dummy_function "do_addRestart") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".getRestart" (dummy_function "do_getRestart") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".invokeRestart" (dummy_function "do_invokeRestart") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".addTryHandlers" (dummy_function "do_addTryHandlers") (0)%Z eval111 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "geterrmessage" (dummy_function "do_geterrmessage") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seterrmessage" (dummy_function "do_seterrmessage") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "printDeferredWarnings" (dummy_function "do_printDeferredWarnings") (0)%Z eval111 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "interruptsSuspended" (dummy_function "do_interruptsSuspended") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.function.default" (dummy_function "do_asfunction") (0)%Z eval11 (2)%Z PP_FUNCTION PREC_FN false ;
              rdecl "debug" (dummy_function "do_debug") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "undebug" (dummy_function "do_debug") (1)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isdebugged" (dummy_function "do_debug") (2)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "debugonce" (dummy_function "do_debug") (3)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Recall" (dummy_function "do_recall") (0)%Z eval210 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "delayedAssign" (dummy_function "do_delayed") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "makeLazy" (dummy_function "do_makelazy") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "identical" (dummy_function "do_identical") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "C_tryCatchHelper" (dummy_function "do_tryCatchHelper") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "+" do_arith PLUSOP eval1 (-1)%Z PP_BINARY PREC_SUM false ;
              rdecl "-" do_arith MINUSOP eval1 (-1)%Z PP_BINARY PREC_SUM false ;
              rdecl "*" do_arith TIMESOP eval1 (2)%Z PP_BINARY PREC_PROD false ;
              rdecl "/" do_arith DIVOP eval1 (2)%Z PP_BINARY2 PREC_PROD false ;
              rdecl "^" do_arith POWOP eval1 (2)%Z PP_BINARY2 PREC_POWER true ;
              rdecl "%%" do_arith MODOP eval1 (2)%Z PP_BINARY2 PREC_PERCENT false ;
              rdecl "%/%" do_arith IDIVOP eval1 (2)%Z PP_BINARY2 PREC_PERCENT false ;
              rdecl "%*%" (dummy_function "do_matprod") (0)%Z eval1 (2)%Z PP_BINARY PREC_PERCENT false ;

              rdecl "==" do_relop EQOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl "!=" do_relop NEOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl "<" do_relop LTOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl "<=" do_relop LEOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl ">=" do_relop GEOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl ">" do_relop GTOP eval1 (2)%Z PP_BINARY PREC_COMPARE false ;
              rdecl "&" (dummy_function "do_logic") (1)%Z eval1 (2)%Z PP_BINARY PREC_AND false ;
              rdecl "|" (dummy_function "do_logic") (2)%Z eval1 (2)%Z PP_BINARY PREC_OR false ;
              rdecl "!" (dummy_function "do_logic") (3)%Z eval1 (1)%Z PP_UNARY PREC_NOT false ;

              rdecl "&&" (dummy_function "do_logic2") (1)%Z eval0 (2)%Z PP_BINARY PREC_AND false ;
              rdecl "||" (dummy_function "do_logic2") (2)%Z eval0 (2)%Z PP_BINARY PREC_OR false ;
              rdecl ":" do_colon (0)%Z eval1 (2)%Z PP_BINARY2 PREC_COLON false ;

              rdecl "~" (dummy_function "do_tilde") (0)%Z eval0 (-1)%Z PP_BINARY PREC_TILDE false ;

              rdecl "all" (dummy_function "do_logic3") (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "any" (dummy_function "do_logic3") (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "...elt" (dummy_function "do_dotsElt") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "...length" (dummy_function "do_dotsLength") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "length" (dummy_function "do_length") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "length<-" (dummy_function "do_lengthgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "c" do_c (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "oldClass" (dummy_function "do_class") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "oldClass<-" (dummy_function "do_classgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "class" (dummy_function "R_do_data_class") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".cache_class" (dummy_function "R_do_data_class") (1)%Z	eval1 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "class<-" (dummy_function "R_do_set_class")	0 eval1 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unclass" (dummy_function "do_unclass") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "names" (dummy_function "do_names") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "names<-" (dummy_function "do_namesgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "dimnames" (dummy_function "do_dimnames") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dimnames<-" (dummy_function "do_dimnamesgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "dim" (dummy_function "do_dim") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dim<-" (dummy_function "do_dimgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "attributes" (dummy_function "do_attributes") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "attributes<-" (dummy_function "do_attributesgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "attr" do_attr (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "attr<-" do_attrgets (0)%Z eval1 (3)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "@<-" do_attrgets (1)%Z eval0 (3)%Z PP_SUBASS PREC_LEFT true ;
              rdecl "levels<-" (dummy_function "do_levelsgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;

              rdecl "vector" (dummy_function "do_makevector") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "complex" (dummy_function "do_complex") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "matrix" (dummy_function "do_matrix") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "array" (dummy_function "do_array") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "diag" (dummy_function "do_diag") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "backsolve" (dummy_function "do_backsolve") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "max.col" (dummy_function "do_maxcol") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "row" (dummy_function "do_rowscols") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "col" (dummy_function "do_rowscols") (2)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unlist" (dummy_function "do_unlist") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cbind" (dummy_function "do_bind") (1)%Z eval10 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rbind" (dummy_function "do_bind") (2)%Z eval10 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "drop" (dummy_function "do_drop") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "all.names" (dummy_function "do_allnames") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "comment" (dummy_function "do_comment") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "comment<-" (dummy_function "do_commentgets") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "get" (dummy_function "do_get") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "get0" (dummy_function "do_get") (2)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "mget" (dummy_function "do_mget") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "exists" (dummy_function "do_get") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "assign" (dummy_function "do_assign") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "list2env" (dummy_function "do_list2env") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "remove" (dummy_function "do_remove") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "duplicated" (dummy_function "do_duplicated") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unique" (dummy_function "do_duplicated") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "anyDuplicated" (dummy_function "do_duplicated") (2)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "anyNA" (dummy_function "do_anyNA") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "which" (dummy_function "do_which") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "which.min" (dummy_function "do_first_min") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pmin" (dummy_function "do_pmin") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pmax" (dummy_function "do_pmin") (1)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "which.max" (dummy_function "do_first_min") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "match" (dummy_function "do_match") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pmatch" (dummy_function "do_pmatch") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "charmatch" (dummy_function "do_charmatch") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "match.call" (dummy_function "do_matchcall") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "crossprod" (dummy_function "do_matprod") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tcrossprod" (dummy_function "do_matprod") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lengths" (dummy_function "do_lengths") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "attach" (dummy_function "do_attach") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "detach" (dummy_function "do_detach") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "search" (dummy_function "do_search") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setFileTime" (dummy_function "do_setFileTime") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "round" (dummy_function "do_Math2") (10001)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "signif" (dummy_function "do_Math2") (10004)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "log" (dummy_function "do_log") (10003)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "log10" (dummy_function "do_log1arg") (10)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "log2" (dummy_function "do_log1arg") (2)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "abs" (dummy_function "do_abs") (6)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "floor" do_math1 (1)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ceiling" do_math1 (2)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sqrt" do_math1 (3)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sign" do_math1 (4)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "trunc" (dummy_function "do_trunc") (5)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "exp" do_math1 (10)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "expm1" do_math1 (11)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "log1p" do_math1 (12)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "cos" do_math1 (20)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sin" do_math1 (21)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tan" do_math1 (22)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "acos" do_math1 (23)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "asin" do_math1 (24)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "atan" do_math1 (25)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "cosh" do_math1 (30)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sinh" do_math1 (31)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tanh" do_math1 (32)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "acosh" do_math1 (33)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "asinh" do_math1 (34)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "atanh" do_math1 (35)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "lgamma" do_math1 (40)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gamma" do_math1 (41)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "digamma" do_math1 (42)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "trigamma" do_math1 (43)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "cospi" do_math1 (47)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sinpi" do_math1 (48)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tanpi" do_math1 (49)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "atan2" (dummy_function "do_math2") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "lbeta" (dummy_function "do_math2") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "beta" (dummy_function "do_math2") (3)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lchoose" (dummy_function "do_math2") (4)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "choose" (dummy_function "do_math2") (5)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dchisq" (dummy_function "do_math2") (6)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pchisq" (dummy_function "do_math2") (7)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qchisq" (dummy_function "do_math2") (8)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dexp" (dummy_function "do_math2") (9)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pexp" (dummy_function "do_math2") (10)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qexp" (dummy_function "do_math2") (11)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dgeom" (dummy_function "do_math2") (12)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pgeom" (dummy_function "do_math2") (13)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qgeom" (dummy_function "do_math2") (14)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dpois" (dummy_function "do_math2") (15)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ppois" (dummy_function "do_math2") (16)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qpois" (dummy_function "do_math2") (17)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dt" (dummy_function "do_math2") (18)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pt" (dummy_function "do_math2") (19)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qt" (dummy_function "do_math2") (20)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dsignrank" (dummy_function "do_math2") (21)%Z eval11 (2+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "psignrank" (dummy_function "do_math2") (22)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qsignrank" (dummy_function "do_math2") (23)%Z eval11 (2+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "besselJ" (dummy_function "do_math2") (24)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "besselY" (dummy_function "do_math2") (25)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "psigamma" (dummy_function "do_math2") (26)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "Re" (dummy_function "do_cmathfuns") (1)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Im" (dummy_function "do_cmathfuns") (2)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Mod" (dummy_function "do_cmathfuns") (3)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Arg" (dummy_function "do_cmathfuns") (4)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Conj" (dummy_function "do_cmathfuns") (5)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dbeta" (dummy_function "do_math3") (1)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pbeta" (dummy_function "do_math3") (2)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qbeta" (dummy_function "do_math3") (3)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dbinom" (dummy_function "do_math3") (4)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pbinom" (dummy_function "do_math3") (5)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qbinom" (dummy_function "do_math3") (6)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dcauchy" (dummy_function "do_math3") (7)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pcauchy" (dummy_function "do_math3") (8)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qcauchy" (dummy_function "do_math3") (9)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "df" (dummy_function "do_math3") (10)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pf" (dummy_function "do_math3") (11)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qf" (dummy_function "do_math3") (12)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dgamma" (dummy_function "do_math3") (13)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pgamma" (dummy_function "do_math3") (14)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qgamma" (dummy_function "do_math3") (15)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dlnorm" (dummy_function "do_math3") (16)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "plnorm" (dummy_function "do_math3") (17)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qlnorm" (dummy_function "do_math3") (18)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dlogis" (dummy_function "do_math3") (19)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "plogis" (dummy_function "do_math3") (20)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qlogis" (dummy_function "do_math3") (21)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnbinom" (dummy_function "do_math3") (22)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnbinom" (dummy_function "do_math3") (23)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnbinom" (dummy_function "do_math3") (24)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnorm" (dummy_function "do_math3") (25)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnorm" (dummy_function "do_math3") (26)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnorm" (dummy_function "do_math3") (27)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dunif" (dummy_function "do_math3") (28)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "punif" (dummy_function "do_math3") (29)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qunif" (dummy_function "do_math3") (30)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dweibull" (dummy_function "do_math3") (31)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pweibull" (dummy_function "do_math3") (32)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qweibull" (dummy_function "do_math3") (33)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnchisq" (dummy_function "do_math3") (34)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnchisq" (dummy_function "do_math3") (35)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnchisq" (dummy_function "do_math3") (36)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnt" (dummy_function "do_math3") (37)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnt" (dummy_function "do_math3") (38)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnt" (dummy_function "do_math3") (39)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dwilcox" (dummy_function "do_math3") (40)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pwilcox" (dummy_function "do_math3") (41)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qwilcox" (dummy_function "do_math3") (42)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "besselI" (dummy_function "do_math3") (43)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "besselK" (dummy_function "do_math3") (44)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnbinom_mu" (dummy_function "do_math3") (45)%Z eval11 (3+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnbinom_mu" (dummy_function "do_math3") (46)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnbinom_mu" (dummy_function "do_math3") (47)%Z eval11 (3+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dhyper" (dummy_function "do_math4") (1)%Z eval11 (4+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "phyper" (dummy_function "do_math4") (2)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qhyper" (dummy_function "do_math4") (3)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnbeta" (dummy_function "do_math4") (4)%Z eval11 (4+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnbeta" (dummy_function "do_math4") (5)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnbeta" (dummy_function "do_math4") (6)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dnf" (dummy_function "do_math4") (7)%Z eval11 (4+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pnf" (dummy_function "do_math4") (8)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qnf" (dummy_function "do_math4") (9)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "dtukey" (dummy_function "do_math4") (10)%Z eval11 (4+1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ptukey" (dummy_function "do_math4") (11)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qtukey" (dummy_function "do_math4") (12)%Z eval11 (4+2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "rchisq" (dummy_function "do_random1") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rexp" (dummy_function "do_random1") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rgeom" (dummy_function "do_random1") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rpois" (dummy_function "do_random1") (3)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rt" (dummy_function "do_random1") (4)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rsignrank" (dummy_function "do_random1") (5)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "rbeta" (dummy_function "do_random2") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rbinom" (dummy_function "do_random2") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rcauchy" (dummy_function "do_random2") (2)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rf" (dummy_function "do_random2") (3)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rgamma" (dummy_function "do_random2") (4)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rlnorm" (dummy_function "do_random2") (5)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rlogis" (dummy_function "do_random2") (6)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rnbinom" (dummy_function "do_random2") (7)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rnbinom_mu" (dummy_function "do_random2") (13)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rnchisq" (dummy_function "do_random2") (12)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rnorm" (dummy_function "do_random2") (8)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "runif" (dummy_function "do_random2") (9)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rweibull" (dummy_function "do_random2") (10)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rwilcox" (dummy_function "do_random2") (11)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "rhyper" (dummy_function "do_random3") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;

              rdecl "sample" (dummy_function "do_sample") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sample2" (dummy_function "do_sample2") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "RNGkind" (dummy_function "do_RNGkind") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "set.seed" (dummy_function "do_setseed") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "sum" (dummy_function "do_summary") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "min" (dummy_function "do_summary") (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "max" (dummy_function "do_summary") (3)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "prod" (dummy_function "do_summary") (4)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "mean" (dummy_function "do_summary") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "range" (dummy_function "do_range") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "cumsum" (dummy_function "do_cum") (1)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cumprod" (dummy_function "do_cum") (2)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cummax" (dummy_function "do_cum") (3)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cummin" (dummy_function "do_cum") (4)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "as.character" (dummy_function "do_asatomic") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.integer" (dummy_function "do_asatomic") (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.double" (dummy_function "do_asatomic") (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.numeric" (dummy_function "do_asatomic") (2)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.complex" (dummy_function "do_asatomic") (3)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.logical" (dummy_function "do_asatomic") (4)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.raw" (dummy_function "do_asatomic") (5)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.call" (dummy_function "do_ascall") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.environment" (dummy_function "do_as_environment") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "storage.mode<-" (dummy_function "do_storage_mode") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "asCharacterFactor" (dummy_function "do_asCharacterFactor") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "as.vector" (dummy_function "do_asvector") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "paste" (dummy_function "do_paste") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "paste0" (dummy_function "do_paste") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.path" (dummy_function "do_filepath") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "format" (dummy_function "do_format") (0)%Z eval11 (9)%Z PP_FUNCALL PREC_FN false ;
              rdecl "format.info" (dummy_function "do_formatinfo") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "cat" do_cat (0)%Z eval111 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "do.call" (dummy_function "do_docall") (0)%Z eval211 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "nchar" (dummy_function "do_nchar") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "nzchar" (dummy_function "do_nzchar") (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "substr" (dummy_function "do_substr") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "startsWith" (dummy_function "do_startsWith") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "endsWith" (dummy_function "do_startsWith") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "substr<-" (dummy_function "do_substrgets") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strsplit" (dummy_function "do_strsplit") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "abbreviate" (dummy_function "do_abbrev") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "make.names" (dummy_function "do_makenames") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pcre_config" (dummy_function "do_pcre_config") (1)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "grep" (dummy_function "do_grep") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "grepl" (dummy_function "do_grep") (1)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "grepRaw" (dummy_function "do_grepraw") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sub" (dummy_function "do_gsub") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gsub" (dummy_function "do_gsub") (1)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "regexpr" (dummy_function "do_regexpr") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gregexpr" (dummy_function "do_regexpr") (1)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "regexec" (dummy_function "do_regexec") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "agrep" (dummy_function "do_agrep") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "agrepl" (dummy_function "do_agrep") (1)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "adist" (dummy_function "do_adist") (1)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "aregexec" (dummy_function "do_aregexec") (1)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tolower" (dummy_function "do_tolower") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "toupper" (dummy_function "do_tolower") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "chartr" (dummy_function "do_chartr") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sprintf" (dummy_function "do_sprintf") (1)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "make.unique" (dummy_function "do_makeunique") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "charToRaw" (dummy_function "do_charToRaw") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawToChar" (dummy_function "do_rawToChar") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawShift" (dummy_function "do_rawShift") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "intToBits" (dummy_function "do_intToBits") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawToBits" (dummy_function "do_rawToBits") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "packBits" (dummy_function "do_packBits") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "utf8ToInt" (dummy_function "do_utf8ToInt") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "intToUtf8" (dummy_function "do_intToUtf8") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "validUTF8" (dummy_function "do_validUTF8") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "validEnc" (dummy_function "do_validEnc") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "encodeString" (dummy_function "do_encodeString") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "iconv" (dummy_function "do_iconv") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strtrim" (dummy_function "do_strtrim") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strtoi" (dummy_function "do_strtoi") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strrep" (dummy_function "do_strrep") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.null" do_is NilSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.logical" do_is LglSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.integer" do_is IntSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.double" do_is RealSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.complex" do_is CplxSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.character" do_is StrSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.symbol" do_is SymSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.name" do_is SymSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.environment" do_is EnvSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.list" do_is VecSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.pairlist" do_is ListSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.expression" do_is ExprSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.raw" do_is RawSxp eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.object" do_is (50)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isS4" do_is (51)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.numeric" do_is (100)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.matrix" do_is (101)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.array" do_is (102)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.atomic" do_is (200)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.recursive" do_is (201)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.call" do_is (300)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.language" do_is (301)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.function" do_is (302)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.single" do_is (999)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.na" do_isna (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.nan" do_isnan (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.finite" (dummy_function "do_isfinite") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.infinite" (dummy_function "do_isinfinite") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "is.vector" do_isvector (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "proc.time" (dummy_function "do_proctime") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gc.time" (dummy_function "do_gctime") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "withVisible" (dummy_function "do_withVisible") (1)%Z eval10 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "expression" (dummy_function "do_expression") (1)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "interactive" (dummy_function "do_interactive") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "invisible" (dummy_function "do_invisible") (0)%Z eval101 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rep" (dummy_function "do_rep") (0)%Z eval0 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rep.int" (dummy_function "do_rep_int") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rep_len" (dummy_function "do_rep_len") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seq.int" (dummy_function "do_seq") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seq_len" (dummy_function "do_seq_len") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seq_along" (dummy_function "do_seq_along") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "list" do_makelist (1)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "xtfrm" (dummy_function "do_xtfrm") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "enc2native" (dummy_function "do_enc2") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "enc2utf8" (dummy_function "do_enc2") (1)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "emptyenv" (dummy_function "do_emptyenv") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "baseenv" (dummy_function "do_baseenv") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "globalenv" (dummy_function "do_globalenv") (0)%Z eval1 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "environment<-" (dummy_function "do_envirgets") (0)%Z eval1 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "pos.to.env" (dummy_function "do_pos2env") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "eapply" (dummy_function "do_eapply") (0)%Z eval10 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lapply" (dummy_function "do_lapply") (0)%Z eval10 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "vapply" (dummy_function "do_vapply") (0)%Z eval10 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "mapply" (dummy_function "do_mapply") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl ".C" (dummy_function "do_dotCode") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".Fortran" (dummy_function "do_dotCode") (1)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".External" (dummy_function "do_External") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".External2" (dummy_function "do_External") (1)%Z eval201 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".Call" (dummy_function "do_dotcall") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".External.graphics" (dummy_function "do_Externalgr") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl ".Call.graphics" (dummy_function "do_dotcallgr") (0)%Z eval1 (-1)%Z PP_FOREIGN PREC_FN false ;

              rdecl "Version" (dummy_function "do_version") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "machine" (dummy_function "do_machine") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "commandArgs" (dummy_function "do_commandArgs") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "internalsID" (dummy_function "do_internalsID") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;

              rdecl "system" (dummy_function "do_system") (0)%Z eval211 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "parse" (dummy_function "do_parse") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;

              rdecl "save" (dummy_function "do_save") (0)%Z eval111 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "saveToConn" (dummy_function "do_saveToConn") (0)%Z eval111 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "load" (dummy_function "do_load") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "loadFromConn2" (dummy_function "do_loadFromConn2") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "serializeToConn" (dummy_function "do_serializeToConn") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unserializeFromConn" (dummy_function "do_unserializeFromConn") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "deparse" (dummy_function "do_deparse") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dput" (dummy_function "do_dput") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dump" (dummy_function "do_dump") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "quit" (dummy_function "do_quit") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readline" (dummy_function "do_readln") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "print.default" (dummy_function "do_printdefault") (0)%Z eval111 (9)%Z PP_FUNCALL PREC_FN false ;
              rdecl "print.function" (dummy_function "do_printfunction") (0)%Z eval111 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "prmatrix" (dummy_function "do_prmatrix") (0)%Z eval111 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gc" (dummy_function "do_gc") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gcinfo" (dummy_function "do_gcinfo") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gctorture" (dummy_function "do_gctorture") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gctorture2" (dummy_function "do_gctorture2") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "memory.profile" (dummy_function "do_memoryprofile") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "split" (dummy_function "do_split") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.loaded" (dummy_function "do_isloaded") (0)%Z eval11 (-1)%Z PP_FOREIGN PREC_FN false ;
              rdecl "recordGraphics" (dummy_function "do_recordGraphics") (0)%Z eval211 (3)%Z PP_FOREIGN PREC_FN false ;
              rdecl "dyn.load" (dummy_function "do_dynload") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dyn.unload" (dummy_function "do_dynunload") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "ls" (dummy_function "do_ls") (1)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "typeof" do_typeof (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "eval" do_eval (0)%Z eval211 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "returnValue" (dummy_function "do_returnValue") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.parent" (dummy_function "do_sys") (1)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.call" (dummy_function "do_sys") (2)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.frame" (dummy_function "do_sys") (3)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.nframe" (dummy_function "do_sys") (4)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.calls" (dummy_function "do_sys") (5)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.frames" (dummy_function "do_sys") (6)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.on.exit" (dummy_function "do_sys") (7)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.parents" (dummy_function "do_sys") (8)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sys.function" (dummy_function "do_sys") (9)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "traceback" (dummy_function "do_traceback") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "browserText" (dummy_function "do_sysbrowser") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "browserCondition" (dummy_function "do_sysbrowser") (2)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "browserSetDebug" (dummy_function "do_sysbrowser") (3)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "parent.frame" (dummy_function "do_parentframe") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sort" (dummy_function "do_sort") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.unsorted" (dummy_function "do_isunsorted") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "psort" (dummy_function "do_psort") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qsort" (dummy_function "do_qsort") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "radixsort" (dummy_function "do_radixsort") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "order" (dummy_function "do_order") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rank" (dummy_function "do_rank") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "scan" (dummy_function "do_scan") (0)%Z eval11 (19)%Z PP_FUNCALL PREC_FN false ;
              rdecl "t.default" (dummy_function "do_transpose") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "aperm" (dummy_function "do_aperm") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "builtins" (dummy_function "do_builtins") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "args" (dummy_function "do_args") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "formals" (dummy_function "do_formals") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "body" (dummy_function "do_body") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bodyCode" (dummy_function "do_bodyCode") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "environment" (dummy_function "do_envir") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "environmentName" (dummy_function "do_envirName") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "env2list" (dummy_function "do_env2list") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "reg.finalizer" (dummy_function "do_regFinaliz") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "options" (dummy_function "do_options") (0)%Z eval211 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getOption" (dummy_function "do_getOption") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sink" (dummy_function "do_sink") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sink.number" (dummy_function "do_sinknumber") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rapply" (dummy_function "do_rapply") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "islistfactor" (dummy_function "do_islistfactor") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "colSums" (dummy_function "do_colsum") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "colMeans" (dummy_function "do_colsum") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rowSums" (dummy_function "do_colsum") (2)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rowMeans" (dummy_function "do_colsum") (3)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tracemem" (dummy_function "do_tracemem") (0)%Z eval1 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "retracemem" (dummy_function "do_retracemem") (0)%Z eval201 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "untracemem" (dummy_function "do_untracemem") (0)%Z eval101 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "inspect" (dummy_function "do_inspect") (0)%Z eval111 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "address" (dummy_function "do_address") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "refcnt" (dummy_function "do_refcnt") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "merge" (dummy_function "do_merge") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "capabilities" (dummy_function "do_capabilities") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "capabilitiesX11" (dummy_function "do_capabilitiesX11") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "new.env" (dummy_function "do_newenv") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "parent.env" (dummy_function "do_parentenv") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "parent.env<-" (dummy_function "do_parentenvgets") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_LEFT true ;
              rdecl "topenv" (dummy_function "do_topenv") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "l10n_info" (dummy_function "do_l10n_info") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Cstack_info" (dummy_function "do_Cstack_info") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "mmap_file" (dummy_function "do_mmap_file") (0)%Z eval11 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "munmap_file" (dummy_function "do_munmap_file") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "wrap_meta" (dummy_function "do_wrap_meta") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "file.show" (dummy_function "do_fileshow") (0)%Z eval111 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.create" (dummy_function "do_filecreate") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.remove" (dummy_function "do_fileremove") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.rename" (dummy_function "do_filerename") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.append" (dummy_function "do_fileappend") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.symlink" (dummy_function "do_filesymlink") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.link" (dummy_function "do_filelink") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.copy" (dummy_function "do_filecopy") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "list.files" (dummy_function "do_listfiles") (0)%Z eval11 (8)%Z PP_FUNCALL PREC_FN false ;
              rdecl "list.dirs" (dummy_function "do_listdirs") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.exists" (dummy_function "do_fileexists") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.choose" (dummy_function "do_filechoose") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.info" (dummy_function "do_fileinfo") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file.access" (dummy_function "do_fileaccess") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dir.exists" (dummy_function "do_direxists") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dir.create" (dummy_function "do_dircreate") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tempfile" (dummy_function "do_tempfile") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tempdir" (dummy_function "do_tempdir") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "R.home" (dummy_function "do_Rhome") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "date" (dummy_function "do_date") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.getenv" (dummy_function "do_getenv") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.setenv" (dummy_function "do_setenv") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.unsetenv" (dummy_function "do_unsetenv") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getwd" (dummy_function "do_getwd") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setwd" (dummy_function "do_setwd") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "basename" (dummy_function "do_basename") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "dirname" (dummy_function "do_dirname") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.chmod" (dummy_function "do_syschmod") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.umask" (dummy_function "do_sysumask") (0)%Z eval211 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.readlink" (dummy_function "do_readlink") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.info" (dummy_function "do_sysinfo") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.sleep" (dummy_function "do_syssleep") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.getlocale" (dummy_function "do_getlocale") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.setlocale" (dummy_function "do_setlocale") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.localeconv" (dummy_function "do_localeconv") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "path.expand" (dummy_function "do_pathexpand") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.getpid" (dummy_function "do_sysgetpid") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "normalizePath" (dummy_function "do_normalizepath") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Sys.glob" (dummy_function "do_glob") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unlink" (dummy_function "do_unlink") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "polyroot" (dummy_function "do_polyroot") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "inherits" (dummy_function "do_inherits") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "UseMethod" (dummy_function "do_usemethod") (0)%Z eval200 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "NextMethod" (dummy_function "do_nextmethod") (0)%Z eval210 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "standardGeneric" (dummy_function "do_standardGeneric") (0)%Z eval201 (-1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "Sys.time" (dummy_function "do_systime") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.POSIXct" (dummy_function "do_asPOSIXct") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "as.POSIXlt" (dummy_function "do_asPOSIXlt") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "format.POSIXlt" (dummy_function "do_formatPOSIXlt") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "strptime" (dummy_function "do_strptime") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "Date2POSIXlt" (dummy_function "do_D2POSIXlt") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "POSIXlt2Date" (dummy_function "do_POSIXlt2D") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "mkCode" (dummy_function "do_mkcode") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bcClose" (dummy_function "do_bcclose") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "is.builtin.internal" (dummy_function "do_is_builtin_internal") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "disassemble" (dummy_function "do_disassemble") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bcVersion" (dummy_function "do_bcversion") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "load.from.file" (dummy_function "do_loadfile") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "save.to.file" (dummy_function "do_savefile") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "growconst" (dummy_function "do_growconst") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "putconst" (dummy_function "do_putconst") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getconst" (dummy_function "do_getconst") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "enableJIT" (dummy_function "do_enablejit") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "compilePKGS" (dummy_function "do_compilepkgs") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "setNumMathThreads" (dummy_function "do_setnumthreads") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setMaxNumMathThreads" (dummy_function "do_setmaxnumthreads") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "stdin" (dummy_function "do_stdin") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "stdout" (dummy_function "do_stdout") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "stderr" (dummy_function "do_stderr") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isatty" (dummy_function "do_isatty") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readLines" (dummy_function "do_readLines") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "writeLines" (dummy_function "do_writelines") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readBin" (dummy_function "do_readbin") (0)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "writeBin" (dummy_function "do_writebin") (0)%Z eval211 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readChar" (dummy_function "do_readchar") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "writeChar" (dummy_function "do_writechar") (0)%Z eval211 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "open" (dummy_function "do_open") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isOpen" (dummy_function "do_isopen") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isIncomplete" (dummy_function "do_isincomplete") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isSeekable" (dummy_function "do_isseekable") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "close" (dummy_function "do_close") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "flush" (dummy_function "do_flush") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "file" (dummy_function "do_url") (1)%Z eval11 (6)%Z PP_FUNCALL PREC_FN false ;
              rdecl "url" (dummy_function "do_url") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pipe" (dummy_function "do_pipe") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "fifo" (dummy_function "do_fifo") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gzfile" (dummy_function "do_gzfile") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bzfile" (dummy_function "do_gzfile") (1)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "xzfile" (dummy_function "do_gzfile") (2)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unz" (dummy_function "do_unz") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "seek" (dummy_function "do_seek") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "truncate" (dummy_function "do_truncate") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pushBack" (dummy_function "do_pushback") (0)%Z eval111 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "clearPushBack" (dummy_function "do_clearpushback") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pushBackLength" (dummy_function "do_pushbacklength") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawConnection" (dummy_function "do_rawconnection") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rawConnectionValue" (dummy_function "do_rawconvalue") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "textConnection" (dummy_function "do_textconnection") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "textConnectionValue" (dummy_function "do_textconvalue") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "socketConnection" (dummy_function "do_sockconn") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "sockSelect" (dummy_function "do_sockselect") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getConnection" do_getconnection (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getAllConnections" (dummy_function "do_getallconnections") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "summary.connection" (dummy_function "do_sumconnection") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "gzcon" (dummy_function "do_gzcon") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "memCompress" (dummy_function "do_memCompress") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "memDecompress" (dummy_function "do_memDecompress") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "readDCF" (dummy_function "do_readDCF") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;


              rdecl "lockEnvironment" (dummy_function "do_lockEnv") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "environmentIsLocked" (dummy_function "do_envIsLocked") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lockBinding" (dummy_function "do_lockBnd") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unlockBinding" (dummy_function "do_lockBnd") (1)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bindingIsLocked" (dummy_function "do_bndIsLocked") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "makeActiveBinding" (dummy_function "do_mkActiveBnd") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bindingIsActive" (dummy_function "do_bndIsActive") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "mkUnbound" (dummy_function "do_mkUnbound") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isNamespaceEnv" (dummy_function "do_isNSEnv") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "registerNamespace" (dummy_function "do_regNS") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unregisterNamespace" (dummy_function "do_unregNS") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getRegisteredNamespace" (dummy_function "do_getRegNS") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "isRegisteredNamespace" (dummy_function "do_getRegNS") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getNamespaceRegistry" (dummy_function "do_getNSRegistry") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "importIntoEnv" (dummy_function "do_importIntoEnv") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "env.profile" (dummy_function "do_envprofile") (0)%Z eval211 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "Encoding" (dummy_function "do_encoding") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setEncoding" (dummy_function "do_setencoding") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setTimeLimit" (dummy_function "do_setTimeLimit") (0)%Z eval111 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setSessionTimeLimit" (dummy_function "do_setSessionTimeLimit") (0)%Z eval111 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "icuSetCollate" (dummy_function "do_ICUset") (0)%Z eval111 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "icuGetCollate" (dummy_function "do_ICUget") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "readRenviron" (dummy_function "do_readEnviron") (0)%Z eval111 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "shortRowNames" (dummy_function "do_shortRowNames") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "copyDFattr" (dummy_function "do_copyDFattr") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getRegisteredRoutines" (dummy_function "do_getRegisteredRoutines") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getLoadedDLLs" (dummy_function "do_getDllTable") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getSymbolInfo" (dummy_function "do_getSymbolInfo") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl ".isMethodsDispatchOn" (dummy_function "do_S4on") (0)%Z eval1 (-1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lazyLoadDBfetch" (dummy_function "do_lazyLoadDBfetch") (0)%Z eval1 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lazyLoadDBflush" (dummy_function "do_lazyLoadDBflush") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "getVarsFromFrame" (dummy_function "do_getVarsFromFrame") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "lazyLoadDBinsertValue" (dummy_function "do_lazyLoadDBinsertValue") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bincode" (dummy_function "do_bincode") (0)%Z eval11 (4)%Z PP_FUNCALL PREC_FN false ;
              rdecl "tabulate" (dummy_function "do_tabulate") (0)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "findInterval" (dummy_function "do_findinterval") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "pretty" (dummy_function "do_pretty") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "formatC" (dummy_function "do_formatC") (0)%Z eval11 (7)%Z PP_FUNCALL PREC_FN false ;
              rdecl "crc64" (dummy_function "do_crc64") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseAnd" (dummy_function "do_bitwise") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseNot" (dummy_function "do_bitwise") (2)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseOr" (dummy_function "do_bitwise") (3)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseXor" (dummy_function "do_bitwise") (4)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseShiftL" (dummy_function "do_bitwise") (5)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bitwiseShiftR" (dummy_function "do_bitwise") (6)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "serialize" (dummy_function "do_serialize") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "serializeb" (dummy_function "do_serialize") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "unserialize" (dummy_function "do_serialize") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rowsum_matrix" (dummy_function "do_rowsum") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "rowsum_df" (dummy_function "do_rowsum") (1)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "setS4Object" (dummy_function "do_setS4Object") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "traceOnOff" (dummy_function "do_traceOnOff") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "debugOnOff" (dummy_function "do_traceOnOff") (1)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;

              rdecl "La_qr_cmplx" (dummy_function "do_lapack") (0)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rs" (dummy_function "do_lapack") (1)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rs_cmplx" (dummy_function "do_lapack") (2)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rg" (dummy_function "do_lapack") (3)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rg_cmplx" (dummy_function "do_lapack") (41)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rs" (dummy_function "do_lapack") (5)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_rs_cmplx" (dummy_function "do_lapack") (51)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_dlange" (dummy_function "do_lapack") (6)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_dgecon" (dummy_function "do_lapack") (7)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_dtrcon" (dummy_function "do_lapack") (8)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_zgecon" (dummy_function "do_lapack") (9)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_ztrcon" (dummy_function "do_lapack") (10)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_solve_cmplx" (dummy_function "do_lapack") (11)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_solve" (dummy_function "do_lapack") (100)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_qr" (dummy_function "do_lapack") (101)%Z eval11 (1)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_chol" (dummy_function "do_lapack") (200)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_chol2inv" (dummy_function "do_lapack") (201)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;

              rdecl "qr_coef_real" (dummy_function "do_lapack") (300)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qr_qy_real" (dummy_function "do_lapack") (301)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "det_ge_real" (dummy_function "do_lapack") (302)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qr_coef_cmplx" (dummy_function "do_lapack") (303)%Z eval11 (2)%Z PP_FUNCALL PREC_FN false ;
              rdecl "qr_qy_cmplx" (dummy_function "do_lapack") (304)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;

              rdecl "La_svd" (dummy_function "do_lapack") (400)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_svd_cmplx" (dummy_function "do_lapack") (401)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_version" (dummy_function "do_lapack") (1000)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "La_library" (dummy_function "do_lapack") (1001)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;

              rdecl "bcprofcounts" (dummy_function "do_bcprofcounts") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bcprofstart" (dummy_function "do_bcprofstart") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "bcprofstop" (dummy_function "do_bcprofstop") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;

              rdecl "eSoftVersion" (dummy_function "do_eSoftVersion") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "curlVersion" (dummy_function "do_curlVersion") (0)%Z eval11 (0)%Z PP_FUNCALL PREC_FN false ;
              rdecl "curlGetHeaders" (dummy_function "do_curlGetHeaders") (0)%Z eval11 (3)%Z PP_FUNCALL PREC_FN false ;
              rdecl "curlDownload" (dummy_function "do_curlDownload") (0)%Z eval11 (5)%Z PP_FUNCALL PREC_FN false

            ]%string)
        end
    |}
  end.

