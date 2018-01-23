(** Rcore.
  Describes how R evaluates expressions.
  The content of this file is the Coq equivalent of functions from R source code.
  Note that only relevant definitions are translated here. Some are just
  reinterpreted in Coq without following the original algorithm of the
  C source. See report for more details. **)

Set Implicit Arguments.
Require Import Ascii Double.
Require Export Loops.


Section Parameterised.

(** * Global Variables **)

Variable globals : Globals.

Let read_globals := read_globals globals.

Local Coercion read_globals : GlobalVariable >-> SExpRec_pointer.

Variable runs : runs_type.

Definition get_R_FunTab S :=
  match runs_R_FunTab runs with
  | None => result_bottom S
  | Some t =>
    result_success S t
  end.

Definition read_R_FunTab S n :=
  let%success t := get_R_FunTab S using S in
  ifb n >= ArrayList.length t then
    result_impossible S "[read_R_FunTab] Out of bounds."
  else
    let c := ArrayList.read t n in
    result_success S c.


Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

(* We may want to make [INT_MIN] and [INT_MAX] a parameter of the formalisation,
  as it depends on the C compiler options. *)
Definition INT_MIN : int := - 2 ^ 31.
Definition INT_MAX : int := 2 ^ 31 - 1.

Definition R_INT_MAX := INT_MAX.
Definition R_INT_MIN := INT_MIN.

Definition R_NaInt := INT_MIN.
Definition R_PosInf := Double.posInf.
Definition R_NegInf := Double.negInf.
Definition R_NaN := Double.NaN.
Definition NA_INTEGER := R_NaInt.
Definition NA_LOGICAL := R_NaInt.
Definition R_NaReal := Double.NaN1954.
Definition NA_REAL := R_NaReal.

Definition R_NaString := NA_STRING.

Definition PLUSOP := 1.
Definition MINUSOP := 2.
Definition TIMESOP := 3.
Definition DIVOP := 4.
Definition POWOP := 5.
Definition MODOP := 6.
Definition IDIVOP := 7.

Definition EQOP := 1.
Definition NEOP := 2.
Definition LTOP := 3.
Definition LEOP := 4.
Definition GEOP := 5.
Definition GTOP := 6.

Definition CTXT_TOPLEVEL := 0.
Definition CTXT_NEXT := 1.
Definition CTXT_BREAK := 2.
Definition CTXT_LOOP := 3.
Definition CTXT_FUNCTION := 4.
Definition CTXT_CCODE := 8.
Definition CTXT_RETURN := 12.
Definition CTXT_BROWSER := 16.
Definition CTXT_GENERIC := 20.
Definition CTXT_RESTART := 32.
Definition CTXT_BUILTIN := 64.


(** * Interpreter functions **)

(** We recall from RinternalsAux.v that we write [p_] for the object
  referenced by the pointer [p], and [p_f] for the field [f] or it **)

(** ** Rmath.h **)

(** The function names of this section corresponds to the macro names
  in the file include/Rmath.h. **)

Definition ISNAN x :=
  Double.isNaN x.


(** ** Rinternals.h **)

(** The function names of this section corresponds to the macro names
  in the file include/Rinternals.h. **)

Definition TYPEOF S x :=
  read%defined x_ := x using S in
  result_success S (type x_).

Definition PRINTNAME S x :=
  read%sym _, x_sym := x using S in
  result_success S (sym_pname x_sym).

Definition CHAR S x :=
  read%VectorChar x_vector := x using S in
  result_success S (list_to_string (ArrayList.to_list x_vector)).

Definition SET_MISSING S e (m : nat) I :=
  map%gp e with @write_nbits 16 4 0 (nat_to_nbits m I) ltac:(nbits_ok) using S in
  result_skip S.
Arguments SET_MISSING : clear implicits.

Definition INCREMENT_NAMED S x :=
  read%defined x_ := x using S in
  match named x_ with
  | named_temporary =>
    map%pointer x with set_named_unique using S in
    result_skip S
  | named_unique =>
    map%pointer x with set_named_plural using S in
    result_skip S
  | named_plural =>
    result_skip S
  end.

Definition NO_REFERENCES S x :=
  read%defined x_ := x using S in
  result_success S (decide (named x_ = named_temporary)).

Definition DDVAL S x :=
  read%defined x_ := x using S in
  result_success S (nth_bit 0 (gp x_) ltac:(nbits_ok)).

Definition SET_DDVAL_BIT S x :=
  map%gp x with @write_nbit 16 0 ltac:(nbits_ok) true using S in
  result_skip S.

Definition UNSET_DDVAL_BIT S x :=
  map%gp x with @write_nbit 16 0 ltac:(nbits_ok) false using S in
  result_skip S.

Definition IS_SCALAR S x t :=
  read%defined x_ := x using S in
  result_success S (decide (type x_ = t /\ scalar x_)).

Definition isLogical S s :=
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = LglSxp)).

Definition IS_LOGICAL := isLogical.

Definition isSymbol S s :=
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = SymSxp)).

Definition isString S s :=
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = StrSxp)).

Definition isNull S s :=
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = NilSxp)).


(** ** duplicate.c **)

(** The function names of this section corresponds to the function names
  in the file main/duplicate.c. **)

(** This is a temporary simplification of the real [duplicate1] function. **)
Definition duplicate1 S s (deep : bool) :=
  read%defined s_ := s using S in
  let (S, s) := alloc_SExp S s_ in
  result_success S s.

Definition duplicate S s :=
  duplicate1 S s true.

(** The following function is actually in the C file include/Rinlinedfuns.h. **)
Definition isPairList S s :=
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | NilSxp
  | ListSxp
  | LangSxp
  | DotSxp =>
    result_success S true
  | _ =>
    result_success S false
  end.

(** The following function is actually in the C file include/Rinlinedfuns.h. **)
Definition isVectorList S s :=
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | VecSxp
  | ExprSxp =>
    result_success S true
  | _ =>
    result_success S false
  end.

Definition isVector S s :=
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | RawSxp
  | VecSxp
  | ExprSxp =>
    result_success S true
  | _ =>
    result_success S false
  end.

Definition R_cycle_detected S s child :=
  let%success child_type := TYPEOF S child using S in
  ifb s = child then
    match child_type with
    | NilSxp
    | SymSxp
    | EnvSxp
    | SpecialSxp
    | BuiltinSxp
    | ExtptrSxp
    | BcodeSxp
    | WeakrefSxp =>
      result_success S false
    | _ =>
      result_success S true
    end
  else
    run%exit
      read%defined child_ := child using S in
      ifb attrib child_ <> R_NilValue then
        if%success runs_R_cycle_detected runs S s (attrib child_) using S then
          result_rreturn S true
        else result_rskip S
      else result_rskip S using S in
    if%success isPairList S child using S then
      fold%return
      along child
      as el, el_, el_list do
        let%success r :=
          runs_R_cycle_detected runs S s (list_carval el_list) using S in
        ifb s = el \/ r then
          result_rreturn S true
        else
          let%success r :=
            runs_R_cycle_detected runs S s (attrib el_) using S in
          ifb attrib el_ <> R_NilValue /\ r then
            result_rreturn S true
          else result_rskip S
      using S, runs, globals in
      result_success S false
    else
      if%success isVectorList S child using S then
        read%VectorPointer child_ := child using S in
        do%let r := false
        for e in VecSxp_data child_ do
          if r then result_success S r
          else runs_R_cycle_detected runs S s e using S
      else result_success S false.


(** ** memory.c **)

(** The function names of this section corresponds to the function names
  in the file main/memory.c. **)

Definition CONS S (car cdr : SExpRec_pointer) : state * SExpRec_pointer :=
  let e_ := make_SExpRec_list R_NilValue car cdr R_NilValue in
  alloc_SExp S e_.

Definition CONS_NR := CONS.

Definition allocList S (n : nat) : state * SExpRec_pointer :=
  let fix aux S n p :=
    match n with
    | 0 => (S, p)
    | S n =>
      let (S, p) := aux S n p in
      CONS S R_NilValue p
    end
  in aux S n R_NilValue.

Definition STRING_ELT S (x : SExpRec_pointer) i : result SExpRec_pointer :=
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> StrSxp then
    result_error S "[STRING_ELT] Not a character vector."
  else
    read%Pointer r := x at i using S in
    result_success S r.

(** Note: there is a macro definition renaming [NewEnvironment] to
  [Rf_NewEnvironment] in the file include/Defn.h. As a consequence,
  the compiled C files references [Rf_NewEnvironment] and not
  [NewEnvironment]. These two functions are exactly the same.
  This is a relatively frequent scheme in R source code. **)
Definition NewEnvironment S (namelist valuelist rho : SExpRec_pointer) : result SExpRec_pointer :=
  let (S, newrho) := alloc_SExp S (make_SExpRec_env R_NilValue valuelist rho) in
  do%success (v, n) := (valuelist, namelist)
  while result_success S (decide (v <> R_NilValue /\ n <> R_NilValue)) do
    read%list _, n_cdr, n_tag := n using S in
    set%tag v := n_tag using S in
    read%list _, v_cdr, _ := v using S in
    result_success S (v_cdr, n_cdr) using S, runs in
  result_success S newrho.

(** Similarly, there is a macro renaming [mkPROMISE] to [Rf_mkPROMISE]. **)
Definition mkPromise S (expr rho : SExpRec_pointer) : result SExpRec_pointer :=
  map%pointer expr with set_named_plural using S in
  let (S, s) := alloc_SExp S (make_SExpRec_prom R_NilValue R_UnboundValue expr rho) in
  result_success S s.


(** ** Rinlinedfuns.c **)

(** The function names of this section corresponds to the function names
  in the file include/Rinlinedfuns.c. **)

(** The way the original functions [allocVector], [allocVector3], etc.
  from R source code are defined are not compatible with the way the
  memory of the C language has been formalised here. The functions
  below are thus slightly different from their C counterparts.
  The [repeat] function of Coq can be used to initialise their data. **)

Definition alloc_vector_char S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_char R_NilValue v_data).

Definition alloc_vector_lgl S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_lgl R_NilValue v_data).

Definition alloc_vector_int S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_int R_NilValue v_data).

Definition alloc_vector_real S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_real R_NilValue v_data).

Definition alloc_vector_cplx S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_cplx R_NilValue v_data).

(** The following allocators uses pointers. Note that the original
  [allocVector] function initialises them to [R_NilValue] (and not
  [NULL], for instance) by default. **)

Definition alloc_vector_str S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_str R_NilValue v_data).

Definition alloc_vector_vec S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_vec R_NilValue v_data).

Definition alloc_vector_expr S v_data : state * SExpRec_pointer :=
  alloc_SExp S (make_SExpRec_expr R_NilValue v_data).

(** We however propose the following smart constructor, based on
  [allocVector]/[allocVector3] from main/memory.c. **)
(** Note: using [arbitrary] would here be more natural than these default values
  for the base cases, but it would not behave well in the extraction. **)
Definition allocVector S type length :=
  let alloc {T} (allocator : state -> ArrayList.array T -> state * SExpRec_pointer) (base : T) :=
    let (S, v) := allocator S (ArrayList.from_list (repeat base length)) in
    result_success S v in
  match type with
  | NilSxp =>
    result_success S (R_NilValue : SExpRec_pointer)
  | RawSxp =>
    result_not_implemented "[allocVector] Raw type."
  | CharSxp =>
    alloc alloc_vector_char Ascii.zero
  | LglSxp =>
    alloc alloc_vector_lgl (NA_LOGICAL)
  | IntSxp =>
    alloc alloc_vector_int (NA_INTEGER)
  | RealSxp =>
    alloc alloc_vector_real (NA_REAL)
  | CplxSxp =>
    alloc alloc_vector_cplx (make_Rcomplex NA_REAL NA_REAL)
  | StrSxp =>
    alloc alloc_vector_str (R_NilValue : SExpRec_pointer)
  | ExprSxp =>
    alloc alloc_vector_expr (R_NilValue : SExpRec_pointer)
  | VecSxp =>
    alloc alloc_vector_vec (R_NilValue : SExpRec_pointer)
  | LangSxp =>
    ifb length = 0 then result_success S (R_NilValue : SExpRec_pointer)
    else
      let (S, s) := allocList S length in
      map%pointer s with set_type LangSxp using S in
      result_success S s
  | ListSxp =>
    let (S, s) := allocList S length in
    result_success S s
  | _ => result_error S "[allocVector] Invalid type in vector allocation."
  end.

Definition ScalarLogical x : SExpRec_pointer :=
  ifb x = NA_LOGICAL then
    R_LogicalNAValue
  else ifb x <> 0 then
    R_TrueValue
  else R_FalseValue.

Definition ScalarInteger S x : state * SExpRec_pointer :=
  alloc_vector_int S (ArrayList.from_list [x]).

Definition ScalarReal S x : state * SExpRec_pointer :=
  alloc_vector_real S (ArrayList.from_list [x]).

Definition ScalarComplex S x : state * SExpRec_pointer :=
  alloc_vector_cplx S (ArrayList.from_list [x]).

Definition ScalarString S (x : SExpRec_pointer) : result SExpRec_pointer :=
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> CharSxp then
    result_error S "[ScalarString] The given argument is not of type ‘CharSxp’."
  else
    let (S, s) := alloc_vector_str S (ArrayList.from_list [x]) in
    result_success S s.


(** Named [length] in the C source file. **)
Definition R_length S s :=
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | NilSxp => result_success S 0
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | CharSxp
  | VecSxp
  | ExprSxp
  | RawSxp =>
    read%defined s_ := s using S in
    let%defined l := get_VecSxp_length s_ using S in
    result_success S l
  | ListSxp
  | LangSxp
  | DotSxp =>
    do%success (s, i) := (s, 0)
    while result_success S (decide (s <> NULL /\ s <> R_NilValue))
    do
      read%list _, s_cdr, _ := s using S in
      result_success S (s_cdr, 1 + i) using S, runs in
    result_success S i
  | EnvSxp =>
    result_not_implemented "[R_length] Rf_envlength"
  | _ =>
    result_success S 1
  end.

Definition inherits S s name :=
  read%defined s_ := s using S in
  if obj s_ then
    let%success klass := runs_getAttrib runs S s R_ClassSymbol using S in
    read%VectorPointer klass_vector := klass using S in
    do%success b := false
    for str in VecSxp_data klass_vector do
      if b then result_success S true
      else
        let%success str_ := CHAR S str using S in
        result_success S (decide (str_ = name)) using S in
    result_success S b
  else result_success S false.

Definition isVectorAtomic S s :=
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | RawSxp => result_success S true
  | _ => result_success S false
  end.

Definition isInteger S s :=
  let%success s_type := TYPEOF S s using S in
  let%success inh := inherits S s "factor" using S in
  result_success S (decide (s_type = IntSxp /\ ~ inh)).

Definition isList S s :=
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s = R_NilValue \/ s_type = ListSxp)).

Definition isLanguage S s :=
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s = R_NilValue \/ s_type = LangSxp)).

Definition isNumeric S s :=
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | IntSxp =>
    let%success inh := inherits S s "factor" using S in
    result_success S (negb inh)
  | LglSxp
  | RealSxp =>
    result_success S true
  | _ => result_success S false
  end.

Definition isNumber S s :=
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | IntSxp =>
    let%success inh := inherits S s "factor" using S in
    result_success S (negb inh)
  | LglSxp
  | RealSxp
  | CplxSxp =>
    result_success S true
  | _ => result_success S false
  end.

Definition SCALAR_LVAL S x :=
  read%Logical r := x at 0 using S in
  result_success S r.

Definition SCALAR_IVAL S x :=
  read%Integer r := x at 0 using S in
  result_success S r.

Definition SCALAR_DVAL S x :=
  read%Real r := x at 0 using S in
  result_success S r.

Definition SET_SCALAR_LVAL S x v :=
  write%Logical x at 0 := v using S in
  result_skip S.

Definition SET_SCALAR_IVAL S x v :=
  write%Integer x at 0 := v using S in
  result_skip S.

Definition SET_SCALAR_DVAL S x v :=
  write%Real x at 0 := v using S in
  result_skip S.


Definition lcons S car cdr :=
  let (S, e) := CONS S car cdr in
  map%pointer e with set_type LangSxp using S in
  result_success S e.

Definition list1 S s :=
  CONS S s R_NilValue.

Definition list2 S s t :=
  let (S, l) := list1 S t in
  CONS S s l.

Definition list3 S s t u :=
  let (S, l) := list2 S t u in
  CONS S s l.

Definition list4 S s t u v :=
  let (S, l) := list3 S t u v in
  CONS S s l.

Definition list5 S s t u v w :=
  let (S, l) := list4 S t u v w in
  CONS S s l.

Definition list6 S s t u v w x :=
  let (S, l) := list5 S t u v w x in
  CONS S s l.

Definition lang1 S s :=
  lcons S s R_NilValue.

Definition lang2 S s t :=
  let (S, l) := list1 S t in
  lcons S s l.

Definition lang3 S s t u :=
  let (S, l) := list2 S t u in
  lcons S s l.

Definition lang4 S s t u v :=
  let (S, l) := list3 S t u v in
  lcons S s l.

Definition lang5 S s t u v w :=
  let (S, l) := list4 S t u v w in
  lcons S s l.

Definition lang6 S s t u v w x :=
  let (S, l) := list5 S t u v w x in
  lcons S s l.


Definition R_FixupRHS S x y :=
  read%defined y_ := y using S in
  ifb y <> R_NilValue /\ named y_ <> named_temporary then
    if%success R_cycle_detected S x y using S then
      duplicate S y
    else
      map%pointer y with set_named_plural using S in
      result_success S y
  else result_success S y.

Definition ALTREP_LENGTH (S : state) (x : SExpRec_pointer) : result nat :=
  result_not_implemented "[ALTREP_LENGTH]".

Definition STDVEC_LENGTH S x :=
  read%defined x_ := x using S in
  match x_ with
  | SExpRec_NonVector _ => result_impossible S "[STDVEC_LENGTH] Not a vector."
  | SExpRec_VectorChar x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorLogical x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorInteger x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorComplex x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorReal x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorPointer x_ => result_success S (VecSxp_length x_)
  end.

Definition XLENGTH_EX S x :=
  read%defined x_ := x using S in
  if alt x_ then ALTREP_LENGTH S x
  else STDVEC_LENGTH S x.

Definition XLENGTH := XLENGTH_EX.

Definition LENGTH_EX S (x : SExpRec_pointer) :=
  ifb x = R_NilValue then
    result_success S 0
  else XLENGTH S x.

Definition LENGTH := LENGTH_EX.


Definition ALTLOGICAL_ELT S x i :=
  read%Logical x_i := x at i using S in
  result_success S x_i.

Definition LOGICAL_ELT S x i :=
  read%defined x_ := x using S in
  ifb alt x_ then ALTLOGICAL_ELT S x i
  else
    read%Logical x_i := x at i using S in
    result_success S x_i.

Definition ALTINTEGER_ELT (S : state) (x : SExpRec_pointer) (i : nat) : result int :=
  result_not_implemented "[ALTINTEGER_ELT]".

Definition INTEGER_ELT S x i :=
  read%defined x_ := x using S in
  ifb alt x_ then ALTINTEGER_ELT S x i
  else
    read%Integer x_i := x at i using S in
    result_success S x_i.

Definition ALTREAL_ELT (S : state) (x : SExpRec_pointer) (i : nat) : result double :=
  result_not_implemented "[ALTREAL_ELT]".

Definition REAL_ELT S x i :=
  read%defined x_ := x using S in
  ifb alt x_ then ALTREAL_ELT S x i
  else
    read%Real x_i := x at i using S in
    result_success S x_i.

Definition ALTCOMPLEX_ELT (S : state) (x : SExpRec_pointer) (i : nat) : result Rcomplex :=
  result_not_implemented "[ALTCOMPLEX_ELT]".

Definition COMPLEX_ELT S x i :=
  read%defined x_ := x using S in
  ifb alt x_ then ALTCOMPLEX_ELT S x i
  else
    read%Complex x_i := x at i using S in
    result_success S x_i.

Definition ALTRAW_ELT S x i :=
  read%Pointer x_i := x at i using S in
  result_success S x_i.

Definition RAW_ELT S x i :=
  read%defined x_ := x using S in
  ifb alt x_ then ALTRAW_ELT S x i
  else
    read%Pointer x_i := x at i using S in
    result_success S x_i.


(** ** arithmetic.c **)

(** The function names of this section corresponds to the function names
  in the file main/arithmetic.c. **)

Definition R_IsNA x :=
  decide (Double.getNaNData x = Some 1954)%positive.

Definition R_IsNAN x :=
  match Double.getNaNData x with
  | Some i => decide (i <> 1954)%positive
  | None => false
  end.

Definition ScalarValue1 S x :=
  if%success NO_REFERENCES S x using S then
    result_success S x
  else
    let%success x_type := TYPEOF S x using S in
    allocVector S x_type 1.

Definition ScalarValue2 S x y :=
  if%success NO_REFERENCES S x using S then
    result_success S x
  else
    if%success NO_REFERENCES S y using S then
      result_success S y
    else
      let%success x_type := TYPEOF S x using S in
      allocVector S x_type 1.


(** ** envir.c **)

(** The function names of this section corresponds to the function names
  in the file main/envir.c. The most important functions of envir.c
  are shown in a later section. **)

(** The function [mkChar] from the R source code performs a lot of things.
  It deals with encoding, for embedded zero-characters, as well as avoid
  allocated twice the same string, by looking through the already
  allocated strings. We do none of the above. **)
(* FIXME: What is the difference between [intCHARSXP] and [CHARSXP]? *)
Definition mkChar S (str : string) : state * SExpRec_pointer :=
  (* Note that values are not cached, in contrary to the original code. *)
  alloc_vector_char S (ArrayList.from_list (string_to_list str)).

Definition mkString S (str : string) : state * SExpRec_pointer :=
  let (S, c) := mkChar S str in
  alloc_vector_str S (ArrayList.from_list [c]).


(** ** dstruct.c **)

(** The function names of this section corresponds to the function names
  in the file main/dstruct.c. **)

Definition iSDDName S (name : SExpRec_pointer) :=
  let%success buf := CHAR S name using S in
  ifb substring 0 2 buf = ".."%string /\ String.length buf > 2 then
    let buf := substring 2 (String.length buf) buf in
    (** I am simplifying the C code here. **)
    result_success S (decide (Forall (fun c : Ascii.ascii =>
        Mem c (["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"])%char)
      (string_to_list buf)))
  else
  result_success S false.

Definition mkSYMSXP S (name value : SExpRec_pointer) :=
  let%success i := iSDDName S name using S in
  let (S, c) := alloc_SExp S (make_SExpRec_sym R_NilValue name value R_NilValue) in
  map%gp c with @write_nbit 16 0 ltac:(nbits_ok) i using S in
  result_success S c.


(** ** names.c **)

(** The function names of this section corresponds to the function names
  in the file main/names.c. **)

Definition mkSymMarker S pname :=
  let (S, ans) := alloc_SExp S (make_SExpRec_sym R_NilValue pname NULL R_NilValue) in
  write%defined ans := make_SExpRec_sym R_NilValue pname ans R_NilValue using S in
  result_success S ans.

Definition install S name_ : result SExpRec_pointer :=
  (** As said in the description of [InitNames] in Rinit.v,
    the hash table present in [R_SymbolTable] has not been
    formalised as such.
    Instead, it is represented as a single list, and not
    as [HSIZE] different lists.
    This approach is slower, but equivalent. **)
  fold%return
  along R_SymbolTable S
  as sym_car, _ do
    let%success str_sym := PRINTNAME S sym_car using S in
    let%success str_name_ := CHAR S str_sym using S in
    ifb name_ = str_name_ then
      result_rreturn S sym_car
    else result_rskip S using S, runs, globals in
  ifb name_ = ""%string then
    result_error S "[install] Attempt to use zero-length variable name."
  else
    let (S, str) := mkChar S name_ in
    let%success sym := mkSYMSXP S str R_UnboundValue using S in
    let (S, SymbolTable) := CONS S sym (R_SymbolTable S) in
    let S := update_R_SymbolTable S SymbolTable in
    result_success S sym.

(** We here choose to model [installChar] as its specification
  given by the associated comment in the C source file. **)
Definition installChar S charSXP :=
  let%success str := CHAR S charSXP using S in
  install S str.


(** ** sysutils.c **)

(** The function names of this section corresponds to the function names
  in the file main/sysutils.c. **)

Definition installTrChar S x :=
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> CharSxp then
    result_error S "[installTrChar] Must be called on a [CharSxp]."
  else
    (** The original C program deals with encoding here. **)
    installChar S x.


(** ** gram.y **)

(** The function names of this section corresponds to the function names
  in the file main/gram.y. **)

Definition mkTrue S :=
  alloc_vector_lgl S (ArrayList.from_list [1 : int]).

Definition mkFalse S :=
  alloc_vector_lgl S (ArrayList.from_list [0 : int]).

Definition mkNA S :=
  alloc_vector_lgl S (ArrayList.from_list [NA_LOGICAL : int]).


Definition NewList S :=
  let (S, s) := CONS S R_NilValue R_NilValue in
  set%car s := s using S in
  result_success S s.

Definition GrowList S l s :=
  let (S, tmp) := CONS S s R_NilValue in
  read%list l_car, _, _ := l using S in
  set%cdr l_car := tmp using S in
  set%car l := tmp using S in
  result_success S l.

Definition TagArg S arg tag :=
  let%success tag_type := TYPEOF S tag using S in
  run%success
    match tag_type with
    | StrSxp =>
      let%success tag_ := STRING_ELT S tag 0 using S in
      run%success installTrChar S tag_ using S in
      result_skip S
    | NilSxp
    | SymSxp =>
      result_skip S
    | _ =>
      result_error S "[TagArg] Incorrect tag type."
    end using S in
  lang2 S arg tag.

Definition FirstArg S s tag :=
  let%success tmp := NewList S using S in
  let%success tmp := GrowList S tmp s using S in
  read%list tmp_car, _, _ := tmp using S in
  set%tag tmp_car := tag using S in
  result_success S tmp.

Definition NextArg S l s tag :=
  let%success l := GrowList S l s using S in
  read%list l_car, _, _ := l using S in
  set%tag l_car := tag using S in
  result_success S l.

Definition CheckFormalArgs S formlist new :=
  fold%success
  along formlist
  as _, formlist_tag do
    ifb formlist_tag = new then
      result_error S "[CheckFormalArgs] Repeated formal argument."
    else result_skip S using S, runs, globals in
  result_skip S.


(** ** context.c **)

(** The function names of this section corresponds to the function names
  in the file main/context.c. **)

(** Instead of updating a context given as its first argument, it returns it. **)
Definition begincontext S flags syscall env sysp promargs callfun :=
  let cptr := {|
     nextcontext := Some (R_GlobalContext S) ;
     cjmpbuf := 1 + cjmpbuf (R_GlobalContext S) ;
     callflag := flags ;
     promargs := promargs ;
     callfun := callfun ;
     sysparent := sysp ;
     call := syscall ;
     cloenv := env ;
     conexit := R_NilValue ;
     returnValue := NULL ;
     jumptarget := None ;
     jumpmask := empty_context_type
   |} in
  let S := state_with_context S cptr in
  result_success S cptr.

Fixpoint first_jump_target_loop S c cptr mask :=
  ifb c = cptr then
    result_success S cptr
  else
    ifb cloenv c <> R_NilValue /\ conexit c <> R_NilValue then
      let c := context_with_jumptarget c (Some cptr) in
      let c := context_with_jumpmask c mask in
      result_success S c
    else
      match nextcontext c with
      | None => result_success S cptr
      | Some c => first_jump_target_loop S c cptr mask
      end.

Definition first_jump_target S cptr mask :=
  first_jump_target_loop S (R_GlobalContext S) cptr mask.

Fixpoint R_run_onexits_loop S c cptr :=
  ifb c = cptr then
    result_skip S
  else
    run%success
      ifb cloenv c <> R_NilValue /\ conexit c <> R_NilValue then
        let s := conexit c in
        let savecontext := R_ExitContext S in
        let c := context_with_conexit c R_NilValue in
        let c := context_with_returnValue c NULL in
        let S := update_R_ExitContext S (Some c) in
        fold%success
        along s
        as _, _, s_list do
          let c := context_with_conexit c (list_cdrval s_list) in
          let S := state_with_context S c in
          run%success
            runs_eval runs S (list_carval s_list) (cloenv cptr) using S in
            result_skip S using S, runs, globals in
        let S := update_R_ExitContext S savecontext in
        result_skip S
      else result_skip S using S in
    run%success
      ifb R_ExitContext S = Some c then
        let S := update_R_ExitContext S None in
        result_skip S
      else result_skip S using S in
    match nextcontext c with
    | None => result_impossible S "[R_run_onexits_loop] Bad target context."
    | Some c => R_run_onexits_loop S c cptr
    end.

Definition R_run_onexits S cptr :=
  R_run_onexits_loop S (R_GlobalContext S) cptr.

Definition R_restore_globals S (cptr : context) :=
  result_skip S.

Definition R_jumpctxt A S targetcptr mask val : result A :=
  let%success cptr := first_jump_target S targetcptr mask using S in
  run%success R_run_onexits S cptr using S in
  let S := update_R_ReturnedValue S val in
  let S := state_with_context S cptr in
  run%success R_restore_globals S (R_GlobalContext S) using S in
  result_longjump S (cjmpbuf cptr) mask.
Arguments R_jumpctxt [A].

Definition endcontext S cptr :=
  let jmptarget := jumptarget cptr in
  run%success
    ifb cloenv cptr <> R_NilValue /\ conexit cptr <> R_NilValue then
      let s := conexit cptr in
      let savecontext := R_ExitContext S in
      let cptr := context_with_conexit cptr R_NilValue in
      let cptr := context_with_jumptarget cptr None in
      let S := update_R_ExitContext S (Some cptr) in
      fold%success
      along s
      as _, _, s_list do
        let cptr := context_with_conexit cptr (list_cdrval s_list) in
        let S := state_with_context S cptr in
        run%success
          runs_eval runs S (list_carval s_list) (cloenv cptr) using S in
        result_skip S using S, runs, globals in
      let S := update_R_ExitContext S savecontext in
      result_skip S
    else result_skip S using S in
  run%success
    ifb R_ExitContext S = Some cptr then
      let S := update_R_ExitContext S None in
      result_skip S
    else result_skip S using S in
  run%success
    match jmptarget with
    | None => result_skip S
    | Some jmptarget =>
      R_jumpctxt S jmptarget (jumpmask cptr) (R_ReturnedValue S)
    end using S in
  let%defined c := nextcontext cptr using S in
  let S := state_with_context S c in
  result_skip S.

Fixpoint findcontext_loop A S cptr env mask mask_against val err : result A :=
  ifb context_type_mask (callflag cptr) mask_against /\ cloenv cptr = env then
    R_jumpctxt S cptr mask val
  else
    let error S := result_error S ("[findcontext_loop] " ++ err) in
    match nextcontext cptr with
    | None => error S
    | Some cptr =>
      ifb callflag cptr = Ctxt_TopLevel then error S
      else findcontext_loop _ S cptr env mask mask_against val err
    end.
Arguments findcontext_loop [A].

Definition findcontext A S mask env val : result A :=
  ifb context_type_mask Ctxt_Loop mask then
    findcontext_loop S (R_GlobalContext S) env mask Ctxt_Loop val "No loop for break/next, jumping to top level."
  else
    findcontext_loop S (R_GlobalContext S) env mask mask val "No function to return from, jumping to top level.".
Arguments findcontext [A].


(** ** match.c **)

(** The function names of this section corresponds to the function names
  in the file main/match.c. **)

Definition psmatch f t exact :=
  if exact : bool then
    decide (f = t)
  else
    String.prefix t f.

Definition pmatch S (formal tag : SExpRec_pointer) exact : result bool :=
  let get_name str :=
    let%success str_type := TYPEOF S str using S in
    match str_type with
    | SymSxp =>
      let%success str_name := PRINTNAME S str using S in
      CHAR S str_name
    | CharSxp =>
      CHAR S str
    | StrSxp =>
      let%success str_ := STRING_ELT S str 0 using S in
      result_not_implemented "[pmatch] translateChar(str_)" (* TODO *)
    | _ =>
      result_error S "[pmatch] Invalid partial string match."
    end in
  let%success f := get_name formal using S in
  let%success t := get_name tag using S in
  result_success S (psmatch f t exact).

(** The function [matchArgs] matches the arguments supplied to a given
  call with the formal, expected arguments.
  This is more complex as it may seem as arguments in R can be named
  (and thus provided in any order), or can be ‘...’.
  The algorithm presented in this function is thus crucial to understand
  the semantics of function calls in R.
  It is furthermore rather complicated.
  This is a large function and is divided into all its three passes for
  readability purposes. **)

(** The function makes use of some bits from the general purpose pool
  to mark some arguments as being used or missing. **)

Definition argused e_ :=
  nbits_to_nat (gp e_).

Definition set_argused (used : nat) I :=
  set_gp (nat_to_nbits used I).
Arguments set_argused : clear implicits.

Definition missing e_ :=
  sub_nbits 0 4 (gp e_) ltac:(nbits_ok).

Definition matchArgs_first S formals actuals supplied : result (list nat) :=
  fold%success (a, fargusedrev) := (actuals, nil)
  along formals
  as _, f_tag do
    let%success f_tag_sym_name := PRINTNAME S f_tag using S in
    let%success ftag_name := CHAR S f_tag_sym_name using S in
    let%success fargusedi :=
      ifb f_tag <> R_DotsSymbol /\ f_tag <> R_NilValue then
        fold%let fargusedi := 0
        along supplied
        as b, b_, b_list do
          let b_tag := list_tagval b_list in
          ifb b_tag <> R_NilValue then
            let%success b_tag_sym_name := PRINTNAME S b_tag using S in
            let%success btag_name := CHAR S b_tag_sym_name using S in
            ifb ftag_name = btag_name then
              ifb fargusedi = 2 then
                result_error S "[matchArgs_first] Formal argument matched by multiple actual arguments."
              else ifb argused b_ = 2 then
                result_error S "[matchArgs_first] Actual argument matches several formal arguments."
              else
                set%car a := list_carval b_list using S in
                run%success
                  ifb list_carval b_list <> R_MissingArg then
                    SET_MISSING S a 0 ltac:(nbits_ok)
                  else result_skip S using S in
                map%pointer b with set_argused 2 ltac:(nbits_ok) using S in
                result_success S 2
            else result_success S fargusedi
          else result_success S fargusedi using S, runs, globals
      else result_success S 0 using S in
    read%list _, a_cdr, _ := a using S in
    result_success S (a_cdr, fargusedi :: fargusedrev) using S, runs, globals in
  result_success S (List.rev fargusedrev).

Definition matchArgs_second S actuals formals supplied fargused :=
  fold%success (a, fargused, dots, seendots) :=
    (actuals, fargused, R_NilValue : SExpRec_pointer, false)
  along formals
  as _, f_tag do
    match fargused with
    | nil => result_impossible S "[matchArgs_second] The list/array “fargused” has an unexpected size."
    | fargusedi :: fargused =>
      let%success (dots, seendots) :=
        ifb fargusedi = 0 then
          ifb f_tag = R_DotsSymbol /\ ~ seendots then
            result_success S (a, true)
          else
            fold%success fargusedi := fargusedi
            along supplied
            as b, b_, b_list do
              let b_tag := list_tagval b_list in
              ifb argused b_ <> 2 /\ b_tag <> R_NilValue then
                if%success pmatch S f_tag b_tag seendots using S then
                  ifb argused b_ <> 0 then
                    result_error S "[matchArgs_second] Actual argument matches several formal arguments."
                  else ifb fargusedi = 1 then
                    result_error S "[matchArgs_second] Formal argument matched by multiple actual arguments."
                  else
                    set%car a := list_carval b_list using S in
                    run%success
                      ifb list_carval b_list <> R_MissingArg then
                        SET_MISSING S a 0 ltac:(nbits_ok)
                      else result_skip S using S in
                    map%pointer b with set_argused 1 ltac:(nbits_ok) using S in
                    result_success S 1
                else result_success S fargusedi
              else result_success S fargusedi using S, runs, globals in
            result_success S (dots, seendots)
        else result_success S (dots, seendots) using S in
      read%list _, a_cdr, _ := a using S in
      result_success S (a_cdr, fargused, dots, seendots)
    end using S, runs, globals in
  result_success S dots.

Definition matchArgs_third S (formals actuals supplied : SExpRec_pointer) :=
  do%success (f, a, b, seendots) := (formals, actuals, supplied, false)
  while result_success S (decide (f <> R_NilValue /\ b <> R_NilValue /\ ~ seendots)) do
    read%list _, f_cdr, f_tag := f using S in
    read%list a_car, a_cdr, _ := a using S in
    ifb f_tag = R_DotsSymbol then
      result_success S (f_cdr, a_cdr, b, true)
    else ifb a_car <> R_MissingArg then
      result_success S (f_cdr, a_cdr, b, seendots)
    else
      read%list b_, b_car, b_cdr, b_tag := b using S in
      ifb argused b_ <> 0 \/ b_tag <> R_NilValue then
        result_success S (f, a, b_cdr, seendots)
      else
        set%car a := b_car using S in
        run%success
          ifb b_car <> R_MissingArg then
            SET_MISSING S a 0 ltac:(nbits_ok)
          else result_skip S using S in
        map%pointer b with set_argused 1 ltac:(nbits_ok) using S in
        result_success S (f_cdr, a_cdr, b_cdr, seendots) using S, runs in
  result_skip S.

Definition matchArgs_dots S dots supplied :=
  run%success SET_MISSING S dots 0 ltac:(nbits_ok) using S in
  fold%success i := 0
  along supplied
  as a, _ do
    read%defined a_ := a using S in
    ifb argused a_ = 0 then
      result_success S (1 + i)
    else
      result_success S i using S, runs, globals in
  ifb i <> 0 then
    let (S, a) := allocList S i in
    map%pointer a with set_type DotSxp using S in
    fold%success f := a
    along supplied
    as _, b_, b_list do
      ifb argused b_ = 0 then
        set%car f := list_carval b_list using S in
        set%tag f := list_tagval b_list using S in
        read%list _, f_cdr, _ := f using S in
        result_success S f_cdr
      else result_success S f using S, runs, globals in
    set%car dots := a using S in
    result_skip S
  else result_skip S.

Definition matchArgs_check S supplied :=
  fold%success (unused, last) := (R_NilValue : SExpRec_pointer, R_NilValue : SExpRec_pointer)
  along supplied
  as _, b_, b_list do
    ifb argused b_ = 0 then
      ifb last = R_NilValue then
        let (S, unused) := CONS S (list_carval b_list) R_NilValue in
        set%tag unused := list_tagval b_list using S in
        result_success S (unused, unused)
      else
        let (S, l) := CONS S (list_carval b_list) R_NilValue in
        set%cdr last := l using S in
        read%list _, last_cdr, _ := last using S in
        let last := last_cdr in
        set%tag last := list_tagval b_list using S in
        result_success S (unused, last)
    else result_success S (unused, last) using S, runs, globals in
  ifb last <> R_NilValue then
    result_error S "[matchArgs_check] Unused argument(s)."
  else
    result_skip S.


Definition matchArgs S formals supplied (call : SExpRec_pointer) :=
  fold%success (actuals, argi) := (R_NilValue : SExpRec_pointer, 0)
  along formals
  as _, _ do
    let (S, actuals) := CONS_NR S R_MissingArg actuals in
    run%success SET_MISSING S actuals 1 ltac:(nbits_ok) using S in
    result_success S (actuals, 1 + argi) using S, runs, globals in
  fold%success
  along supplied
  as b, _ do
    map%pointer b with set_argused 0 ltac:(nbits_ok) using S in
    result_skip S using S, runs, globals in
  let%success fargused := matchArgs_first S formals actuals supplied using S in
  let%success dots := matchArgs_second S actuals formals supplied fargused using S in
  run%success matchArgs_third S formals actuals supplied using S in
  ifb dots <> R_NilValue then
    run%success matchArgs_dots S dots supplied using S in
    result_success S actuals
  else
    run%success matchArgs_check S supplied using S in
    result_success S actuals.


(** ** envir.c **)

(** The function names of this section corresponds to the function names
  in the file main/envir.c. **)

Definition IS_SPECIAL_SYMBOL S b :=
  read%defined b_ := b using S in
  result_success S (nth_bit 12 (gp b_) ltac:(nbits_ok)).

(** This macro definition was already redundant in C. **)
Definition NO_SPECIAL_SYMBOLS S x :=
  read%defined x_ := x using S in
  result_success S (nth_bit 12 (gp x_) ltac:(nbits_ok)).

Definition SET_SPECIAL_SYMBOL S x v :=
  map%gp x with @write_nbit 16 12 ltac:(nbits_ok) v using S in
  result_skip S.

Definition R_envHasNoSpecialSymbols S (env : SExpRec_pointer) : result bool :=
  read%env env_, env_env := env using S in
  (** A note about hashtabs has been commented out. **)
  fold%let b := true
  along env_frame env_env
  as frame_car, frame_tag do
    if%success IS_SPECIAL_SYMBOL S frame_tag using S then
      result_success S false
    else result_success S b using S, runs, globals.

Definition SET_FRAME S x v :=
  read%env x_, x_env := x using S in
  let x_env := {|
      env_frame := v ;
      env_enclos := env_enclos x_env
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_env
    |} in
  write%defined x := x_ using S in
  result_success S tt.

Definition addMissingVarsToNewEnv S (env addVars : SExpRec_pointer) :=
  ifb addVars = R_NilValue then
    result_skip S
  else
    let%success addVars_type := TYPEOF S addVars using S in
    ifb addVars_type = EnvSxp then
      result_error S "[addMissingVarsToNewEnv] Additional variables should be passed as a list."
    else
      read%list addVars_car, addVars_cdr, _ := addVars using S in
      fold%success aprev := addVars
      along addVars_cdr
      as a, _, _ do
        result_success S a using S, runs, globals in
      read%env _, env_env := env using S in
      set%cdr aprev := env_frame env_env using S in
      run%success SET_FRAME S env addVars using S in
      fold%let
      along addVars_cdr
      as endp, _, endp_list do
        let endTag := list_tagval endp_list in
        do%success (addVars, s, sprev) := (addVars, addVars, R_NilValue : SExpRec_pointer)
        while result_success S (decide (s <> endp)) do
          read%list _, s_cdr, s_tag := s using S in
            ifb s_tag = endTag then
              ifb sprev = R_NilValue then
                let addVars := s_cdr in
                run%success SET_FRAME S env addVars using S in
                result_success S (addVars, s_cdr, sprev)
              else
                set_cdr S s_cdr sprev (fun S =>
                  result_success S (addVars, s_cdr, sprev))
            else result_success S (addVars, s_cdr, s) using S, runs in
        result_skip S using S, runs, globals.

Definition FRAME_IS_LOCKED S rho :=
  read%defined rho_ := rho using S in
  result_success S (nth_bit 14 (gp rho_) ltac:(nbits_ok)).

Definition BINDING_IS_LOCKED S symbol :=
  read%defined symbol_ := symbol using S in
  result_success S (nth_bit 14 (gp symbol_) ltac:(nbits_ok)).

Definition IS_ACTIVE_BINDING S symbol :=
  read%defined symbol_ := symbol using S in
  result_success S (nth_bit 15 (gp symbol_) ltac:(nbits_ok)).

Definition getActiveValue S f :=
  let%success expr := lcons S f R_NilValue using S in
  runs_eval runs S expr R_GlobalEnv.

Definition SYMBOL_BINDING_VALUE S s :=
  read%sym _, s_sym := s using S in
  if%success IS_ACTIVE_BINDING S s using S then
    getActiveValue S (sym_value s_sym)
  else result_success S (sym_value s_sym).

Definition setActiveValue S (f v : SExpRec_pointer) :=
  let%success arg_tail := lcons S v R_NilValue using S in
  let%success arg := lcons S R_QuoteSymbol arg_tail using S in
  let%success expr_tail := lcons S arg R_NilValue using S in
  let%success expr := lcons S f expr_tail using S in
  run%success runs_eval runs S expr R_GlobalEnv using S in
  result_skip S.

Definition SET_BINDING_VALUE S b val :=
  if%success BINDING_IS_LOCKED S b using S then
    result_error S "[SET_BINDING_VALUE] Can not change value of locked binding."
  else
    read%list b_car, _, _ := b using S in
    if%success IS_ACTIVE_BINDING S b using S then
      setActiveValue S b_car val
    else
      set%car b := val using S in
      result_skip S.

Definition BINDING_VALUE S b :=
  read%list b_car, _, _ := b using S in
  if%success IS_ACTIVE_BINDING S b using S then
    getActiveValue S b_car
  else result_success S b_car.

Definition IS_USER_DATABASE S rho :=
  read%defined rho_ := rho using S in
  let%success inh := inherits S rho "UserDefinedDatabase" using S in
  result_success S (obj rho_ && inh).

Definition gsetVar S (symbol value rho : SExpRec_pointer) : result unit :=
  if%success FRAME_IS_LOCKED S rho using S then
    read%sym symbol_, symbol_sym := symbol using S in
    ifb sym_value symbol_sym = R_UnboundValue then
      result_error S "[gsetVar] Can not add such a bidding to the base environment."
    else result_skip S in
  if%success BINDING_IS_LOCKED S symbol using S then
    result_error S "[gsetVar] Can not change value of locked biding."
  else
    read%sym symbol_, symbol_sym := symbol using S in
    if%success IS_ACTIVE_BINDING S symbol using S then
      setActiveValue S (sym_value symbol_sym) value
    else
      let symbol_sym := {|
          sym_pname := sym_pname symbol_sym ;
          sym_value := value ;
          sym_internal := sym_internal symbol_sym
        |} in
      let symbol_ := {|
          NonVector_SExpRec_header := NonVector_SExpRec_header symbol_ ;
          NonVector_SExpRec_data := symbol_sym
        |} in
      write%defined symbol := symbol_ using S in
      result_skip S.

Definition defineVar S (symbol value rho : SExpRec_pointer) : result unit :=
  ifb rho = R_EmptyEnv then
    result_error S "[defineVar] Can not assign values in the empty environment."
  else
    if%success IS_USER_DATABASE S rho using S then
      result_not_implemented "[defineVar] [R_ObjectTable]"
    else
      ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
        gsetVar S symbol value rho
      else
        if%success IS_SPECIAL_SYMBOL S symbol using S then
          run%success SET_SPECIAL_SYMBOL S rho false using S in
          result_skip S in
        (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
        read%env _, rho_env := rho using S in
        fold%return
        along env_frame rho_env
        as frame, _, frame_list do
          ifb list_tagval frame_list = symbol then
            run%success SET_BINDING_VALUE S frame value using S in
            run%success SET_MISSING S frame 0 ltac:(nbits_ok) using S in
            result_rreturn S tt
          else
            result_rskip S using S, runs, globals in
        if%success FRAME_IS_LOCKED S rho using S then
          result_error S "[defineVar] Can not add a binding to a locked environment."
        else
          let (S, l) := CONS S value (env_frame rho_env) in
          run%success SET_FRAME S rho l using S in
          set%tag l := symbol using S in
          result_skip S.

Definition setVarInFrame S (rho symbol value : SExpRec_pointer) :=
  ifb rho = R_EmptyEnv then
    result_success S (R_NilValue : SExpRec_pointer)
  else
    result_not_implemented "[setVarInFrame]".

Definition setVar S (symbol value rho : SExpRec_pointer) :=
  do%success rho := rho
  while result_success S (decide (rho <> R_EmptyEnv)) do
    let%success vl :=
      setVarInFrame S rho symbol value using S in
    ifb vl <> R_NilValue then
      result_success S (R_EmptyEnv : SExpRec_pointer)
    else
      read%env rho_, rho_env := rho using S in
      result_success S (env_enclos rho_env)
  using S, runs in
  defineVar S symbol value R_GlobalEnv.

Definition findVarInFrame3 S rho symbol (doGet : bool) :=
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type = NilSxp then
    result_error S "[findVarInFrame3] Use of NULL environment is defunct."
  else ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
    SYMBOL_BINDING_VALUE S symbol
  else ifb rho = R_EmptyEnv then
    result_success S (R_UnboundValue : SExpRec_pointer)
  else
    if%success IS_USER_DATABASE S rho using S then
      result_not_implemented "[findVarInFrame3] [R_ObjectTable]"
    else
      (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
      read%defined rho_ := rho using S in
      let%env _, rho_env := rho_ using S in
      fold%return
      along env_frame rho_env
      as frame, _, frame_list do
        ifb list_tagval frame_list = symbol then
          let%success r := BINDING_VALUE S frame using S in
          result_rreturn S r
        else result_rskip S using S, runs, globals in
      result_success S (R_UnboundValue : SExpRec_pointer).

Definition findVar S symbol rho :=
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type = NilSxp then
    result_error S "[findVar] Use of NULL environment is defunct."
  else ifb rho_type <> EnvSxp then
    result_error S "[findVar] Argument ‘rho’ is not an environment."
  else
    do%return rho := rho
    while result_success S (decide (rho <> R_EmptyEnv)) do
      let%success vl := findVarInFrame3 S rho symbol true using S in
      ifb vl <> R_UnboundValue then
        result_rreturn S vl
      else
        read%env _, rho_env := rho using S in
        result_rsuccess S (env_enclos rho_env) using S, runs in
    result_success S (R_UnboundValue : SExpRec_pointer).

Definition ddfindVar (S : state) (symbol rho : SExpRec_pointer) : result SExpRec_pointer :=
  result_not_implemented "[ddfindVar]".


Definition findFun3 S symbol rho (call : SExpRec_pointer) : result SExpRec_pointer :=
  let%success rho :=
    if%success IS_SPECIAL_SYMBOL S symbol using S then
      do%success rho := rho
      while let%success special := NO_SPECIAL_SYMBOLS S rho using S in
            result_success S (decide (rho <> R_EmptyEnv /\ special)) do
        read%env _, rho_env := rho using S in
        result_success S (env_enclos rho_env)
      using S, runs in
      result_success S rho
    else result_success S rho using S in
  do%return rho := rho
  while result_success S (decide (rho <> R_EmptyEnv)) do
    let%success vl := findVarInFrame3 S rho symbol true using S in
    run%return
      ifb vl <> R_UnboundValue then
        let%success vl_type := TYPEOF S vl using S in
        let%success vl :=
          ifb vl_type = PromSxp then
            runs_eval runs S vl rho
          else result_success S vl using S in
        let%success vl_type := TYPEOF S vl using S in
        ifb vl_type = CloSxp \/ vl_type = BuiltinSxp \/ vl_type = SpecialSxp then
          result_rreturn S vl
        else ifb vl = R_MissingArg then
          let%success str_symbol := PRINTNAME S symbol using S in
          let%success str_symbol_ := CHAR S str_symbol using S in
          result_error S ("[findFun3] Argument “" ++ str_symbol_ ++ "” is missing, with no default.")
        else result_rskip S
      else result_rskip S using S in
    read%env _, rho_env := rho using S in
    result_rsuccess S (env_enclos rho_env)
  using S, runs in
  let%success str_symbol := PRINTNAME S symbol using S in
  let%success str_symbol_ := CHAR S str_symbol using S in
  result_error S ("[findFun3] Could not find function “" ++ str_symbol_ ++ "”.").


(** ** attrib.c **)

(** The function names of this section corresponds to the function names
  in the file main/attrib.c. **)

Definition isOneDimensionalArray S vec :=
  let%success ivec := isVector S vec using S in
  let%success ilist := isList S vec using S in
  let%success ilang := isLanguage S vec using S in
  ifb ivec \/ ilist \/ ilang then
    let%success s := runs_getAttrib runs S vec R_DimSymbol using S in
    let%success s_type := TYPEOF S s using S in
    ifb s_type = IntSxp then
      let%success len := R_length S s using S in
      ifb len = 1 then result_success S true
      else result_success S false
    else result_success S false
  else result_success S false.

Definition getAttrib0 S (vec name : SExpRec_pointer) :=
  run%exit
    ifb name = R_NamesSymbol then
      run%return
        if%success isOneDimensionalArray S vec using S then
          let%success s := runs_getAttrib runs S vec R_DimNamesSymbol using S in
          let%success s_type := TYPEOF S s using S in
          ifb s_type <> NilSxp then
            read%Pointer s_0 := s at 0 using S in
            map%pointer s_0 with set_named_plural using S in
            result_rreturn S s_0
          else result_rskip S
        else result_rskip S using S in
      result_not_implemented "[getAttrib0] TODO"
    else result_rskip S using S in
  read%defined vec_ := vec using S in
  fold%return
  along attrib vec_
  as s, _, s_list do
    ifb list_tagval s_list = name then
      let%success s_car_type := TYPEOF S (list_carval s_list) using S in
      ifb name = R_DimNamesSymbol /\ s_car_type = ListSxp then
        result_error S "[getAttrib0] Old list is no longer allowed for dimnames attributes."
      else
        map%pointer (list_carval s_list) with set_named_plural using S in
        result_rreturn S (list_carval s_list)
    else result_rskip S
  using S, runs, globals in
  result_success S (R_NilValue : SExpRec_pointer).

Definition getAttrib S (vec name : SExpRec_pointer) :=
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "[getAttrib] Can not have attributes on a [CharSxp]."
  else
    read%defined vec_ := vec using S in
    ifb attrib vec_ = R_NilValue /\ ~ (vec_type  = ListSxp \/ vec_type  = LangSxp) then
      result_success S (R_NilValue : SExpRec_pointer)
    else
      let%success name_type := TYPEOF S name using S in
      let%success name :=
        ifb name_type = StrSxp then
          read%VectorPointer name_ := name using S in
          let%success str := STRING_ELT S name 0 using S in
          let%success sym := installTrChar S str using S in
          result_success S sym
        else result_success S name using S in
      ifb name = R_RowNamesSymbol then
        let%success s := getAttrib0 S vec name using S in
        read%defined s_ := s using S in
        if%success isInteger S s using S then
          let%defined s_length := get_VecSxp_length s_ using S in
          ifb s_length = 2 then
            let%Integer s_0 := s_ at 0 using S in
            ifb s_0 = R_NaInt then
              let%Integer s_1 := s_ at 1 using S in
              let n := abs s_1 in
              let (S, s) :=
                alloc_vector_int S
                  (ArrayList.from_list (map (id : nat -> int) (seq 1 n))) in
              result_success S s
            else result_success S s
          else result_success S s
        else result_success S s
      else getAttrib0 S vec name.

Definition installAttrib S vec name val :=
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "[installAttrib] Cannot set attribute on a CharSxp."
  else ifb vec_type = SymSxp then
    result_error S "[installAttrib] Cannot set attribute on a symbol."
  else
    read%defined vec_ := vec using S in
    fold%return t := R_NilValue : SExpRec_pointer
    along attrib vec_
    as s, _, s_list do
      ifb list_tagval s_list = name then
        set%car s := val using S in
          result_rreturn S val
      else result_rsuccess S s
    using S, runs, globals in
    let (S, s) := CONS S val R_NilValue in
    set%tag s := name using S in
    run%success
      ifb attrib vec_ = R_NilValue then
        set%attrib vec := s using S in
        result_skip S
      else
        set%cdr t := s using S in
        result_skip S using S in
    result_success S val.

Definition stripAttrib S (tag lst : SExpRec_pointer) :=
  ifb lst = R_NilValue then
    result_success S lst
  else
    read%list _, lst_cdr, lst_tag := lst using S in
    ifb tag = lst_tag then
      runs_stripAttrib runs S tag lst_cdr
    else
      let%success r :=
        runs_stripAttrib runs S tag lst_cdr using S in
      set%cdr lst := r using S in
      result_success S lst.

Definition removeAttrib S (vec name : SExpRec_pointer) :=
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "[removeAttrib] Cannot set attribute on a CharSxp."
  else
    let%success pl := isPairList S vec using S in
    ifb name = R_NamesSymbol /\ pl then
      fold%success
      along vec
      as t, _, _ do
        set%tag t := R_NilValue using S in
        result_skip S
      using S, runs, globals in
      result_success S (R_NilValue : SExpRec_pointer)
    else
      read%defined vec_ := vec using S in
      run%success
        ifb name = R_DimSymbol then
          let%success r :=
            stripAttrib S R_DimNamesSymbol (attrib vec_) using S in
          set%attrib vec := r using S in
          result_skip S
        else
          result_skip S using S in
      let%success r :=
        stripAttrib S R_DimSymbol (attrib vec_) using S in
      set%attrib vec := r using S in
      run%success
        ifb name = R_ClassSymbol then
          set%obj vec := false using S in
          result_skip S
        else
          result_skip S using S in
      result_success S (R_NilValue : SExpRec_pointer).

Definition setAttrib S (vec name val : SExpRec_pointer) :=
  let%success name :=
    let%success name_type := TYPEOF S name using S in
    ifb name_type = StrSxp then
      let%success str := STRING_ELT S name 0 using S in
      installTrChar S str
    else result_success S name using S in
  ifb val = R_NilValue then
    removeAttrib S vec name
  else
    ifb vec = R_NilValue then
      result_error S "[setAttrib] Attempt to set an attribute on NULL."
    else
      let%success val :=
        read%defined val_ := val using S in
        ifb named val_ <> named_temporary then
          R_FixupRHS S vec val
        else result_success S val using S in
      ifb name = R_NamesSymbol then
        result_not_implemented "[namesgets]"
      else ifb name = R_DimSymbol then
        result_not_implemented "[dimgets]"
      else ifb name = R_DimNamesSymbol then
        result_not_implemented "[dimnamesgets]"
      else ifb name = R_ClassSymbol then
        result_not_implemented "[classgets]"
      else ifb name = R_TspSymbol then
        result_not_implemented "[tspgets]"
      else ifb name = R_CommentSymbol then
        result_not_implemented "[commentgets]"
      else ifb name = R_RowNamesSymbol then
        result_not_implemented "[row_names_gets]"
      else installAttrib S vec name val.


(** ** utils.c **)

(** The function names of this section corresponds to the function names
  in the file main/utils.c. **)

Definition truenames : list string :=
  ["T"; "True"; "TRUE"; "true"]%string.

Definition StringTrue name :=
  decide (Mem name truenames).

Definition falsenames : list string :=
  ["F"; "False"; "FALSE"; "false"]%string.

Definition StringFalse name :=
  decide (Mem name falsenames).


(** ** coerce.c **)

(** The function names of this section corresponds to the function names
  in the file main/coerce.c. **)

Definition LogicalFromString S (x : SExpRec_pointer) :=
  ifb x <> R_NaString then
    let%success c := CHAR S x using S in
    if StringTrue c then result_success S (1 : int)
    else if StringFalse c then result_success S (0 : int)
    else result_success S NA_LOGICAL
  else result_success S NA_LOGICAL.

Definition LogicalFromInteger S (x : int) : result int :=
  ifb x = NA_INTEGER then result_success S NA_LOGICAL
  else result_success S (ifb x <> 0 then 1 : int else 0).

Definition LogicalFromReal S x : result int :=
  ifb ISNAN x then result_success S NA_LOGICAL
  else result_success S (if negb (Double.is_zero x) then 1 : int else 0).

Definition LogicalFromComplex S x : result int :=
  ifb ISNAN (Rcomplex_r x) \/ ISNAN (Rcomplex_i x) then result_success S NA_LOGICAL
  else result_success S (ifb ~ Double.is_zero (Rcomplex_r x)
                             \/ ~ Double.is_zero (Rcomplex_i x) then 1 : int else 0).

Definition asLogical S x :=
  if%success isVectorAtomic S x using S then
    let%success len := XLENGTH S x using S in
    ifb len < 1 then
      result_success S NA_LOGICAL
    else
      read%defined x_ := x using S in
      match type x_ with
      | LglSxp => LOGICAL_ELT S x 0
      | IntSxp =>
        let%success i := INTEGER_ELT S x 0 using S in
        LogicalFromInteger S i
      | RealSxp =>
        let%success r := REAL_ELT S x 0 using S in
        LogicalFromReal S r
      | CplxSxp =>
        let%success c := COMPLEX_ELT S x 0 using S in
        LogicalFromComplex S c
      | StrSxp =>
        let%success s := STRING_ELT S x 0 using S in
        LogicalFromString S s
      | RawSxp =>
        let%success s := RAW_ELT S x 0 using S in
        LogicalFromString S s
      | _ => result_error S "[asLogical] Unimplemented type."
      end
  else
    let%success x_type := TYPEOF S x using S in
    ifb x_type = CharSxp then
      LogicalFromString S x
    else result_success S NA_LOGICAL.


(** ** eval.c **)

(** The function names of this section corresponds to the function names
  in the file main/eval.c. **)

(** The function [forcePromise] evaluates a promise if needed. **)
Definition forcePromise S (e : SExpRec_pointer) : result SExpRec_pointer :=
  read%prom e_, e_prom := e using S in
  ifb prom_value e_prom = R_UnboundValue then
    run%success
      ifb nbits_to_nat (gp e_) <> 0 then
        ifb nbits_to_nat (gp e_) = 1 then
          result_error S "[forcePromise] Promise already under evaluation."
        else
          (** The C code emitted a warning here: restarting interrupted promise evaluation.
            This may be a sign that this part should be ignored. *)
          result_skip S
      else result_skip S using S in
    set%gp e with @nat_to_nbits 16 1 ltac:(nbits_ok) using S in
    let%success val := runs_eval runs S (prom_expr e_prom) (prom_env e_prom) using S in
    set%gp e with @nat_to_nbits 16 0 ltac:(nbits_ok) using S in
    map%pointer val with set_named_plural using S in
    read%prom e_, e_prom := e using S in
    let e_prom := {|
        prom_value := val ;
        prom_expr := prom_expr e_prom ;
        prom_env := R_NilValue
      |} in
    let e_ := {|
        NonVector_SExpRec_header := e_ ;
        NonVector_SExpRec_data := e_prom
      |} in
    write%defined e := e_ using S in
    result_success S val
  else result_success S (prom_value e_prom).

Definition R_execClosure S (call newrho sysparent rho arglist op : SExpRec_pointer)
    : result SExpRec_pointer :=
  let%success cntxt :=
    begincontext S Ctxt_Return call newrho sysparent arglist op using S in
  read%clo op_, op_clo := op using S in
  let body := clo_body op_clo in
  (** JIT functions have been ignored here. **)
  let%success R_srcef := getAttrib S op R_SrcrefSymbol using S in
  set%longjump cjmpbuf cntxt as jmp using S, runs in
  let%success cntxt_returnValue :=
    ifb jmp <> empty_context_type then
      ifb jumptarget cntxt = None then
        ifb R_ReturnedValue S = R_RestartToken then
          let cntxt := context_with_callflag cntxt Ctxt_Return in
          let S := state_with_context S cntxt in
          let S := update_R_ReturnedValue S R_NilValue in
          runs_eval runs S body newrho
        else result_success S (R_ReturnedValue S)
      else result_success S NULL
    else runs_eval runs S body newrho using S in
  let cntxt := context_with_returnValue cntxt cntxt_returnValue in
  let S := state_with_context S cntxt in
  run%success endcontext S cntxt using S in
  result_success S (returnValue cntxt).

Definition applyClosure S (call op arglist rho suppliedvars : SExpRec_pointer)
    : result SExpRec_pointer :=
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type <> EnvSxp then
    result_error S "[applyClosure] ‘rho’ must be an environment."
  else
    read%clo op_, op_clo := op using S in
    let formals := clo_formals op_clo in
    let savedrho := clo_env op_clo in
    let%success actuals := matchArgs S formals arglist call using S in
    let%success newrho := NewEnvironment S formals actuals savedrho using S in
    fold%success a := actuals
    along formals
    as f_car, f_tag do
      read%list a_car, a_cdr, _ := a using S in
      ifb a_car = R_MissingArg /\ f_car <> R_MissingArg then
        let%success newprom := mkPromise S f_car newrho using S in
        set%car a := newprom using S in
        run%success SET_MISSING S a 2 ltac:(nbits_ok) using S in
        result_success S a_cdr
      else result_success S a_cdr using S, runs, globals in
    run%success
      ifb suppliedvars <> R_NilValue then
         addMissingVarsToNewEnv S newrho suppliedvars
       else result_skip S using S in
    if%success R_envHasNoSpecialSymbols S newrho using S then
      run%success SET_SPECIAL_SYMBOL S newrho false using S in
      result_skip S in
    R_execClosure S call newrho
      (ifb callflag (R_GlobalContext S) = Ctxt_Generic then
         sysparent (R_GlobalContext S)
       else rho)
      rho arglist op.

Definition promiseArgs S (el rho : SExpRec_pointer) : result SExpRec_pointer :=
  let (S, tail) := CONS S R_NilValue R_NilValue in
  fold%success (ans, tail) := (tail, tail)
  along el
  as el_car, el_tag do
    ifb el_car = R_DotsSymbol then
      let%success h := findVar S el_car rho using S in
      let%success h_type := TYPEOF S h using S in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%success tail := tail
        along h
        as h_car, h_tag do
          let%success h_car_type := TYPEOF S h_car using S in
          run%success
            ifb h_car_type = PromSxp \/ h_car = R_MissingArg then
              let (S, l) := CONS S h_car R_NilValue in
              set%cdr tail := l using S in
              result_skip S
            else
              let%success prom :=
                mkPromise S h_car rho using S in
              let (S, l) := CONS S prom R_NilValue in
              set%cdr tail := l using S in
              result_skip S using S in
          read%list _, tail_cdr, _ := tail using S in
          let tail := tail_cdr in
          run%success
            ifb h_tag <> R_NilValue then
              set%tag tail := h_tag using S in
              result_skip S
            else result_skip S using S in
          result_success S tail
        using S, runs, globals in
        result_success S (ans, tail)
      else ifb h <> R_MissingArg then
        result_error S "[promiseArgs] ‘...’ used in an incorrect context."
      else result_success S (ans, tail)
    else ifb el_car = R_MissingArg then
      let (S, l) := CONS S R_MissingArg R_NilValue in
      set%cdr tail := l using S in
      read%list _, tail_cdr, _ := tail using S in
      let tail := tail_cdr in
      set%tag tail := el_tag using S in
      result_success S (ans, tail)
    else
      let%success prom :=
        mkPromise S el_car rho using S in
      let (S, l) := CONS S prom R_NilValue in
      set%cdr tail := l using S in
      read%list _, tail_cdr, _ := tail using S in
      let tail := tail_cdr in
      set%tag tail := el_tag using S in
      result_success S (ans, tail)
  using S, runs, globals in
  read%list _, ans_cdr, _ := ans using S in
  result_success S ans_cdr.

Definition PRIMFUN S x :=
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (fun_cfun x_fun).

Definition PRIMVAL S x :=
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (fun_code x_fun).

Definition PPINFO S x :=
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (fun_gram x_fun).

Definition PRIMARITY S x :=
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (fun_arity x_fun).

Definition PRIMINTERNAL S x :=
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (funtab_eval_arg_internal (fun_eval x_fun)).

Definition evalList S (el rho call : SExpRec_pointer) n :=
  fold%success (n, head, tail) := (n, R_NilValue : SExpRec_pointer, R_NilValue : SExpRec_pointer)
  along el
  as el_car, el_tag
    do
    let n := n + 1 in
    ifb el_car = R_DotsSymbol then
      let%success h := findVar S el_car rho using S in
      let%success h_type := TYPEOF S h using S in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%success tail := tail
        along h
        as h_car, h_tag
        do
          let%success tmp_ev := runs_eval runs S h_car rho using S in
          let (S, ev) := CONS_NR S tmp_ev R_NilValue in
          let%success head :=
            ifb head = R_NilValue then
              result_success S ev
            else
              set%cdr tail := ev using S in
              result_success S head using S in
          run%success
            ifb h_tag <> R_NilValue then
              set%tag ev := h_tag using S in
              result_skip S
            else result_skip S using S in
          result_success S ev
        using S, runs, globals in
        result_success S (n, head, tail)
      else ifb h <> R_MissingArg then
        result_error S "[evalList] ‘...’ used in an incorrect context."
      else result_success S (n, head, tail)
    else ifb el_car = R_MissingArg then
      result_error S "[evalList] Argument is empty."
    else
      let%success ev := runs_eval runs S el_car rho using S in
      let (S, ev) := CONS_NR S ev R_NilValue in
      let%success head :=
        ifb head = R_NilValue then
          result_success S ev
        else
          set%cdr tail := ev using S in
          result_success S head using S in
      run%success
        ifb el_tag <> R_NilValue then
          set%tag ev := el_tag using S in
          result_skip S
        else result_skip S using S in
      result_success S (n, head, ev)
  using S, runs, globals in
  result_success S head.

(** The function [eval] evaluates its argument to an unreducible value. **)
Definition eval S (e rho : SExpRec_pointer) :=
  let%success e_type := TYPEOF S e using S in
  match e_type with
  | NilSxp
  | ListSxp
  | LglSxp
  | IntSxp
  | RealSxp
  | StrSxp
  | CplxSxp
  | RawSxp
  | S4Sxp
  | SpecialSxp
  | BuiltinSxp
  | EnvSxp
  | CloSxp
  | VecSxp
  | ExtptrSxp
  | WeakrefSxp
  | ExprSxp =>
    map%pointer e with set_named_plural using S in
    result_success S e
  | _ =>
    let%success rho_type := TYPEOF S rho using S in
    ifb rho_type <> EnvSxp then
      result_error S "[eval] ‘rho’ must be an environment."
    else
      match e_type with
      | BcodeSxp =>
        (** See Line 3543 of src/main/eval.c, for a definition of this bytecode,
          Line 5966 of the same file for the evaluator.
          We do not consider byte code for now in this formalisation. **)
        result_not_implemented "[eval] bcEval"
      | SymSxp =>
        ifb e = R_DotsSymbol then
          result_error S "[eval] ‘...’ used in an incorrect context."
        else
          let%success tmp :=
            if%success DDVAL S e using S then
              ddfindVar S e rho
            else
              findVar S e rho using S in
          ifb tmp = R_UnboundValue then
            result_error S "[eval] Object not found."
          else
            let%success ddval := DDVAL S e using S in
            ifb tmp = R_MissingArg /\ ~ ddval then
              result_error S "[eval] Argument is missing, with no default."
            else
              let%success tmp_type := TYPEOF S tmp using S in
              ifb tmp_type = PromSxp then
                read%prom _, tmp_prom := tmp using S in
                let%success tmp :=
                  ifb prom_value tmp_prom = R_UnboundValue then
                    forcePromise S tmp
                  else result_success S (prom_value tmp_prom) using S in
                map%pointer tmp with set_named_plural using S in
                result_success S tmp
              else
                read%defined tmp_ := tmp using S in
                run%success
                  ifb type tmp_ <> NilSxp /\ named tmp_ = named_temporary then
                    map%pointer tmp with set_named_unique using S in
                    result_skip S
                  else result_skip S using S in
                result_success S tmp
      | PromSxp =>
        run%success
          read%prom _, e_prom := e using S in
          ifb prom_value e_prom = R_UnboundValue then
            run%success forcePromise S e using S in
            result_skip S
          else result_skip S using S in
        read%prom _, e_prom := e using S in
        result_success S (prom_value e_prom)
      | LangSxp =>
        read%list e_car, e_cdr, _ := e using S in
        let%success e_car_type := TYPEOF S e_car using S in
        let%success op :=
          ifb e_car_type = SymSxp then
            let%success ecall :=
              ifb callflag (R_GlobalContext S) = Ctxt_CCode then
                result_success S (call (R_GlobalContext S))
              else result_success S e using S in
            findFun3 S e_car rho ecall
          else runs_eval runs S e_car rho using S in
        let%success op_type := TYPEOF S op using S in
        match op_type with
        | SpecialSxp =>
          let%success f := PRIMFUN S op using S in
          f S e op e_cdr rho
        | BuiltinSxp =>
          let%success tmp := evalList S e_cdr rho e 0 using S in
          let%success infos := PPINFO S op using S in
          ifb PPinfo_kind infos = PP_FOREIGN then
            let%success cntxt :=
              begincontext S Ctxt_Builtin e R_BaseEnv R_BaseEnv R_NilValue R_NilValue using S in
            let%success f := PRIMFUN S op using S in
            let%success tmp := f S e op tmp rho using S in
            run%success endcontext S cntxt using S in
            result_success S tmp
          else
            let%success f := PRIMFUN S op using S in
            f S e op tmp rho
        | CloSxp =>
          let%success tmp := promiseArgs S e_cdr rho using S in
          applyClosure S e op tmp rho R_NilValue
        | _ => result_error S "[eval] Attempt to apply non-function."
        end
      | DotSxp => result_error S "[eval] ‘...’ used in an incorrect context"
      | _ => result_error S "[eval] Type unimplemented in the R source code."
      end
  end.


(** Evaluates the expression in the global environment. **)
Definition eval_global S e :=
  eval S e R_GlobalEnv.

End Parameterised.

