(** ** Rinlinedfuns.c **)

(** The function names of this section correspond to the function
  names in the file include/Rinlinedfuns.c. **)

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
Require Import Ascii Double.
Require Import Loops.
Require Import RinternalsCore.
Require Import Memory.

Section Parameterised.

(** * Global Variables **)

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition get_R_FunTab S :=
  add%stack "get_R_FunTab" in
  match runs_R_FunTab runs with
  | None => result_bottom S
  | Some t => result_success S t
  end.

Definition read_R_FunTab S n :=
  add%stack "read_R_FunTab" in
  let%success t := get_R_FunTab S using S in
  ifb n >= ArrayList.length t then
    result_impossible S "Out of bounds."
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
Definition NA_INTEGER := R_NaInt.
Definition NA_LOGICAL := R_NaInt.
Definition R_PosInf : double := Double.posInf.
Definition R_NegInf : double := Double.negInf.
Definition R_NaN : double := Double.NaN.
Definition R_NaReal : double := Double.NaN1954.
Definition NA_REAL : double := R_NaReal.

Definition R_NaString := NA_STRING.

Definition R_XLEN_T_MAX : int := Zpos 4503599627370496.

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

(** End of Global Variables **)

(** The way the original functions [allocVector], [allocVector3], etc.
  from R source code are defined is not compatible with the way the
  memory of the C language has been formalised here. The functions
  below are thus slightly different from their C counterparts.  The
  [repeat] function of Coq can be used to initialise their data. **)

Definition alloc_vector_char S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_char R_NilValue v_data).

Definition alloc_vector_lgl S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_lgl R_NilValue v_data).

Definition alloc_vector_int S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_int R_NilValue v_data).

Definition alloc_vector_real S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_real R_NilValue v_data).

Definition alloc_vector_cplx S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_cplx R_NilValue v_data).

(** The following allocators uses pointers. Note that the original
  [allocVector] function initialises them to [R_NilValue] (and not
  [NULL], for instance) by default. **)

Definition alloc_vector_str S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_str R_NilValue v_data).

Definition alloc_vector_vec S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_vec R_NilValue v_data).

Definition alloc_vector_expr S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_expr R_NilValue v_data).

(** We however propose the following smart constructor, based on
  [allocVector]/[allocVector3] from main/memory.c. **)
(** Note: using [arbitrary] would here be more natural than these default values
  for the base cases, but it would not behave well in the extraction. **)
Definition allocVector S type (length : nat) :=
  add%stack "allocVector" in
  ifb (length : int) > R_XLEN_T_MAX then
    result_error S "Vector is too large"
  else
    let alloc {T} (allocator : state -> ArrayList.array T -> state * SEXP) (base : T) :=
      let (S, v) := allocator S (ArrayList.from_list (repeat base length)) in
      result_success S v in
    match type with
    | NilSxp =>
      result_success S (R_NilValue : SEXP)
    | RawSxp =>
      result_not_implemented "Raw type."
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
      alloc alloc_vector_str (R_NilValue : SEXP)
    | ExprSxp =>
      alloc alloc_vector_expr (R_NilValue : SEXP)
    | VecSxp =>
      alloc alloc_vector_vec (R_NilValue : SEXP)
    | LangSxp =>
      ifb length = 0 then result_success S (R_NilValue : SEXP)
      else
        let (S, s) := allocList globals S length in
        map%pointer s with set_type LangSxp using S in
        result_success S s
    | ListSxp =>
      let (S, s) := allocList globals S length in
      result_success S s
    | _ => result_error S "Invalid type in vector allocation."
    end.

Definition ScalarLogical x : SEXP :=
  ifb x = NA_LOGICAL then
    R_LogicalNAValue
  else ifb x <> 0 then
    R_TrueValue
  else R_FalseValue.

Definition ScalarInteger S x : state * SEXP :=
  alloc_vector_int S (ArrayList.from_list [x]).

Definition ScalarReal S x : state * SEXP :=
  alloc_vector_real S (ArrayList.from_list [x]).

Definition ScalarComplex S x : state * SEXP :=
  alloc_vector_cplx S (ArrayList.from_list [x]).

Definition ScalarString S (x : SEXP) : result SEXP :=
  add%stack "ScalarString" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> CharSxp then
    result_error S "The given argument is not of type ‘CharSxp’."
  else
    let (S, s) := alloc_vector_str S (ArrayList.from_list [x]) in
    result_success S s.

Definition isPairList S s :=
  add%stack "isPairList" in
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

Definition isVectorList S s :=
  add%stack "isVectorList" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | VecSxp
  | ExprSxp =>
    result_success S true
  | _ =>
    result_success S false
  end.

(** The following function is actually from main/altrep.c. It has been
  placed here to solve a circular file dependency. **)

Definition ALTREP_LENGTH (S : state) (x : SEXP) : result nat :=
  unimplemented_function "ALTREP_LENGTH".

Definition XLENGTH_EX S x :=
  add%stack "XLENGTH_EX" in
  read%defined x_ := x using S in
  if alt x_ then ALTREP_LENGTH S x
  else STDVEC_LENGTH S x.

Definition XLENGTH := XLENGTH_EX.

Definition LENGTH_EX S (x : SEXP) :=
  add%stack "LENGTH_EX" in
  ifb x = R_NilValue then
    result_success S 0
  else XLENGTH S x.

Definition LENGTH := LENGTH_EX.

Definition xlength S s :=
  add%stack "xlength" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | NilSxp =>
    result_success S 0
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | CharSxp
  | VecSxp
  | ExprSxp
  | RawSxp =>
    LENGTH S s
  | ListSxp
  | LangSxp
  | DotSxp =>
    do%success (s, i) := (s, 0)
    whileb s <> NULL /\ s <> R_NilValue do
      read%list _, s_cdr, _ := s using S in
      result_success S (s_cdr, 1 + i) using S, runs in
    result_success S i
  | EnvSxp =>
    unimplemented_function "Rf_envlength"
  | _ =>
    result_success S 1
  end.
(** Named [length] in the C source file. **)
Definition R_length S s :=
  add%stack "R_length" in
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
    whileb s <> NULL /\ s <> R_NilValue do
      read%list _, s_cdr, _ := s using S in
      result_success S (s_cdr, 1 + i) using S, runs in
    result_success S i
  | EnvSxp =>
    unimplemented_function "Rf_envlength"
  | _ =>
    result_success S 1
  end.

Definition inherits S s name :=
  add%stack "inherits" in
  read%defined s_ := s using S in
  if obj s_ then
    let%success klass := runs_getAttrib runs S s R_ClassSymbol using S in
    read%VectorPointer klass_vector := klass using S in
    do%success b := false
    for str in%array VecSxp_data klass_vector do
      if b then result_success S true
      else
        let%success str_ := CHAR S str using S in
        result_success S (decide (str_ = name)) using S in
    result_success S b
  else result_success S false.

Definition isVectorAtomic S s :=
  add%stack "isVectorAtomic" in
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
  add%stack "isInteger" in
  let%success s_type := TYPEOF S s using S in
  let%success inh := inherits S s "factor" using S in
  result_success S (decide (s_type = IntSxp /\ ~ inh)).

Definition isList S s :=
  add%stack "isList" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s = R_NilValue \/ s_type = ListSxp)).

Definition isLanguage S s :=
  add%stack "isLanguage" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s = R_NilValue \/ s_type = LangSxp)).

Definition isNumeric S s :=
  add%stack "isNumeric" in
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
  add%stack "isNumber" in
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

Definition isFrame S s :=
  add%stack "isFrame" in
  if%success OBJECT S s using S then
    let%success klass := runs_getAttrib runs S s R_ClassSymbol using S in
    let%success klass_len := R_length S klass using S in
    do%exit
    for i from 0 to klass_len - 1 do
      let%success str := STRING_ELT S klass i using S in
      let%success str_ := CHAR S str using S in
      ifb str_ = "data.frame"%string then
        result_rreturn S true
      else result_rskip S using S in
    result_success S false
  else result_success S false.

Definition isNewList S s :=
  add%stack "isNewList" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s = R_NilValue \/ s_type = VecSxp)).

Definition SCALAR_LVAL S x :=
  add%stack "SCALAR_LVAL" in
  read%Logical r := x at 0 using S in
  result_success S r.

Definition SCALAR_IVAL S x :=
  add%stack "SCALAR_IVAL" in
  read%Integer r := x at 0 using S in
  result_success S r.

Definition SCALAR_DVAL S x :=
  add%stack "SCALAR_DVAL" in
  read%Real r := x at 0 using S in
  result_success S r.

Definition SET_SCALAR_LVAL S x v :=
  add%stack "SET_SCALAR_LVAL" in
  write%Logical x at 0 := v using S in
  result_skip S.

Definition SET_SCALAR_IVAL S x v :=
  add%stack "SET_SCALAR_IVAL" in
  write%Integer x at 0 := v using S in
  result_skip S.

Definition SET_SCALAR_DVAL S x v :=
  add%stack "SET_SCALAR_DVAL" in
  write%Real x at 0 := v using S in
  result_skip S.


Definition lcons S car cdr :=
  add%stack "lcons" in
  let (S, e) := CONS globals S car cdr in
  map%pointer e with set_type LangSxp using S in
  result_success S e.

Definition LCONS := lcons.

Definition list1 S s :=
  CONS globals S s R_NilValue.

Definition list2 S s t :=
  let (S, l) := list1 S t in
  CONS globals S s l.

Definition list3 S s t u :=
  let (S, l) := list2 S t u in
  CONS globals S s l.

Definition list4 S s t u v :=
  let (S, l) := list3 S t u v in
  CONS globals S s l.

Definition list5 S s t u v w :=
  let (S, l) := list4 S t u v w in
  CONS globals S s l.

Definition list6 S s t u v w x :=
  let (S, l) := list5 S t u v w x in
  CONS globals S s l.

Definition lang1 S s :=
  add%stack "lang1" in
  lcons S s R_NilValue.

Definition lang2 S s t :=
  add%stack "lang2" in
  let (S, l) := list1 S t in
  lcons S s l.

Definition lang3 S s t u :=
  add%stack "lang3" in
  let (S, l) := list2 S t u in
  lcons S s l.

Definition lang4 S s t u v :=
  add%stack "lang4" in
  let (S, l) := list3 S t u v in
  lcons S s l.

Definition lang5 S s t u v w :=
  add%stack "lang5" in
  let (S, l) := list4 S t u v w in
  lcons S s l.

Definition lang6 S s t u v w x :=
  add%stack "lang6" in
  let (S, l) := list5 S t u v w x in
  lcons S s l.


Definition ALTLOGICAL_ELT S x i :=
  add%stack "ALTLOGICAL_ELT" in
  read%Logical x_i := x at i using S in
  result_success S x_i.

Definition LOGICAL_ELT S x i :=
  add%stack "LOGICAL_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTLOGICAL_ELT S x i
  else
    read%Logical x_i := x at i using S in
    result_success S x_i.

Definition ALTINTEGER_ELT (S : state) (x : SEXP) (i : nat) : result int :=
  unimplemented_function "ALTINTEGER_ELT".

Definition INTEGER_ELT S x i :=
  add%stack "INTEGER_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTINTEGER_ELT S x i
  else
    read%Integer x_i := x at i using S in
    result_success S x_i.

Definition ALTREAL_ELT (S : state) (x : SEXP) (i : nat) : result double :=
  unimplemented_function "ALTREAL_ELT".

Definition REAL_ELT S x i :=
  add%stack "REAL_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTREAL_ELT S x i
  else
    read%Real x_i := x at i using S in
    result_success S x_i.

Definition ALTCOMPLEX_ELT (S : state) (x : SEXP) (i : nat) : result Rcomplex :=
  unimplemented_function "ALTCOMPLEX_ELT".

Definition COMPLEX_ELT S x i :=
  add%stack "COMPLEX_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTCOMPLEX_ELT S x i
  else
    read%Complex x_i := x at i using S in
    result_success S x_i.

Definition ALTRAW_ELT S x i :=
  add%stack "ALTRAW_ELT" in
  read%Pointer x_i := x at i using S in
  result_success S x_i.

Definition RAW_ELT S x i :=
  add%stack "RAW_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTRAW_ELT S x i
  else
    read%Pointer x_i := x at i using S in
    result_success S x_i.

(** The following function is actually from main/altrep.c. It has been
  placed here to solve a circular file dependency. **)

Definition ALTREP_TRUELENGTH S (x : SEXP) :=
  add%stack "ALTREP_TRUELENGTH" in
  result_success S 0.

Definition XTRUELENGTH S x :=
  add%stack "XTRUELENGTH" in
  if%success ALTREP S x using S then
    ALTREP_TRUELENGTH S x
  else STDVEC_TRUELENGTH S x.

End Parameterised.
