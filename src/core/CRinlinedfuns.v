(** Core.CRinlinedfuns.
  The function names in this file correspond to the function
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
Require Import Ascii.
Require Import Loops.
Require Import CRinternals.
Require Import CMemory.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


(** The way the original functions [allocVector], [allocVector3], etc.
  from R source code are defined is not compatible with the way the
  memory of the C language has been formalised here. The functions
  below are thus slightly different from their C counterparts.  The
  [repeat] function of Coq can be used to initialise their data. **)

Definition alloc_vector_char v_data : state * SEXP :=
  alloc_SExp (make_SExpRec_char R_NilValue v_data).

Definition alloc_vector_lgl v_data : state * SEXP :=
  alloc_SExp (make_SExpRec_lgl R_NilValue v_data).

Definition alloc_vector_int v_data : state * SEXP :=
  alloc_SExp (make_SExpRec_int R_NilValue v_data).

Definition alloc_vector_real v_data : state * SEXP :=
  alloc_SExp (make_SExpRec_real R_NilValue v_data).

Definition alloc_vector_cplx v_data : state * SEXP :=
  alloc_SExp (make_SExpRec_cplx R_NilValue v_data).

(** The following allocators uses pointers. Note that the original
  [allocVector] function initialises them to [R_NilValue] (and not
  [NULL], for instance) by default. **)

Definition alloc_vector_str v_data : state * SEXP :=
  alloc_SExp (make_SExpRec_str R_NilValue v_data).

Definition alloc_vector_vec v_data : state * SEXP :=
  alloc_SExp (make_SExpRec_vec R_NilValue v_data).

Definition alloc_vector_expr v_data : state * SEXP :=
  alloc_SExp (make_SExpRec_expr R_NilValue v_data).

(** We however propose the following smart constructor, based on
  [allocVector]/[allocVector3] from main/memory.c. **)
(** Note: using [arbitrary] would here be more natural than these default values
  for the base cases, but it would not behave well in the extraction. **)
Definition allocVector type (length : nat) :=
  add%stack "allocVector" in
  ifb (length : int) > R_XLEN_T_MAX then
    result_error "Vector is too large"
  else
    let alloc {T} (allocator : state -> ArrayList.array T -> state * SEXP) (base : T) :=
      let (S, v) := allocator (ArrayList.from_list (repeat base length)) in
      result_success v in
    match type with
    | NilSxp =>
      result_success (R_NilValue : SEXP)
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
      ifb length = 0 then result_success (R_NilValue : SEXP)
      else
        let (S, s) := allocList globals length in
        set%type s := LangSxp in
        result_success s
    | ListSxp =>
      let (S, s) := allocList globals length in
      result_success s
    | _ => result_error "Invalid type in vector allocation."
    end.

Definition ScalarLogical x : SEXP :=
  ifb x = NA_LOGICAL then
    R_LogicalNAValue
  else ifb x <> 0 then
    R_TrueValue
  else R_FalseValue.

Definition ScalarInteger x : state * SEXP :=
  alloc_vector_int (ArrayList.from_list [x]).

Definition ScalarReal x : state * SEXP :=
  alloc_vector_real (ArrayList.from_list [x]).

Definition ScalarComplex x : state * SEXP :=
  alloc_vector_cplx (ArrayList.from_list [x]).

Definition ScalarString (x : SEXP) : result SEXP :=
  add%stack "ScalarString" in
  let%success x_type := TYPEOF x in
  ifb x_type <> CharSxp then
    result_error "The given argument is not of type ‘CharSxp’."
  else
    let (S, s) := alloc_vector_str (ArrayList.from_list [x]) in
    result_success s.

Definition isPairList s :=
  add%stack "isPairList" in
  let%success s_type := TYPEOF s in
  match s_type with
  | NilSxp
  | ListSxp
  | LangSxp
  | DotSxp =>
    result_success true
  | _ =>
    result_success false
  end.

Definition isVectorList s :=
  add%stack "isVectorList" in
  let%success s_type := TYPEOF s in
  match s_type with
  | VecSxp
  | ExprSxp =>
    result_success true
  | _ =>
    result_success false
  end.

(** The following function is actually from main/altrep.c. It has been
  placed here to solve a circular file dependency. **)

Definition ALTREP_LENGTH (S : state) (x : SEXP) : result nat :=
  unimplemented_function "ALTREP_LENGTH".

Definition XLENGTH_EX x :=
  add%stack "XLENGTH_EX" in
  let%success x_altrep := ALTREP x in
  if x_altrep then ALTREP_LENGTH x
  else STDVEC_LENGTH x.

Definition XLENGTH := XLENGTH_EX.

Definition LENGTH_EX (x : SEXP) :=
  add%stack "LENGTH_EX" in
  ifb x = R_NilValue then
    result_success 0
  else XLENGTH x.

Definition LENGTH := LENGTH_EX.

Definition xlength s :=
  add%stack "xlength" in
  let%success s_type := TYPEOF s in
  match s_type with
  | NilSxp =>
    result_success 0
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | CharSxp
  | VecSxp
  | ExprSxp
  | RawSxp =>
    LENGTH s
  | ListSxp
  | LangSxp
  | DotSxp =>
    do%success (s, i) := (s, 0)
    whileb s <> NULL /\ s <> R_NilValue do
      read%list _, s_cdr, _ := s in
      result_success (s_cdr, 1 + i) using S, runs in
    result_success i
  | EnvSxp =>
    unimplemented_function "Rf_envlength"
  | _ =>
    result_success 1
  end.
(** Named [length] in the C source file. **)
Definition R_length s :=
  add%stack "R_length" in
  let%success s_type := TYPEOF s in
  match s_type with
  | NilSxp => result_success 0
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | CharSxp
  | VecSxp
  | ExprSxp
  | RawSxp =>
    read%defined s_ := s in
    let%defined l := get_VecSxp_length s_ in
    result_success l
  | ListSxp
  | LangSxp
  | DotSxp =>
    do%success (s, i) := (s, 0)
    whileb s <> NULL /\ s <> R_NilValue do
      read%list _, s_cdr, _ := s in
      result_success (s_cdr, 1 + i) using S, runs in
    result_success i
  | EnvSxp =>
    unimplemented_function "Rf_envlength"
  | _ =>
    result_success 1
  end.

Definition inherits s name :=
  add%stack "inherits" in
  read%defined s_ := s in
  if obj s_ then
    let%success klass := runs_getAttrib runs s R_ClassSymbol in
    read%VectorPointer klass_vector := klass in
    do%success b := false
    for str in%array VecSxp_data klass_vector do
      if b then result_success true
      else
        let%success str_ := CHAR str in
        result_success (decide (str_ = name)) in
    result_success b
  else result_success false.

Definition isVectorAtomic s :=
  add%stack "isVectorAtomic" in
  let%success s_type := TYPEOF s in
  match s_type with
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | RawSxp => result_success true
  | _ => result_success false
  end.

Definition isInteger s :=
  add%stack "isInteger" in
  let%success s_type := TYPEOF s in
  let%success inh := inherits s "factor" in
  result_success (decide (s_type = IntSxp /\ ~ inh)).

Definition isFunction s :=
  add%stack "isFunction" in
    let%success s_type := TYPEOF s in
    result_success (decide (s_type = CloSxp \/ s_type = BuiltinSxp \/ s_type = SpecialSxp)).

Definition isList s :=
  add%stack "isList" in
  let%success s_type := TYPEOF s in
  result_success (decide (s = R_NilValue \/ s_type = ListSxp)).

Definition isLanguage s :=
  add%stack "isLanguage" in
  let%success s_type := TYPEOF s in
  result_success (decide (s = R_NilValue \/ s_type = LangSxp)).

Definition isNumeric s :=
  add%stack "isNumeric" in
  let%success s_type := TYPEOF s in
  match s_type with
  | IntSxp =>
    let%success inh := inherits s "factor" in
    result_success (negb inh)
  | LglSxp
  | RealSxp =>
    result_success true
  | _ => result_success false
  end.

Definition isNumber s :=
  add%stack "isNumber" in
  let%success s_type := TYPEOF s in
  match s_type with
  | IntSxp =>
    let%success inh := inherits s "factor" in
    result_success (negb inh)
  | LglSxp
  | RealSxp
  | CplxSxp =>
    result_success true
  | _ => result_success false
  end.

Definition isFrame s :=
  add%stack "isFrame" in
  if%success OBJECT s then
    let%success klass := runs_getAttrib runs s R_ClassSymbol in
    let%success klass_len := R_length klass in
    do%exit
    for i from 0 to klass_len - 1 do
      let%success str := STRING_ELT klass i in
      let%success str_ := CHAR str in
      ifb str_ = "data.frame"%string then
        result_rreturn true
      else result_rskip in
    result_success false
  else result_success false.

Definition isNewList s :=
  add%stack "isNewList" in
  let%success s_type := TYPEOF s in
  result_success (decide (s = R_NilValue \/ s_type = VecSxp)).

Definition SCALAR_LVAL x :=
  add%stack "SCALAR_LVAL" in
  read%Logical r := x at 0 in
  result_success r.

Definition SCALAR_IVAL x :=
  add%stack "SCALAR_IVAL" in
  read%Integer r := x at 0 in
  result_success r.

Definition SCALAR_DVAL x :=
  add%stack "SCALAR_DVAL" in
  read%Real r := x at 0 in
  result_success r.

Definition SET_SCALAR_LVAL x v :=
  add%stack "SET_SCALAR_LVAL" in
  write%Logical x at 0 := v in
  result_skip.

Definition SET_SCALAR_IVAL x v :=
  add%stack "SET_SCALAR_IVAL" in
  write%Integer x at 0 := v in
  result_skip.

Definition SET_SCALAR_DVAL x v :=
  add%stack "SET_SCALAR_DVAL" in
  write%Real x at 0 := v in
  result_skip.


Definition lcons car cdr :=
  add%stack "lcons" in
  let (S, e) := CONS globals car cdr in
  set%type e := LangSxp in
  result_success e.

Definition LCONS := lcons.

Definition list1 s :=
  CONS globals s R_NilValue.

Definition list2 s t :=
  let (S, l) := list1 t in
  CONS globals s l.

Definition list3 s t u :=
  let (S, l) := list2 t u in
  CONS globals s l.

Definition list4 s t u v :=
  let (S, l) := list3 t u v in
  CONS globals s l.

Definition list5 s t u v w :=
  let (S, l) := list4 t u v w in
  CONS globals s l.

Definition list6 s t u v w x :=
  let (S, l) := list5 t u v w x in
  CONS globals s l.

Definition lang1 s :=
  add%stack "lang1" in
  lcons s R_NilValue.

Definition lang2 s t :=
  add%stack "lang2" in
  let (S, l) := list1 t in
  lcons s l.

Definition lang3 s t u :=
  add%stack "lang3" in
  let (S, l) := list2 t u in
  lcons s l.

Definition lang4 s t u v :=
  add%stack "lang4" in
  let (S, l) := list3 t u v in
  lcons s l.

Definition lang5 s t u v w :=
  add%stack "lang5" in
  let (S, l) := list4 t u v w in
  lcons s l.

Definition lang6 s t u v w x :=
  add%stack "lang6" in
  let (S, l) := list5 t u v w x in
  lcons s l.


Definition ALTLOGICAL_ELT x i :=
  add%stack "ALTLOGICAL_ELT" in
  read%Logical x_i := x at i in
  result_success x_i.

Definition LOGICAL_ELT x i :=
  add%stack "LOGICAL_ELT" in
  read%defined x_ := x in
  ifb alt x_ then ALTLOGICAL_ELT x i
  else
    read%Logical x_i := x at i in
    result_success x_i.

Definition ALTINTEGER_ELT (S : state) (x : SEXP) (i : nat) : result int :=
  unimplemented_function "ALTINTEGER_ELT".

Definition INTEGER_ELT x i :=
  add%stack "INTEGER_ELT" in
  read%defined x_ := x in
  ifb alt x_ then ALTINTEGER_ELT x i
  else
    read%Integer x_i := x at i in
    result_success x_i.

Definition ALTREAL_ELT (S : state) (x : SEXP) (i : nat) : result double :=
  unimplemented_function "ALTREAL_ELT".

Definition REAL_ELT x i :=
  add%stack "REAL_ELT" in
  read%defined x_ := x in
  ifb alt x_ then ALTREAL_ELT x i
  else
    read%Real x_i := x at i in
    result_success x_i.

Definition ALTCOMPLEX_ELT (S : state) (x : SEXP) (i : nat) : result Rcomplex :=
  unimplemented_function "ALTCOMPLEX_ELT".

Definition COMPLEX_ELT x i :=
  add%stack "COMPLEX_ELT" in
  read%defined x_ := x in
  ifb alt x_ then ALTCOMPLEX_ELT x i
  else
    read%Complex x_i := x at i in
    result_success x_i.

Definition ALTRAW_ELT x i :=
  add%stack "ALTRAW_ELT" in
  read%Pointer x_i := x at i in
  result_success x_i.

Definition RAW_ELT x i :=
  add%stack "RAW_ELT" in
  read%defined x_ := x in
  ifb alt x_ then ALTRAW_ELT x i
  else
    read%Pointer x_i := x at i in
    result_success x_i.

(** The following function is actually from main/altrep.c. It has been
  placed here to solve a circular file dependency. **)

Definition ALTREP_TRUELENGTH (x : SEXP) :=
  add%stack "ALTREP_TRUELENGTH" in
  result_success 0.

Definition XTRUELENGTH x :=
  add%stack "XTRUELENGTH" in
  if%success ALTREP x then
    ALTREP_TRUELENGTH x
  else STDVEC_TRUELENGTH x.

End Parameterised.

