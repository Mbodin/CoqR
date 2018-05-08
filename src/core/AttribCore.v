(** ** attrib.c **)

(** The function names of this section correspond to the function names
  in the file main/attrib.c. **)

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
Require Import Rinlinedfuns.
Require Import Duplicate.
Require Import Sysutils.
Require Import Altrep.
Require Import CoerceCore.

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

(** The following two functions are actually from main/Rinlinedfuns.c. They
  are placed here to solve a circular file dependency. **)

Definition R_FixupRHS S x y :=
  add%stack "R_FixupRHS" in
  let%success y_named := NAMED S y using S in
  ifb y <> R_NilValue /\ y_named <> named_temporary then
    if%success R_cycle_detected globals runs S x y using S then
      duplicate globals runs S y
    else
      map%pointer y with set_named_plural using S in
      result_success S y
  else result_success S y.

Definition isVectorizable S (s : SEXP) :=
  add%stack "isVectorizable" in
  ifb s = R_NilValue then
    result_success S true
  else if%success isNewList globals S s using S then
    let%success n := XLENGTH S s using S in
    do%exit
    for i from 0 to n - 1 do
      let%success s_i := VECTOR_ELT S s i using S in
      let%success s_i_iv := isVector S s_i using S in
      let%success s_i_len := LENGTH globals S s_i using S in
      ifb ~ s_i_iv \/ s_i_len > 1 then
        result_rreturn S false
      else result_rskip S using S in
    result_success S true
  else if%success isList globals S s using S then
    fold%return
    along s
    as s_car, _ do
      let%success s_car_iv := isVector S s_car using S in
      let%success s_car_len := LENGTH globals S s_car using S in
      ifb ~ s_car_iv \/ s_car_len > 1 then
        result_rreturn S false
      else result_rskip S using S, runs, globals in
    result_success S true
  else result_success S false.




Definition isOneDimensionalArray S vec :=
  add%stack "isOneDimensionalArray" in
  let%success ivec := isVector S vec using S in
  let%success ilist := isList globals S vec using S in
  let%success ilang := isLanguage globals S vec using S in
  ifb ivec \/ ilist \/ ilang then
    let%success s := runs_getAttrib runs S vec R_DimSymbol using S in
    let%success s_type := TYPEOF S s using S in
    ifb s_type = IntSxp then
      let%success s_len := R_length globals runs S s using S in
      ifb s_len = 1 then result_success S true
      else result_success S false
    else result_success S false
  else result_success S false.

Definition getAttrib0 S (vec name : SEXP) :=
  add%stack "getAttrib0" in
  run%exit
    ifb name = R_NamesSymbol then
      run%return
        if%success isOneDimensionalArray S vec using S then
          let%success s := runs_getAttrib runs S vec R_DimNamesSymbol using S in
          let%success s_null := isNull S s using S in
          if negb s_null then
            read%Pointer s_0 := s at 0 using S in
            run%success MARK_NOT_MUTABLE S s_0 using S in
            result_rreturn S s_0
          else result_rskip S
        else result_rskip S using S in
      let%success vec_list := isList globals S vec using S in
      let%success vec_lang := isLanguage globals S vec using S in
      ifb vec_list \/ vec_lang then
        let%success len := R_length globals runs S vec using S in
        let%success s := allocVector globals S StrSxp len using S in
        fold%success (i, any) := (0, false)
        along vec
        as _, vec_tag do
          let%success any :=
            ifb vec_tag = R_NilValue then
              run%success SET_STRING_ELT S s i R_BlankString using S in
              result_success S any
            else if%success isSymbol S vec_tag using S then
              let%success vec_name := PRINTNAME S vec_tag using S in
              run%success SET_STRING_ELT S s i vec_name using S in
              result_success S true
            else result_error S "Invalid type for TAG." using S in
          result_success S (1 + i, any) using S, runs, globals in
        if any then
          let%success s_null := isNull S s using S in
          run%success
            if negb s_null then
              MARK_NOT_MUTABLE S s
            else result_skip S using S in
          result_rreturn S s
        else result_rreturn S (R_NilValue : SEXP)
      else result_rskip S
    else result_rskip S using S in
  let%success vec_attr := ATTRIB S vec using S in
  fold%return
  along vec_attr
  as s_car, s_tag do
    ifb s_tag = name then
      let%success s_car_type := TYPEOF S s_car using S in
      ifb name = R_DimNamesSymbol /\ s_car_type = ListSxp then
        result_error S "Old list is no longer allowed for dimnames attributes."
      else
        run%success MARK_NOT_MUTABLE S s_car using S in
        result_rreturn S s_car
    else result_rskip S using S, runs, globals in
  result_success S (R_NilValue : SEXP).

Definition getAttrib S (vec name : SEXP) :=
  add%stack "getAttrib" in
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "Can not have attributes on a CharSxp."
  else
    let%success vec_attr := ATTRIB S vec using S in
    ifb vec_attr = R_NilValue /\ ~ (vec_type  = ListSxp \/ vec_type  = LangSxp) then
      result_success S (R_NilValue : SEXP)
    else
      let%success name :=
        if%success isString S name using S then
          let%success name_0 := STRING_ELT S name 0 using S in
          let%success name_sym := installTrChar globals runs S name_0 using S in
          result_success S name_sym
        else result_success S name using S in
      ifb name = R_RowNamesSymbol then
        let%success s := getAttrib0 S vec name using S in
        let%success s_in := isInteger globals runs S s using S in
        let%success s_len := LENGTH globals S s using S in
        ifb s_in /\ s_len = 2 then
          read%Integer s_0 := s at 0 using S in
          ifb s_0 = NA_INTEGER then
            read%Integer s_1 := s at 1 using S in
            let n := abs s_1 in
            ifb n > 0 then
              R_compact_intrange globals S 1 n
            else allocVector globals S IntSxp 0
          else result_success S s
        else result_success S s
      else getAttrib0 S vec name.

Definition installAttrib S vec name val :=
  add%stack "installAttrib" in
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "Cannot set attribute on a CharSxp."
  else ifb vec_type = SymSxp then
    result_error S "Cannot set attribute on a symbol."
  else
    let%success vec_attr := ATTRIB S vec using S in
    fold%return t := R_NilValue : SEXP
    along vec_attr
    as s, _, s_list do
      ifb list_tagval s_list = name then
        set%car s := val using S in
        result_rreturn S val
      else result_rsuccess S s using S, runs, globals in
    let (S, s) := CONS globals S val R_NilValue in
    set%tag s := name using S in
    run%success
      ifb vec_attr = R_NilValue then
        run%success SET_ATTRIB S vec s using S in
        result_skip S
      else
        set%cdr t := s using S in
        result_skip S using S in
    result_success S val.

Definition stripAttrib S (tag lst : SEXP) :=
  add%stack "stripAttrib" in
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

Definition removeAttrib S (vec name : SEXP) :=
  add%stack "removeAttrib" in
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "Cannot set attribute on a CharSxp."
  else
    let%success vec_pl := isPairList S vec using S in
    ifb name = R_NamesSymbol /\ vec_pl then
      fold%success
      along vec
      as t, _, _ do
        set%tag t := R_NilValue using S in
        result_skip S
      using S, runs, globals in
      result_success S (R_NilValue : SEXP)
    else
      run%success
        ifb name = R_DimSymbol then
          let%success r :=
            let%success vec_attr := ATTRIB S vec using S in
            stripAttrib S R_DimNamesSymbol vec_attr using S in
          run%success SET_ATTRIB S vec r using S in
          result_skip S
        else result_skip S using S in
      let%success r :=
        let%success vec_attr := ATTRIB S vec using S in
        stripAttrib S name vec_attr using S in
      run%success SET_ATTRIB S vec r using S in
      run%success
        ifb name = R_ClassSymbol then
          set%obj vec := false using S in
          result_skip S
        else result_skip S using S in
      result_success S (R_NilValue : SEXP).

Definition checkNames S x s :=
  add%stack "checkNames" in
  let%success x_vec := isVector S x using S in
  let%success x_list := isList globals S x using S in
  let%success x_lang := isLanguage globals S x using S in
  ifb x_vec \/ x_list \/ x_lang then
    let%success s_vec := isVector S s using S in
    let%success s_list := isList globals S s using S in
    ifb ~ s_vec /\ ~ s_list then
      result_error S "Invalid type for ‘names’: must be a vector."
    else
      let%success x_len := xlength globals runs S x using S in
      let%success s_len := xlength globals runs S s using S in
      ifb x_len <> x_len then
        result_error S "‘names’ attribute must be the same length as the vector."
      else result_skip S
  else if%success IS_S4_OBJECT S x using S then
    result_skip S
  else result_error S "‘names’ applied to a non-vector.".

Definition classgets S (vec klass : SEXP) :=
  add%stack "classgets" in
  let%success klass_null := isNull S klass using S in
  let%success klass_str := isString S klass using S in
  ifb klass_null \/ klass_str then
    let%success ncl := R_length globals runs S klass using S in
    ifb ncl <= 0 then
      let%success vec_attr := ATTRIB S vec using S in
      let%success sa := stripAttrib S R_ClassSymbol vec_attr using S in
      run%success SET_ATTRIB S vec sa using S in
      run%success SET_OBJECT S vec false using S in
      result_success S (R_NilValue : SEXP)
    else
      ifb vec = R_NilValue then
        result_error S "Attempt to set an attribute on NULL."
      else
        do%break isfactor := false
        for i from 0 to ncl - 1 do
          let%success klass_i := STRING_ELT S klass i using S in
          let%success klass_i_str := CHAR S klass_i using S in
          ifb klass_i_str = "factor"%string then
            result_rreturn S true
          else result_rsuccess S isfactor using S in
        let%success vec_type := TYPEOF S vec using S in
        ifb isfactor /\ vec_type <> IntSxp then
          result_error S "Adding class ‘factor’ to an invalid object."
        else
          run%success installAttrib S vec R_ClassSymbol klass using S in
          run%success SET_OBJECT S vec true using S in
          result_success S (R_NilValue : SEXP)
  else
    result_error S "Attempt to set invalid ‘class’ attribute.".

Definition namesgets S (vec val : SEXP) :=
  add%stack "namesgets" in
  let%success val :=
    if%success isList globals S val using S then
      let%success val_vec := isVectorizable S val using S in
      if negb val_vec then
        result_error S "Incompatible ‘names’ argument."
      else
        let%success vec_len := R_length globals runs S vec using S in
        let%success rval := allocVector globals S StrSxp vec_len using S in
        do%success (i, tval) := (0, val)
        whileb i < vec_len /\ rval <> R_NilValue do
          read%list tval_car, tval_cdr, _ := tval using S in
          let%success s := coerceVector globals runs S tval_car StrSxp using S in
          let%success s_0 := STRING_ELT S s 0 using S in
          run%success SET_STRING_ELT S rval i s_0 using S in
          result_success S (1 + i, tval_cdr) using S, runs in
        result_success S rval
    else coerceVector globals runs S val StrSxp using S in
  let%success val_len := xlength globals runs S val using S in
  let%success vec_len := xlength globals runs S vec using S in
  let%success val :=
    ifb val_len < vec_len then
      unimplemented_function "xlengthgets"
    else result_success S val using S in
  run%success checkNames S vec val using S in
  if%success isOneDimensionalArray S vec using S then
    let (S, val) := CONS globals S val R_NilValue in
    run%success runs_setAttrib runs S vec R_DimNamesSymbol val using S in
    result_success S vec
  else
    run%success
      let%success vec_list := isList globals S vec using S in
      let%success vec_lang := isLanguage globals S vec using S in
      ifb vec_list \/ vec_lang then
        fold%success i := 0
        along vec
        as s, _, _ do
          run%success
            let%success val_i := STRING_ELT S val i using S in
            let%success val_i_char := CHAR S val_i using S in
            ifb val_i <> R_NilValue /\ val_i <> R_NaString /\ String.length val_i_char > 0 then
              let%success ins := installTrChar globals runs S val_i using S in
              set%tag s := ins using S in
              result_skip S
            else
              set%tag s := R_NilValue using S in
              result_skip S using S in
          result_success S (1 + i) using S, runs, globals in
        result_skip S
      else
        let%success vec_vec := isVector S vec using S in
        let%success vec_S4 := IS_S4_OBJECT S vec using S in
        ifb vec_vec \/ vec_S4 then
          run%success installAttrib S vec R_NamesSymbol val using S in
          result_skip S
        else result_error S "Invalid type to set ‘names’ attribute." using S in
    result_success S vec.

Definition dimgets S (vec val : SEXP) :=
  add%stack "dimgets" in
  let%success vec_vec := isVector S vec using S in
  let%success vec_list := isList globals S vec using S in
  ifb ~ vec_vec /\ ~ vec_list then
    result_error S "Invalid first argument."
  else
    let%success val_vec := isVector S val using S in
    let%success val_list := isList globals S val using S in
    ifb ~ val_vec /\ ~ val_list then
      result_error S "Invalid second argument."
    else
      let%success val := coerceVector globals runs S val IntSxp using S in
      let%success len := xlength globals runs S vec using S in
      let%success ndim := R_length globals runs S val using S in
      ifb ndim = 0 then
        result_error S "Length-0 dimension vector is invalid."
      else
        do%success total := 1 : int
        for i from 0 to ndim - 1 do
          read%Integer val_i := val at i using S in
          ifb val_i = NA_INTEGER then
            result_error S "The dims contain missing values."
          else ifb val_i < 0 then
            result_error S "The dims contain negative values."
          else result_success S (total * val_i)%Z using S in
        ifb total <> len then
          result_error S "dims do not match the length of the object."
        else
          run%success removeAttrib S vec R_DimNamesSymbol using S in
          run%success installAttrib S vec R_DimSymbol val using S in
          run%success MARK_NOT_MUTABLE S val using S in
          result_success S vec.

Definition setAttrib S (vec name val : SEXP) :=
  add%stack "setAttrib" in
  let%success name :=
    if%success isString S name using S then
      let%success str := STRING_ELT S name 0 using S in
      installTrChar globals runs S str
    else result_success S name using S in
  ifb val = R_NilValue then
    removeAttrib S vec name
  else
    ifb vec = R_NilValue then
      result_error S "Attempt to set an attribute on NULL."
    else
      let%success val :=
        if%success MAYBE_REFERENCED S val using S then
          R_FixupRHS S vec val
        else result_success S val using S in
      ifb name = R_NamesSymbol then
        namesgets S vec val
      else ifb name = R_DimSymbol then
        dimgets S vec val
      else ifb name = R_DimNamesSymbol then
        unimplemented_function "dimnamesgets"
      else ifb name = R_ClassSymbol then
        classgets S vec val
      else ifb name = R_TspSymbol then
        unimplemented_function "tspgets"
      else ifb name = R_CommentSymbol then
        unimplemented_function "commentgets"
      else ifb name = R_RowNamesSymbol then
        unimplemented_function "row_names_gets"
      else installAttrib S vec name val.

Definition copyMostAttrib S (inp ans : SEXP) :=
  add%stack "copyMostAttrib" in
  ifb ans = R_NilValue then
    result_error S "Attempt to set an attribute on NULL."
  else
    let%success inp_attr := ATTRIB S inp using S in
    fold%success
    along inp_attr
    as s_car, s_tag do
      ifb s_tag <> R_NamesSymbol
          /\ s_tag <> R_DimSymbol
          /\ s_tag <> R_DimNamesSymbol then
        run%success installAttrib S ans s_tag s_car using S in
        result_skip S
      else result_skip S using S, runs, globals in
    if%success OBJECT S inp using S then
      SET_OBJECT S ans true in
    if%success IS_S4_OBJECT S inp using S then
      SET_S4_OBJECT S ans
    else UNSET_S4_OBJECT S ans.

End Parameterised.
