(** Core.CAttrib.
  The function names in this file correspond to the function names
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
Require Import Double.
Require Import Loops.
Require Import Conflicts.
Require Import CRinternals.
Require Import CMemory.
Require Import CRinlinedfuns.
Require Import CDuplicate.
Require Import CSysutils.
Require Import CAltrep.
Require Import CCoerce.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition isOneDimensionalArray vec :=
  add%stack "isOneDimensionalArray" in
  let%success ivec := isVector vec in
  let%success ilist := isList globals vec in
  let%success ilang := isLanguage globals vec in
  ifb ivec \/ ilist \/ ilang then
    let%success s := runs_getAttrib runs vec R_DimSymbol in
    let%success s_type := TYPEOF s in
    ifb s_type = IntSxp then
      let%success s_len := R_length globals runs s in
      ifb s_len = 1 then result_success true
      else result_success false
    else result_success false
  else result_success false.

Definition getAttrib0 (vec name : SEXP) :=
  add%stack "getAttrib0" in
  run%exit
    ifb name = R_NamesSymbol then
      run%return
        if%success isOneDimensionalArray vec then
          let%success s := runs_getAttrib runs vec R_DimNamesSymbol in
          let%success s_null := isNull s in
          if negb s_null then
            read%Pointer s_0 := s at 0 in
            run%success MARK_NOT_MUTABLE s_0 in
            result_rreturn s_0
          else result_rskip
        else result_rskip in
      let%success vec_list := isList globals vec in
      let%success vec_lang := isLanguage globals vec in
      ifb vec_list \/ vec_lang then
        let%success len := R_length globals runs vec in
        let%success s := allocVector globals StrSxp len in
        fold%success (i, any) := (0, false)
        along vec
        as _, vec_tag do
          let%success any :=
            ifb vec_tag = R_NilValue then
              run%success SET_STRING_ELT s i R_BlankString in
              result_success any
            else if%success isSymbol vec_tag then
              let%success vec_name := PRINTNAME vec_tag in
              run%success SET_STRING_ELT s i vec_name in
              result_success true
            else result_error "Invalid type for TAG." in
          result_success (1 + i, any) using runs in
        if any then
          let%success s_null := isNull s in
          run%success
            if negb s_null then
              MARK_NOT_MUTABLE s
            else result_skip in
          result_rreturn s
        else result_rreturn (R_NilValue : SEXP)
      else result_rskip
    else result_rskip in
  let%success vec_attr := ATTRIB vec in
  fold%return
  along vec_attr
  as s_car, s_tag do
    ifb s_tag = name then
      let%success s_car_type := TYPEOF s_car in
      ifb name = R_DimNamesSymbol /\ s_car_type = ListSxp then
        result_error "Old list is no longer allowed for dimnames attributes."
      else
        run%success MARK_NOT_MUTABLE s_car in
        result_rreturn s_car
    else result_rskip using runs in
  result_success (R_NilValue : SEXP).

Definition getAttrib (vec name : SEXP) :=
  add%stack "getAttrib" in
  let%success vec_type := TYPEOF vec in
  ifb vec_type = CharSxp then
    result_error "Can not have attributes on a CharSxp."
  else
    let%success vec_attr := ATTRIB vec in
    ifb vec_attr = R_NilValue /\ ~ (vec_type  = ListSxp \/ vec_type  = LangSxp) then
      result_success (R_NilValue : SEXP)
    else
      let%success name :=
        if%success isString name then
          let%success name_0 := STRING_ELT name 0 in
          let%success name_sym := installTrChar globals runs name_0 in
          result_success name_sym
        else result_success name in
      ifb name = R_RowNamesSymbol then
        let%success s := getAttrib0 vec name in
        let%success s_in := isInteger globals runs s in
        let%success s_len := LENGTH globals s in
        ifb s_in /\ s_len = 2 then
          read%Integer s_0 := s at 0 in
          ifb s_0 = NA_INTEGER then
            read%Integer s_1 := s at 1 in
            let n := abs s_1 in
            ifb n > 0 then
              R_compact_intrange globals 1 n
            else allocVector globals IntSxp 0
          else result_success s
        else result_success s
      else getAttrib0 vec name.

Definition installAttrib vec name val :=
  add%stack "installAttrib" in
  let%success vec_type := TYPEOF vec in
  ifb vec_type = CharSxp then
    result_error "Cannot set attribute on a CharSxp."
  else ifb vec_type = SymSxp then
    result_error "Cannot set attribute on a symbol."
  else
    let%success vec_attr := ATTRIB vec in
    fold%return t := R_NilValue : SEXP
    along vec_attr
    as s, _, s_list do
      ifb list_tagval s_list = name then
        set%car s := val in
        result_rreturn val
      else result_rsuccess s using runs in
    let%success s := CONS globals val R_NilValue in
    set%tag s := name in
    run%success
      ifb vec_attr = R_NilValue then
        run%success SET_ATTRIB vec s in
        result_skip
      else
        set%cdr t := s in
        result_skip in
    result_success val.

Definition stripAttrib (tag lst : SEXP) :=
  add%stack "stripAttrib" in
  ifb lst = R_NilValue then
    result_success lst
  else
    read%list _, lst_cdr, lst_tag := lst in
    ifb tag = lst_tag then
      runs_stripAttrib runs tag lst_cdr
    else
      let%success r :=
        runs_stripAttrib runs tag lst_cdr in
      set%cdr lst := r in
      result_success lst.

Definition removeAttrib (vec name : SEXP) :=
  add%stack "removeAttrib" in
  let%success vec_type := TYPEOF vec in
  ifb vec_type = CharSxp then
    result_error "Cannot set attribute on a CharSxp."
  else
    let%success vec_pl := isPairList vec in
    ifb name = R_NamesSymbol /\ vec_pl then
      fold%success
      along vec
      as t, _, _ do
        set%tag t := R_NilValue in
        result_skip
      using runs in
      result_success (R_NilValue : SEXP)
    else
      run%success
        ifb name = R_DimSymbol then
          let%success r :=
            let%success vec_attr := ATTRIB vec in
            stripAttrib R_DimNamesSymbol vec_attr in
          run%success SET_ATTRIB vec r in
          result_skip
        else result_skip in
      let%success r :=
        let%success vec_attr := ATTRIB vec in
        stripAttrib name vec_attr in
      run%success SET_ATTRIB vec r in
      run%success
        ifb name = R_ClassSymbol then
          set%obj vec := false in
          result_skip
        else result_skip in
      result_success (R_NilValue : SEXP).

Definition checkNames x s :=
  add%stack "checkNames" in
  let%success x_vec := isVector x in
  let%success x_list := isList globals x in
  let%success x_lang := isLanguage globals x in
  ifb x_vec \/ x_list \/ x_lang then
    let%success s_vec := isVector s in
    let%success s_list := isList globals s in
    ifb ~ s_vec /\ ~ s_list then
      result_error "Invalid type for ‘names’: must be a vector."
    else
      let%success x_len := xlength globals runs x in
      let%success s_len := xlength globals runs s in
      ifb x_len <> x_len then
        result_error "‘names’ attribute must be the same length as the vector."
      else result_skip
  else if%success IS_S4_OBJECT x then
    result_skip
  else result_error "‘names’ applied to a non-vector.".

Definition classgets (vec klass : SEXP) :=
  add%stack "classgets" in
  let%success klass_null := isNull klass in
  let%success klass_str := isString klass in
  ifb klass_null \/ klass_str then
    let%success ncl := R_length globals runs klass in
    ifb ncl <= 0 then
      let%success vec_attr := ATTRIB vec in
      let%success sa := stripAttrib R_ClassSymbol vec_attr in
      run%success SET_ATTRIB vec sa in
      run%success SET_OBJECT vec false in
      result_success (R_NilValue : SEXP)
    else
      ifb vec = R_NilValue then
        result_error "Attempt to set an attribute on NULL."
      else
        do%break isfactor := false
        for i from 0 to ncl - 1 do
          let%success klass_i := STRING_ELT klass i in
          let%success klass_i_str := CHAR klass_i in
          ifb klass_i_str = "factor"%string then
            result_rreturn true
          else result_rsuccess isfactor in
        let%success vec_type := TYPEOF vec in
        ifb isfactor /\ vec_type <> IntSxp then
          result_error "Adding class ‘factor’ to an invalid object."
        else
          run%success installAttrib vec R_ClassSymbol klass in
          run%success SET_OBJECT vec true in
          result_success (R_NilValue : SEXP)
  else
    result_error "Attempt to set invalid ‘class’ attribute.".

Definition namesgets (vec val : SEXP) :=
  add%stack "namesgets" in
  let%success val :=
    if%success isList globals val then
      let%success val_vec := isVectorizable globals runs val in
      if negb val_vec then
        result_error "Incompatible ‘names’ argument."
      else
        let%success vec_len := R_length globals runs vec in
        let%success rval := allocVector globals StrSxp vec_len in
        do%success (i, tval) := (0, val)
        whileb i < vec_len /\ rval <> R_NilValue do
          read%list tval_car, tval_cdr, _ := tval in
          let%success s := coerceVector globals runs tval_car StrSxp in
          let%success s_0 := STRING_ELT s 0 in
          run%success SET_STRING_ELT rval i s_0 in
          result_success (1 + i, tval_cdr) using runs in
        result_success rval
    else coerceVector globals runs val StrSxp in
  let%success val_len := xlength globals runs val in
  let%success vec_len := xlength globals runs vec in
  let%success val :=
    ifb val_len < vec_len then
      unimplemented_function "xlengthgets"
    else result_success val in
  run%success checkNames vec val in
  if%success isOneDimensionalArray vec then
    let%success val := CONS globals val R_NilValue in
    run%success runs_setAttrib runs vec R_DimNamesSymbol val in
    result_success vec
  else
    run%success
      let%success vec_list := isList globals vec in
      let%success vec_lang := isLanguage globals vec in
      ifb vec_list \/ vec_lang then
        fold%success i := 0
        along vec
        as s, _, _ do
          run%success
            let%success val_i := STRING_ELT val i in
            let%success val_i_char := CHAR val_i in
            ifb val_i <> R_NilValue /\ val_i <> R_NaString /\ String.length val_i_char > 0 then
              let%success ins := installTrChar globals runs val_i in
              set%tag s := ins in
              result_skip
            else
              set%tag s := R_NilValue in
              result_skip in
          result_success (1 + i) using runs in
        result_skip
      else
        let%success vec_vec := isVector vec in
        let%success vec_S4 := IS_S4_OBJECT vec in
        ifb vec_vec \/ vec_S4 then
          run%success installAttrib vec R_NamesSymbol val in
          result_skip
        else result_error "Invalid type to set ‘names’ attribute." in
    result_success vec.

Definition dimgets (vec val : SEXP) :=
  add%stack "dimgets" in
  let%success vec_vec := isVector vec in
  let%success vec_list := isList globals vec in
  ifb ~ vec_vec /\ ~ vec_list then
    result_error "Invalid first argument."
  else
    let%success val_vec := isVector val in
    let%success val_list := isList globals val in
    ifb ~ val_vec /\ ~ val_list then
      result_error "Invalid second argument."
    else
      let%success val := coerceVector globals runs val IntSxp in
      let%success len := xlength globals runs vec in
      let%success ndim := R_length globals runs val in
      ifb ndim = 0 then
        result_error "Length-0 dimension vector is invalid."
      else
        do%success total := 1 : int
        for i from 0 to ndim - 1 do
          read%Integer val_i := val at i in
          ifb val_i = NA_INTEGER then
            result_error "The dims contain missing values."
          else ifb val_i < 0 then
            result_error "The dims contain negative values."
          else result_success (total * val_i)%Z in
        ifb total <> len then
          result_error "dims do not match the length of the object."
        else
          run%success removeAttrib vec R_DimNamesSymbol in
          run%success installAttrib vec R_DimSymbol val in
          run%success MARK_NOT_MUTABLE val in
          result_success vec.

Definition setAttrib (vec name val : SEXP) :=
  add%stack "setAttrib" in
  let%success name :=
    if%success isString name then
      let%success str := STRING_ELT name 0 in
      installTrChar globals runs str
    else result_success name in
  ifb val = R_NilValue then
    removeAttrib vec name
  else
    ifb vec = R_NilValue then
      result_error "Attempt to set an attribute on NULL."
    else
      let%success val :=
        if%success MAYBE_REFERENCED val then
          R_FixupRHS globals runs vec val
        else result_success val in
      ifb name = R_NamesSymbol then
        namesgets vec val
      else ifb name = R_DimSymbol then
        dimgets vec val
      else ifb name = R_DimNamesSymbol then
        unimplemented_function "dimnamesgets"
      else ifb name = R_ClassSymbol then
        classgets vec val
      else ifb name = R_TspSymbol then
        unimplemented_function "tspgets"
      else ifb name = R_CommentSymbol then
        unimplemented_function "commentgets"
      else ifb name = R_RowNamesSymbol then
        unimplemented_function "row_names_gets"
      else installAttrib vec name val.

Definition copyMostAttrib (inp ans : SEXP) :=
  add%stack "copyMostAttrib" in
  ifb ans = R_NilValue then
    result_error "Attempt to set an attribute on NULL."
  else
    let%success inp_attr := ATTRIB inp in
    fold%success
    along inp_attr
    as s_car, s_tag do
      ifb s_tag <> R_NamesSymbol
          /\ s_tag <> R_DimSymbol
          /\ s_tag <> R_DimNamesSymbol then
        run%success installAttrib ans s_tag s_car in
        result_skip
      else result_skip using runs in
    if%success OBJECT inp then
      SET_OBJECT ans true in
    if%success IS_S4_OBJECT inp then
      SET_S4_OBJECT ans
    else UNSET_S4_OBJECT ans.


Definition GetArrayDimnames x :=
  add%stack "GetArrayDimnames" in
  getAttrib x R_DimNamesSymbol.

End Parameterised.

