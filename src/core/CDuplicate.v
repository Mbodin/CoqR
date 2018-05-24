(** Core.CDuplicate.
  The function names in this file correspond to the function names
  in the file main/duplicate.c. **)

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
Require Import CRinternals.
Require Import CMemory.
Require Import CRinlinedfuns.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition lazy_duplicate S s :=
  add%stack "lazy_duplicate" in
  let%success s_t := TYPEOF S s using S in
  run%success
    match s_t with
    | NilSxp
    | SymSxp
    | EnvSxp
    | SpecialSxp
    | BuiltinSxp
    | ExtptrSxp
    | BcodeSxp
    | WeakrefSxp
    | CharSxp
    | PromSxp =>
      result_skip S
    | CloSxp
    | ListSxp
    | LangSxp
    | DotSxp
    | ExprSxp
    | VecSxp
    | LglSxp
    | IntSxp
    | RealSxp
    | CplxSxp
    | RawSxp
    | StrSxp
    | S4Sxp =>
      set%named s := named_plural using S in
      result_skip S
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S s.

Definition DUPLICATE_ATTRIB S vto vfrom deep :=
  add%stack "DUPLICATE_ATTRIB" in
  let%success a := ATTRIB S vfrom using S in
  ifb a <> R_NilValue then
    let%success a_duplicate := runs_duplicate1 runs S a deep using S in
    run%success SET_ATTRIB S vto a_duplicate using S in
    let%success vfrom_object := OBJECT S vfrom using S in
    run%success SET_OBJECT S vto vfrom_object using S in
    if%success IS_S4_OBJECT S vfrom using S then
      SET_S4_OBJECT S vto
    else UNSET_S4_OBJECT S vto
  else result_skip S.

Definition duplicate_child S s (deep : bool) :=
  add%stack "duplicate_child" in
  if deep then
    runs_duplicate1 runs S s true
  else lazy_duplicate S s.

Definition duplicate_list S s deep :=
  add%stack "duplicate_list" in
  fold%success val := (R_NilValue : SEXP)
  along s
  as _, _ do
    let (S, val) := CONS globals S R_NilValue val in
    result_success S val using S, runs, globals in
  fold%success vp := val
  along s
  as s, _, s_list do
    let sp_car := list_carval s_list in
    let%success sp_car_duplicate := duplicate_child S sp_car deep using S in
    set%car vp := sp_car_duplicate using S in
    set%tag vp := list_tagval s_list using S in
    run%success DUPLICATE_ATTRIB S vp s deep using S in
    read%list _, vp_cdr, _ := vp using S in
    result_success S vp_cdr using S, runs, globals in
  result_success S val.

(** The following two functions are actually from main/memory.c. They
  are placed here to solve a circular file dependency. **)

Definition SET_VECTOR_ELT S x i v :=
  add%stack "SET_VECTOR_ELT" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> VecSxp /\ x_type <> ExprSxp /\ x_type <> WeakrefSxp then
    result_error S "It can onlybe applied to a list."
  else
    let%success x_len := XLENGTH S x using S in
    ifb i < 0 \/ i >= x_len then
      result_error S "Outbound index."
    else
      write%Pointer x at i := v using S in
      result_success S v.

Definition SET_STRING_ELT S (x : SEXP) i v : result unit :=
  add%stack "SET_STRING_ELT" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> StrSxp then
    result_error S "It can only be applied to a character vector."
  else
    let%success v_type := TYPEOF S v using S in
    ifb v_type <> CharSxp then
      result_error S "The value must be a CharSxp."
    else
      let%success x_len := XLENGTH S x using S in
      ifb i < 0 \/ i >= x_len then
        result_error S "Outbound index."
      else
        write%Pointer x at i := v using S in
        result_skip S.

Definition COPY_TRUELENGTH S (vto vfrom : SEXP) :=
  add%stack "COPY_TRUELENGTH" in
  let%success vfrom_growable := IS_GROWABLE S vfrom using S in
  if negb vfrom_growable then
    let%success vfrom_len := XTRUELENGTH S vfrom using S in
    SET_TRUELENGTH S vto vfrom_len
  else result_skip S.

Definition duplicate1 S s deep :=
  add%stack "duplicate1" in
  run%exit
    if%success ALTREP S s using S then
      unimplemented_function "ALTREP_DUPLICATE_EX"
    else result_rskip S using S in
  let%success s_type := TYPEOF S s using S in
  let%exit t :=
    match s_type with
    | NilSxp
    | SymSxp
    | EnvSxp
    | SpecialSxp
    | BuiltinSxp
    | ExtptrSxp
    | BcodeSxp
    | WeakrefSxp =>
      result_rreturn S s
    | CloSxp =>
      read%clo _, s_clo := s using S in
      let t_ :=
        make_SExpRec_clo R_NilValue
          (clo_formals s_clo) (clo_body s_clo) (clo_env s_clo) in
      let (S, t) := alloc_SExp S t_ in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      (** JIT functions have been ignored here. **)
      result_rsuccess S t
    | ListSxp =>
      let%success t := duplicate_list S s deep using S in
      result_rsuccess S t
    | LangSxp =>
      let%success t := duplicate_list S s deep using S in
      set%type s := LangSxp using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      result_rsuccess S t
    | DotSxp =>
      let%success t := duplicate_list S s deep using S in
      set%type s := DotSxp using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      result_rsuccess S t
    | CharSxp =>
      result_rreturn S s
    | ExprSxp
    | VecSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector globals S s_type n using S in
      do%success
      for i from 0 to n - 1 do
        let%success s_i := VECTOR_ELT S s i using S in
        let%success s_i_duplicated := duplicate_child S s_i deep using S in
        run%success SET_VECTOR_ELT S t i s_i_duplicated using S in
        result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | LglSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector globals S s_type n using S in
      run%success
        ifb n = 1 then
          read%Logical s_0 := s at 0 using S in
          write%Logical t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorLogical s_ := s using S in
          write%VectorLogical t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | IntSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector globals S s_type n using S in
      run%success
        ifb n = 1 then
          read%Integer s_0 := s at 0 using S in
          write%Integer t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorInteger s_ := s using S in
          write%VectorInteger t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | RealSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector globals S s_type n using S in
      run%success
        ifb n = 1 then
          read%Real s_0 := s at 0 using S in
          write%Real t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorReal s_ := s using S in
          write%VectorReal t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | CplxSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector globals S s_type n using S in
      run%success
        ifb n = 1 then
          read%Complex s_0 := s at 0 using S in
          write%Complex t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorComplex s_ := s using S in
          write%VectorComplex t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | RawSxp =>
      result_not_implemented "Raw case."
    | StrSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector globals S s_type n using S in
      run%success
        ifb n = 1 then
          read%Pointer s_0 := s at 0 using S in
          write%Pointer t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorPointer s_ := s using S in
          write%VectorPointer t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | PromSxp =>
      result_rreturn S s
    | S4Sxp =>
      unimplemented_function "allocS4Object"
    | _ => result_error S "Unimplemented type."
    end using S in
  let%success t_type := TYPEOF S t using S in
  run%success
    ifb t_type = s_type then
      let%success s_obj := OBJECT S s using S in
      run%success SET_OBJECT S t s_obj using S in
      if%success IS_S4_OBJECT S s using S then
        SET_S4_OBJECT S t
      else UNSET_S4_OBJECT S t
    else result_skip S using S in
  result_success S t.

Definition duplicate S s :=
  add%stack "duplicate" in
  duplicate1 S s true.

Definition shallow_duplicate S s :=
  add%stack "shallow_duplicate" in
  duplicate1 S s false.

(** The following function is actually from main/memory.c. It has been
  placed here to solve a circular file dependency. **)
Definition SHALLOW_DUPLICATE_ATTRIB S vto vfrom :=
  add%stack "SHALLOW_DUPLICATE_ATTRIB" in
  let%success vfrom_attrib := ATTRIB S vfrom using S in
  let%success vfrom_attrib := shallow_duplicate S vfrom_attrib using S in
  run%success SET_ATTRIB S vto vfrom_attrib using S in
  let%success vfrom_obj := OBJECT S vfrom using S in
  map%pointer vto with set_obj vfrom_obj using S in
  run%success
    if%success IS_S4_OBJECT S vfrom using S then
      SET_S4_OBJECT S vto
    else UNSET_S4_OBJECT S vto using S in
  result_skip S.


Definition isVector S s :=
  add%stack "isVector" in
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

Definition isMatrix S s :=
  add%stack "isMatrix" in
  if%success isVector S s using S then
    let%success t := runs_getAttrib runs S s R_DimSymbol using S in
    let%success t_type := TYPEOF S t using S in
    ifb t_type = IntSxp then
      let%success t_len := LENGTH globals S t using S in
      ifb t_len = 2 then
        result_success S true
      else result_success S false
    else result_success S false
  else result_success S false.

Definition R_cycle_detected S s child :=
  add%stack "R_cycle_detected" in
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
      let%success child_attrib := ATTRIB S child using S in
      ifb child_attrib <> R_NilValue then
        if%success runs_R_cycle_detected runs S s child_attrib using S then
          result_rreturn S true
        else result_rskip S
      else result_rskip S using S in
    if%success isPairList S child using S then
      fold%return
      along child
      as el, _, el_list do
        let%success r :=
          runs_R_cycle_detected runs S s (list_carval el_list) using S in
        ifb s = el \/ r then
          result_rreturn S true
        else
          let%success el_attrib := ATTRIB S el using S in
          let%success r :=
            runs_R_cycle_detected runs S s el_attrib using S in
          ifb el_attrib <> R_NilValue /\ r then
            result_rreturn S true
          else result_rskip S
      using S, runs, globals in
      result_success S false
    else
      if%success isVectorList S child using S then
        read%VectorPointer child_ := child using S in
        do%let r := false
        for e in%array VecSxp_data child_ do
          if r then result_success S r
          else runs_R_cycle_detected runs S s e using S
      else result_success S false.

End Parameterised.

