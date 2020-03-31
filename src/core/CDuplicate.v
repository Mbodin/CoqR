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


Definition lazy_duplicate s :=
  add%stack "lazy_duplicate" in
  let%success s_t := TYPEOF s in
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
      result_skip
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
      set%named s := named_plural in
      result_skip
    | _ =>
      result_error "Unimplemented type."
    end in
  result_success s.

Definition DUPLICATE_ATTRIB vto vfrom deep :=
  add%stack "DUPLICATE_ATTRIB" in
  let%success a := ATTRIB vfrom in
  ifb a <> R_NilValue then
    let%success a_duplicate := runs_duplicate1 runs a deep in
    run%success SET_ATTRIB vto a_duplicate in
    let%success vfrom_object := OBJECT vfrom in
    run%success SET_OBJECT vto vfrom_object in
    if%success IS_S4_OBJECT vfrom then
      SET_S4_OBJECT vto
    else UNSET_S4_OBJECT vto
  else result_skip.

Definition duplicate_child s (deep : bool) :=
  add%stack "duplicate_child" in
  if deep then
    runs_duplicate1 runs s true
  else lazy_duplicate s.

Definition duplicate_list s deep :=
  add%stack "duplicate_list" in
  fold%success val := (R_NilValue : SEXP)
  along s
  as _, _ do
    let%success val := CONS globals R_NilValue val in
    result_success val using runs in
  fold%success vp := val
  along s
  as s, _, s_list do
    let sp_car := list_carval s_list in
    let%success sp_car_duplicate := duplicate_child sp_car deep in
    set%car vp := sp_car_duplicate in
    set%tag vp := list_tagval s_list in
    run%success DUPLICATE_ATTRIB vp s deep in
    read%list _, vp_cdr, _ := vp in
    result_success vp_cdr using runs in
  result_success val.

(** The following two functions are actually from main/memory.c. They
  are placed here to solve a circular file dependency. **)

Definition SET_VECTOR_ELT x i v :=
  add%stack "SET_VECTOR_ELT" in
  let%success x_type := TYPEOF x in
  ifb x_type <> VecSxp /\ x_type <> ExprSxp /\ x_type <> WeakrefSxp then
    result_error "It can onlybe applied to a list."
  else
    let%success x_len := XLENGTH x in
    ifb i < 0 \/ i >= x_len then
      result_error "Outbound index."
    else
      write%Pointer x at i := v in
      result_success v.

Definition SET_STRING_ELT (x : SEXP) i v : result unit :=
  add%stack "SET_STRING_ELT" in
  let%success x_type := TYPEOF x in
  ifb x_type <> StrSxp then
    result_error "It can only be applied to a character vector."
  else
    let%success v_type := TYPEOF v in
    ifb v_type <> CharSxp then
      result_error "The value must be a CharSxp."
    else
      let%success x_len := XLENGTH x in
      ifb i < 0 \/ i >= x_len then
        result_error "Outbound index."
      else
        write%Pointer x at i := v in
        result_skip.

Definition COPY_TRUELENGTH (vto vfrom : SEXP) :=
  add%stack "COPY_TRUELENGTH" in
  let%success vfrom_growable := IS_GROWABLE vfrom in
  if negb vfrom_growable then
    let%success vfrom_len := XTRUELENGTH vfrom in
    SET_TRUELENGTH vto vfrom_len
  else result_skip.

Definition duplicate1 s deep :=
  add%stack "duplicate1" in
  run%exit
    if%success ALTREP s then
      unimplemented_function "ALTREP_DUPLICATE_EX"
    else result_rskip in
  let%success s_type := TYPEOF s in
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
      result_rreturn s
    | CloSxp =>
      read%clo _, s_clo := s in
      let t_ :=
        make_SExpRec_clo R_NilValue
          (clo_formals s_clo) (clo_body s_clo) (clo_env s_clo) in
      let%alloc t := t_ in
      run%success DUPLICATE_ATTRIB t s deep in
      (** JIT functions have been ignored here. **)
      result_rsuccess t
    | ListSxp =>
      let%success t := duplicate_list s deep in
      result_rsuccess t
    | LangSxp =>
      let%success t := duplicate_list s deep in
      set%type t := LangSxp in
      run%success DUPLICATE_ATTRIB t s deep in
      result_rsuccess t
    | DotSxp =>
      let%success t := duplicate_list s deep in
      set%type t := DotSxp in
      run%success DUPLICATE_ATTRIB t s deep in
      result_rsuccess t
    | CharSxp =>
      result_rreturn s
    | ExprSxp
    | VecSxp =>
      let%success n := XLENGTH s in
      let%success t := allocVector globals s_type n in
      do%success
      for i from 0 to n - 1 do
        let%success s_i := VECTOR_ELT s i in
        let%success s_i_duplicated := duplicate_child s_i deep in
        run%success SET_VECTOR_ELT t i s_i_duplicated in
        result_skip in
      run%success DUPLICATE_ATTRIB t s deep in
      run%success COPY_TRUELENGTH t s in
      result_rsuccess t
    | LglSxp =>
      let%success n := XLENGTH s in
      let%success t := allocVector globals s_type n in
      run%success
        ifb n = 1 then
          read%Logical s_0 := s at 0 in
          write%Logical t at 0 := s_0 in
          result_skip
        else
          read%VectorLogical s_ := s in
          write%VectorLogical t := s_ in
          result_skip in
      run%success DUPLICATE_ATTRIB t s deep in
      run%success COPY_TRUELENGTH t s in
      result_rsuccess t
    | IntSxp =>
      let%success n := XLENGTH s in
      let%success t := allocVector globals s_type n in
      run%success
        ifb n = 1 then
          read%Integer s_0 := s at 0 in
          write%Integer t at 0 := s_0 in
          result_skip
        else
          read%VectorInteger s_ := s in
          write%VectorInteger t := s_ in
          result_skip in
      run%success DUPLICATE_ATTRIB t s deep in
      run%success COPY_TRUELENGTH t s in
      result_rsuccess t
    | RealSxp =>
      let%success n := XLENGTH s in
      let%success t := allocVector globals s_type n in
      run%success
        ifb n = 1 then
          read%Real s_0 := s at 0 in
          write%Real t at 0 := s_0 in
          result_skip
        else
          read%VectorReal s_ := s in
          write%VectorReal t := s_ in
          result_skip in
      run%success DUPLICATE_ATTRIB t s deep in
      run%success COPY_TRUELENGTH t s in
      result_rsuccess t
    | CplxSxp =>
      let%success n := XLENGTH s in
      let%success t := allocVector globals s_type n in
      run%success
        ifb n = 1 then
          read%Complex s_0 := s at 0 in
          write%Complex t at 0 := s_0 in
          result_skip
        else
          read%VectorComplex s_ := s in
          write%VectorComplex t := s_ in
          result_skip in
      run%success DUPLICATE_ATTRIB t s deep in
      run%success COPY_TRUELENGTH t s in
      result_rsuccess t
    | RawSxp =>
      result_not_implemented "Raw case."
    | StrSxp =>
      let%success n := XLENGTH s in
      let%success t := allocVector globals s_type n in
      run%success
        ifb n = 1 then
          read%Pointer s_0 := s at 0 in
          write%Pointer t at 0 := s_0 in
          result_skip
        else
          read%VectorPointer s_ := s in
          write%VectorPointer t := s_ in
          result_skip in
      run%success DUPLICATE_ATTRIB t s deep in
      run%success COPY_TRUELENGTH t s in
      result_rsuccess t
    | PromSxp =>
      result_rreturn s
    | S4Sxp =>
      unimplemented_function "allocS4Object"
    | _ => result_error "Unimplemented type."
    end in
  let%success t_type := TYPEOF t in
  run%success
    ifb t_type = s_type then
      let%success s_obj := OBJECT s in
      run%success SET_OBJECT t s_obj in
      if%success IS_S4_OBJECT s then
        SET_S4_OBJECT t
      else UNSET_S4_OBJECT t
    else result_skip in
  result_success t.

Definition duplicate s :=
  add%stack "duplicate" in
  duplicate1 s true.

Definition shallow_duplicate s :=
  add%stack "shallow_duplicate" in
  duplicate1 s false.

(** The following function is actually from main/memory.c. It has been
  placed here to solve a circular file dependency. **)
Definition SHALLOW_DUPLICATE_ATTRIB vto vfrom :=
  add%stack "SHALLOW_DUPLICATE_ATTRIB" in
  let%success vfrom_attrib := ATTRIB vfrom in
  let%success vfrom_attrib := shallow_duplicate vfrom_attrib in
  run%success SET_ATTRIB vto vfrom_attrib in
  let%success vfrom_obj := OBJECT vfrom in
  map%pointer vto with set_obj vfrom_obj in
  run%success
    if%success IS_S4_OBJECT vfrom then
      SET_S4_OBJECT vto
    else UNSET_S4_OBJECT vto in
  result_skip.


Definition isVector s :=
  add%stack "isVector" in
  let%success s_type := TYPEOF s in
  match s_type with
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | RawSxp
  | VecSxp
  | ExprSxp =>
    result_success true
  | _ =>
    result_success false
  end.

Definition isMatrix s :=
  add%stack "isMatrix" in
  if%success isVector s then
    let%success t := runs_getAttrib runs s R_DimSymbol in
    let%success t_type := TYPEOF t in
    ifb t_type = IntSxp then
      let%success t_len := LENGTH globals t in
      ifb t_len = 2 then
        result_success true
      else result_success false
    else result_success false
  else result_success false.

Definition R_cycle_detected s child :=
  add%stack "R_cycle_detected" in
  let%success child_type := TYPEOF child in
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
      result_success false
    | _ =>
      result_success true
    end
  else
    run%exit
      let%success child_attrib := ATTRIB child in
      ifb child_attrib <> R_NilValue then
        if%success runs_R_cycle_detected runs s child_attrib then
          result_rreturn true
        else result_rskip
      else result_rskip in
    if%success isPairList child then
      fold%return
      along child
      as el, _, el_list do
        let%success r :=
          runs_R_cycle_detected runs s (list_carval el_list) in
        ifb s = el \/ r then
          result_rreturn true
        else
          let%success el_attrib := ATTRIB el in
          let%success r :=
            runs_R_cycle_detected runs s el_attrib in
          ifb el_attrib <> R_NilValue /\ r then
            result_rreturn true
          else result_rskip
      using runs in
      result_success false
    else
      if%success isVectorList child then
        read%VectorPointer child_ := child in
        do%let r := false
        for e in%array VecSxp_data child_ do
          if r then result_success r
          else runs_R_cycle_detected runs s e
      else result_success false.

End Parameterised.

