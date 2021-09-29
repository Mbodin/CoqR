(** Features.FAttrib.
  The function names of this file correspond to the function names
  in the file main/attrib.c. **)

(* Copyright © 2018 Martin Bodin, Tomás Díaz

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
From CoqR Require Import Rcore.
From CoqR.features Require Import FUtil.

Section Parameters.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.
Local Coercion int_to_double : Z >-> double.

(** This enumeration is used in a local definition. **)
Inductive enum_none_partial_partial2_full :=
  | enum_none
  | enum_partial
  | enum_partial2
  | enum_full.

Instance enum_none_partial_partial2_full_Comparable : Comparable enum_none_partial_partial2_full.
Proof. prove_comparable_trivial_inductive. Defined.

Definition do_attr (call op args env : SEXP) : result_SEXP :=
  add%stack "do_attr" in
  (** The initialisation of [do_attr_formals] is done in [do_attr_init] in Rinit. **)
  let%success nargs := R_length globals runs args in
  let%success argList := matchArgs globals runs do_attr_do_attr_formals args call in
  ifb nargs < 2 \/ nargs > 3 then
    result_error "Either 2 or 3 arguments are required."
  else
    read%list argList_car, argList_cdr, _ := argList in
    let s := argList_car in
    read%list argList_cdr_car, _, _ := argList_cdr in
    let t := argList_cdr_car in
    let%success t_str := isString t in
    if negb t_str then
      result_error "‘which’ must be of mode character."
    else
      let%success t_len := R_length globals runs t in
      ifb t_len <> 1 then
        result_error "Exactly one attribute ‘which’ must be given."
      else
        let%success s_type := TYPEOF s in
        ifb s_type = EnvSxp then
          unimplemented_function "R_checkStack"
        else
          let%success exact :=
            ifb nargs = 3 then
              read%list _, args_cdr, _ := args in
              read%list _, args_cdr_cdr, _ := args_cdr in
              read%list args_cdr_cdr_car, _, _ := args_cdr_cdr in
              let%success exact := asLogical globals args_cdr_cdr_car in
              ifb exact = NA_LOGICAL then
                result_success false
              else result_success (decide (exact <> 0))
            else result_success false in
          let%success t_0 := STRING_ELT t 0 in
          ifb t_0 = NA_STRING then
            result_success (R_NilValue : SEXP)
          else
            let%success str := translateChar t_0 in
            let%success alist := ATTRIB s in
            fold%break (vmatch, tag) := (enum_none, R_NilValue : SEXP)
            along alist
            as _, alist_tag do
              let tmp := alist_tag in
              let%success tmp_name := PRINTNAME tmp in
              let%success s := CHAR tmp_name in
              ifb s = str then
                result_rreturn (enum_full, tmp)
              else if String.prefix str s then
                ifb vmatch = enum_partial \/ vmatch = enum_partial2 then
                  result_rsuccess (enum_partial2, tag)
                else result_rsuccess (enum_partial, tmp)
              else result_rsuccess (vmatch, tag) using runs in
            ifb vmatch = enum_partial2 then
              result_success (R_NilValue : SEXP)
            else
              let%exit (vmatch, tag) :=
                ifb vmatch <> enum_full /\ str = "names"%string then
                  result_rsuccess (enum_full, R_NamesSymbol : SEXP)
                else ifb vmatch <> enum_full /\ String.prefix "names" str then
                  ifb vmatch = enum_none /\ ~ exact then
                    let tag := R_NamesSymbol : SEXP in
                    let%success t := getAttrib globals runs s tag in
                    (* A potential warning has been formalised out here. *)
                    result_rreturn t
                  else
                    let%success tag_name := PRINTNAME tag in
                    let%success tag_name_ := CHAR tag_name in
                    ifb vmatch = enum_partial /\ tag_name_ = "names"%string then
                      let%success t := getAttrib globals runs s R_NamesSymbol in
                      ifb t <> R_NilValue then
                        result_rreturn (R_NilValue : SEXP)
                      else result_rsuccess (vmatch, tag)
                    else result_rsuccess (vmatch, tag)
                else result_rsuccess (vmatch, tag) in
              ifb vmatch = enum_none \/ (exact /\ vmatch <> enum_full) then
                result_success (R_NilValue : SEXP)
              else
                (* A potential warning has been formalised out here. *)
                getAttrib globals runs s tag.

(* attr(obj, which = "<name>")  <-  value    (op == 0)  and
        obj @ <name>            <-  value    (op == 1)
*)
Definition do_attrgets (call op args env : SEXP) : result_SEXP :=
  add%stack "do_attrgets" in
  run%success Rf_checkArityCall globals runs op args call in

  let%success op_val := PRIMVAL runs op in
  ifb op_val <> 0 then  (* @<- *)
    let%success input := allocVector globals StrSxp 1 in
    read%list _, args_cdr, _ := args in
    read%list args_cdr_car, _, _ := args_cdr in
    let nlist := args_cdr_car in
    run%success
      if%success isSymbol nlist then
        let%success nlist_name := PRINTNAME nlist in
        SET_STRING_ELT input 0 nlist_name
      else if%success isString nlist then
        let%success nlist_0 := STRING_ELT nlist 0 in
        SET_STRING_ELT input 0 nlist_0
      else result_error "Invalid type for slot name." in
    set%car args_cdr := input in
    let%success (disp, ans) :=
      DispatchOrEval globals runs call op "@<-" args env false false in
    if disp then
      result_success ans
    else
      read%list ans_car, ans_cdr, _ := ans in
      let obj := ans_car in
      read%list _, ans_cdr_cdr, _ := ans_cdr in
      read%list ans_cdr_cdr_car, _, _ := ans_cdr_cdr in
      let value := ans_cdr_cdr_car in
      unimplemented_function "check_slot_assign"
  else  (* attr(obj, "name") <- value : *)
    read%list args_car, args_cdr, _ := args in
    let obj := args_car in
    let%success obj :=
      if%success MAYBE_SHARED obj then
        shallow_duplicate globals runs obj
      else result_success obj in
    (** The initialisation of [do_attrgets_formals] is done in [do_attrgets_init] in Rinit. **)
    let%success argList :=
      matchArgs globals runs do_attrgets_do_attrgets_formals args call in
    read%list _, argList_cdr, _ := argList in
    read%list argList_cdr_car, _, _ := argList_cdr in
    let name := argList_cdr_car in
    let%success name_valid := isValidString globals name in
    let%success name_0 := STRING_ELT name 0 in
    ifb ~ name_valid \/ name_0 = NA_STRING then
      result_error "‘name’ must be non-null character string."
    else
      read%list _, args_cdr_cdr, _ := args_cdr in
      read%list args_cdr_cdr_car, _, _ := args_cdr_cdr in
      run%success setAttrib globals runs obj name args_cdr_cdr_car in
      run%success SETTER_CLEAR_NAMED obj in
      result_success obj.

End Parameters.

