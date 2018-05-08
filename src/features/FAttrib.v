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
Require Import Rcore.
Require Import Util.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

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
          unimplemented_function "R_checkStack"
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
            fold%break (vmatch, tag) := (enum_none, R_NilValue : SEXP)
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
  run%success Rf_checkArityCall globals runs S op args call using S in
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
      unimplemented_function "check_slot_assign"
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

End Parameters.

