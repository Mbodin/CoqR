(** Core.CDstruct.
  The function names in this file correspond to the function names
  in the file main/dstruct.c. **)

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
Require Import CRinternals.


Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.
Local Coercion int_to_double : Z >-> double.


Definition mkPRIMSXP (offset : nat) (type : bool) : result_SEXP :=
  add%stack "mkPRIMSXP" in
  let type := if type then BuiltinSxp else SpecialSxp in
  let%success R_FunTab := get_R_FunTab runs in
  let FunTabSize := ArrayList.length R_FunTab in
  (** The initialisation of the array is performed in [mkPRIMSXP_init] in [Rinit]. **)
  ifb offset >= FunTabSize then
    result_error "Offset is out of range"
  else
    read%Pointer result := mkPRIMSXP_primCache at offset in
    ifb result = R_NilValue then
      let%alloc result := make_SExpRec_prim R_NilValue offset type in
      write%Pointer mkPRIMSXP_primCache at offset := result in
      result_success result
    else
      let%success result_type := TYPEOF result in
      ifb result_type <> type then
        result_error "Requested primitive type is not consistent with cached value."
      else result_success result.

Definition mkCLOSXP (formals body rho : SEXP) :=
  add%stack "mkCLOSXP" in
  let%success body_type := TYPEOF body in
  match body_type with
  | CloSxp
  | BuiltinSxp
  | SpecialSxp
  | DotSxp
  | AnySxp =>
    result_error "Invalid body argument."
  | _ =>
    let env :=
      ifb rho = R_NilValue then
        (R_GlobalEnv : SEXP)
      else rho in
    let%alloc c := make_SExpRec_clo R_NilValue formals body env in
    result_success c
  end.

Definition iSDDName (name : SEXP) :=
  add%stack "iSDDName" in
  let%success buf := CHAR name in
  ifb String.substring 0 2 buf = ".."%string /\ String.length buf > 2 then
    let buf := String.substring 2 (String.length buf) buf in
    (** I am simplifying the C code here. **)
    result_success (decide (Forall (fun c : Ascii.ascii =>
        Mem c (["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"])%char)
      (string_to_list buf)))
  else
  result_success false.

Definition mkSYMSXP (name value : SEXP) :=
  add%stack "mkSYMSXP" in
  let%success i := iSDDName name in
  let%alloc c := make_SExpRec_sym R_NilValue name value R_NilValue in
  run%success SET_DDVAL c i in
  result_success c.

End Parameterised.

