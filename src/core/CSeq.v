(** Core.CSeq.
  The function names in this file correspond to the function names
  in the file main/seq.c. **)

(** The alternative representation ALTREP is meant to symbolically
  represent some operations, to avoid allocating trivial arrays into
  the memory.  The relevant code is however under active
  developpement, and it would not make sense to start formalising it
  right now.  We thus implement the following function using the
  traditionnal representation, although it needs more memory and time
  resources. **)

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
Require Import CDuplicate.
Require Import CCoerce.
Require Import CRinlinedfuns.
Require Import CRmath.

Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.

Definition rep2 S s ncopy :=
  add%stack "rep2" in
    let R2_SWITCH_LOOP S a nc it :=
        let n := 0 in
        let%success s_type := TYPEOF S s using S in
        match s_type with
        | LglSxp => do%success
                    for i from 0 to nc - 1 do
                        read%cell it_i := it at i using S in 
                        do%success n := n
                        for j from 0 to it_i - 1 do
                            read%Logical s_i := s at i using S in
                            write%Logical a at n := s_i using S in
                            result_success S (n + 1)
                        using S in
                        result_skip S
                    using S in
                    result_skip S                                 
        | IntSxp => do%success
                    for i from 0 to nc - 1 do
                        read%cell it_i := it at i using S in 
                        do%success n := n
                        for j from 0 to it_i - 1 do
                            read%Integer s_i := s at i using S in
                            write%Integer a at n := s_i using S in
                            result_success S (n + 1)
                        using S in
                        result_skip S
                    using S in
                    result_skip S   
        | RealSxp => do%success
                    for i from 0 to nc - 1 do
                        read%cell it_i := it at i using S in 
                        do%success n := n
                        for j from 0 to it_i - 1 do
                            read%Real s_i := s at i using S in
                            write%Real a at n := s_i using S in
                            result_success S (n + 1)
                        using S in
                        result_skip S
                    using S in
                    result_skip S   
        | CplxSxp => do%success
                    for i from 0 to nc - 1 do
                        read%cell it_i := it at i using S in 
                        do%success n := n
                        for j from 0 to it_i - 1 do
                            read%Complex s_i := s at i using S in
                            write%Complex a at n := s_i using S in
                            result_success S (n + 1)
                        using S in
                        result_skip S
                    using S in
                    result_skip S   
        | StrSxp => do%success
                    for i from 0 to nc - 1 do
                        read%cell it_i := it at i using S in 
                        do%success n := n
                        for j from 0 to it_i - 1 do
                            let%success s_i := STRING_ELT S s i using S in
                            run%success SET_STRING_ELT S a n s_i using S in
                            result_success S (n + 1)
                        using S in
                        result_skip S
                    using S in
                    result_skip S   
        | VecSxp
        | ExprSxp => do%success
                    for i from 0 to nc - 1 do
                        let%success s_i := VECTOR_ELT S s i using S in
                        let%success elt := lazy_duplicate S s_i using S in                   
                        read%cell it_i := it at i using S in 
                        do%success (j, n) := (0, n)
                        for j from 0 to it_i - 1 do
                            run%success SET_VECTOR_ELT S a n elt using S in 
                            result_success S ((j + 1), (n + 1))
                        using S in
                        ifb j < (Z.to_nat it_i) - 2 then
                            set%named elt := named_plural using S in
                            result_skip S
                        else result_skip S
                    using S in
                    result_skip S  
        | RawSxp => result_not_implemented "Raw case not implemented"
        | _ => result_error S "UNIMPLEMENTED TYPE"

        end
    in
    (** LONG_VECTOR_SUPPORT omitted **)
      let%success ncopy_type := TYPEOF S ncopy using S in
      let%success t :=
      ifb ncopy_type = RealSxp then
          coerceVector globals runs S ncopy RealSxp
      else
          coerceVector globals runs S ncopy IntSxp
      using S in

    let%success nc := xlength globals runs S ncopy using S in 
    let sna := 0 in
    let%success t_type := TYPEOF S t using S in
    let%success sna :=
    ifb t_type = RealSxp then
        do%success sna := sna
        for i from 0 to nc - 1 do
            read%Real t_i := t at i using S in
            ifb ISNAN t_i \/ t_i <= (-1)%Z \/ t_i >= (Z.to_nat R_XLEN_T_MAX) + 1 then               
                result_error S "invalid 'times' value"
            else
                result_success S (sna + (Z.to_nat (Double.double_to_int_zero t_i)))
        using S in
        result_success S sna
    else
        do%success sna := sna
        for i from 0 to nc - 1 do
            read%Integer t_i := t at i using S in
            ifb t_i = NA_INTEGER \/ t_i < 0 then               
                result_error S "invalid 'times' value"
            else
                result_success S (sna + (Z.to_nat t_i))
        using S in
        result_success S sna
    using S in
    ifb sna > (Z.to_nat R_XLEN_T_MAX) then
        result_error S "invalid 'times' value"
    else
    let na := sna in

    let%success s_type := TYPEOF S s using S in
    let%success a := allocVector globals S s_type na using S in
    run%success
    ifb t_type = RealSxp then
        read%VectorReal t_ := t using S in
        R2_SWITCH_LOOP S a nc t_
    else
        read%VectorInteger t_ := t using S in
        R2_SWITCH_LOOP S a nc t_
    using S in
    result_success S a.

Definition rep3 S s ns na :=
  add%stack "rep3" in
    
    (** let%success s_type := TYPEOF S s using S in
    let%success a := allocVector globals S s_type na using S in

    run%success 
    match s_type with
    | LglSxp =>
    | IntSxp =>
    | RealSxp =>
    | CplxSxp =>
    | RawSxp =>
    | StrSxp =>
    | VecSxp
    | ExprSxp =>
    | _ => result_error S "UNIMPLEMENTED TYPE"
    end
    using S in
    result_success S a. **)
    
    result_not_implemented "rep3".





    
End Parameterised.
