(** Core.CSubscript.
  The function names in this file correspond to the function names
  in the file main/subscript.c. **)

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
Require Import CRinlinedfuns.
Require Import CAttrib.
Require Import CDuplicate.
Require Import CArithmetic.

Section Parameterised.

(** Global Variables **)

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition get1index (S : state) (s names : SEXP) (len pok pos : int) (call : SEXP) : result int :=
  add%stack "get1index" in
    result_not_implemented "get1index".
                           

Definition vectorIndex (S : state) (x thesub : SEXP) (start stop pok : int) (call : SEXP) (dup : bool) : result SEXP :=
  add%stack "vectorIndex" in
    result_not_implemented "vectorIndex".

  
Definition logicalSubscript (S : state) (s : SEXP) (ns nx : nat) (stretch : nat) (call : SEXP) : result SEXP :=
  add%stack "logicalSubscript" in
    result_not_implemented "logicalSubscript".

Definition realSubscript S s (ns nx stretch : nat) call :=
  add%stack "realSubscript" in
    let isna := false in
    let canstretch := decide (stretch > 0) in
    let stretch := 0 : nat in
    let min := 0 : double in
    let max := 0 : double in
    do%success (min, max, isna) := (min, max, isna)
    for i from 0 to ns - 1 do                                
        read%Real ii := s at i using S in
        if R_FINITE ii then                                
            let min := ifb ii < min then ii else min in
            let max := ifb ii > max then ii else max in
            result_success S (min, max, isna)
        else                 
            result_success S (min, max, true)
    using S in

    let%success stretch :=                                     
    ifb max > nx then                                     
        if canstretch then 
            result_success S (Z.to_nat (Double.double_to_int_zero max))
        else
            result_error S "subscript out of bounds"
    else
        result_success S stretch
    using S in

    ifb min < 0 then
        ifb max = 0 /\ ~ isna then
            let stretch := 0 : nat in
            let%success indx := allocVector globals S LglSxp nx using S in 
            do%success for i from 0 to nx - 1 do write%Logical indx at i := 1 using S in result_skip S
            using S in                                                                  
            do%success
            for i from 0 to ns - 1 do
                read%Real dx := s at i using S in
                ifb R_FINITE dx /\ dx <> 0 /\ Double.opp dx <= (nx : double) then                                                                 
                    let ix := Z.to_nat (Double.double_to_int_zero (Double.sub (Double.opp dx) (1 : double))) in
                    write%Logical indx at ix := 0 using S in result_skip S
                else
                    result_skip S
            using S in

            let%success s := logicalSubscript S indx nx nx stretch call using S in
            result_success S (s : SEXP, stretch)
        else
            result_error S "only 0's may be mixed with negative subscripts"
    else
        (* Only return a REALSXP index if we need to *)
        let cnt := 0 in
        let int_ok := true in
        do%success (int_ok, cnt) := (int_ok, cnt) 
        for i from 0 to ns - 1 do
            read%Real ds := s at i using S in
            let int_ok := ifb R_FINITE ds /\ ds > INT_MAX then false else int_ok in
            let cnt := ifb ~ (R_FINITE ds) \/ ds%Z <> 0 then cnt + 1 else cnt in
            result_success S (int_ok, cnt)
        using S in

        let%success indx :=
        if int_ok then 
            let%success indx := allocVector globals S IntSxp cnt using S in
            do%success cnt := 0
            for i from 0 to ns - 1 do
                read%Real ds := s at i using S in
                let ia := if negb (R_FINITE ds) then NA_INTEGER else Double.double_to_int_zero ds in
                ifb ia <> 0 then
                    write%Integer indx at cnt := ia using S in
                    result_success S (cnt + 1)
                else
                    result_success S cnt
            using S in
            result_success S indx 
        else
            let%success indx := allocVector globals S RealSxp cnt using S in
            do%success cnt := 0
            for i from 0 to ns - 1 do
                read%Real ds := s at i using S in                   
                ifb ~ (R_FINITE ds) \/ ds%Z <> 0 then                   
                    write%Real indx at cnt := ds using S in
                    result_success S (cnt + 1)
                else
                    result_success S cnt
            using S in                       
            result_success S indx 
        using S in
        result_success S (indx : SEXP, stretch).


Definition makeSubscript S x s stretch (call : SEXP)  :=
  add%stack "makeSubscript" in
    let%success x_isVector := isVector S x using S in
    let%success x_isList := isList globals S x using S in
    let%success x_isLanguage := isLanguage globals S x using S in
    ifb ~ (x_isVector \/ x_isList \/ x_isLanguage) then
        result_error S "subscripting on non-vector"
    else
    
    let%success nx := xlength globals runs S x using S in  

    let%success s_isScalar := IS_SCALAR S s IntSxp using S in
    run%exit
    (* special case for simple indices -- does not duplicate *)
    if s_isScalar then
        let%success i := SCALAR_IVAL S s using S in
        ifb 0%Z < i /\ i <= nx then
            result_rreturn S (s, 0)
        else
            result_rskip S
    else
        let%success s_isScalar := IS_SCALAR S s RealSxp using S in
        if s_isScalar then
            let%success di := SCALAR_DVAL S s using S in
            ifb 1%Z <= (Double.double_to_int_zero di) /\ di <= nx then
                result_rreturn S (s, 0)
        else
            result_rskip S
        else result_rskip S
    using S in

    let%success ns := xlength globals runs S s using S in    
    let ans := (R_NilValue : SEXP) in
    let%success s_type := TYPEOF S s using S in
    let%success (ans, stretch) :=
    match s_type with
    | NilSxp =>
      let%success ans := allocVector globals S IntSxp 0 using S in
      result_success S (ans, 0)
    | LglSxp => unimplemented_function "logicalSubscript"  
    | IntSxp => unimplemented_function "integerSubscript"
    | RealSxp => realSubscript S s ns nx stretch call
    | StrSxp =>
      let%success names := getAttrib globals runs S x R_NamesSymbol using S in
      unimplemented_function "stringSubscript"
    | SymSxp =>
      ifb s = R_MissingArg then
          unimplemented_function "nullSubscript"
      else
          result_success S (ans, 0)
    | _ => result_error S "invalid subscript type"
    end
    using S in
    result_success S (ans, stretch).


End Parameterised.
