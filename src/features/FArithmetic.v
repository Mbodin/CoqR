(** Features.FArithmetic.
  The function names of this file correspond to the function names
  in the file main/arithmetic.c. **)

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
Require Import FUtil.
Require Import FComplex.
Require Import FSign.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition R_allocOrReuseVector S s1 s2 type n :=
  add%stack "R_allocOrReuseVector" in
  let%success n1 := XLENGTH S s1 using S in
  let%success n2 := XLENGTH S s2 using S in
  let%success s1_type := TYPEOF S s1 using S in
  let%success s1_nref := NO_REFERENCES S s1 using S in
  ifb n = n2 then
    let%success s2_type := TYPEOF S s2 using S in
    let%success s2_nref := NO_REFERENCES S s2 using S in
    let%success s2_attr := ATTRIB S s2 using S in
    ifb s2_type = type /\ s2_nref then
      run%success
        ifb s2_attr <> R_NilValue then
          run%success
            setAttrib globals runs S s2 R_NamesSymbol R_NilValue using S in
          result_skip S
        else result_skip S using S in
      result_success S s2
    else
      ifb n = n1 /\ s1_type = type /\ s1_nref /\ s2_attr = R_NilValue then
        result_success S s1
      else allocVector globals S type n
  else ifb n = n1 /\ s1_type = type /\ s1_nref then
    result_success S s1
  else allocVector globals S type n.

Definition R_integer_plus x y :=
  ifb x = NA_INTEGER \/ y = NA_INTEGER then NA_INTEGER
  else
    ifb (y < 0 /\ x > R_INT_MAX - y)%Z \/ (y > 0 /\ x < R_INT_MIN - y)%Z then
      (* A warning has been formalised out here. *)
      NA_INTEGER
    else (x + y)%Z.

Definition R_integer_minus x y :=
  ifb x = NA_INTEGER \/ y = NA_INTEGER then NA_INTEGER
  else
    ifb (y < 0 /\ x > R_INT_MAX + y)%Z \/ (y > 0 /\ x < R_INT_MIN + y)%Z then
      (* A warning has been formalised out here. *)
      NA_INTEGER
    else (x - y)%Z.

Definition R_integer_times x y :=
  ifb x = NA_INTEGER \/ y = NA_INTEGER then NA_INTEGER
  else
    let z := (x * y)%Z in
    ifb Double.mult (x : double) (y : double) = (z : double) /\ z <> NA_INTEGER then z
    else
      (* A warning has been formalised out here. *)
      NA_INTEGER.

Definition R_integer_divide x y :=
  ifb x = NA_INTEGER \/ y = NA_INTEGER then NA_REAL
  else Double.div (x : double) (y : double).

Definition integer_binary S (code : int) (s1 s2 lcall : SEXP) : result SEXP :=
  add%stack "integer_binary" in
  let%success n1 := XLENGTH S s1 using S in
  let%success n2 := XLENGTH S s2 using S in
  let n :=
    ifb n1 = 0 \/ n2 = 0 then 0
    else ifb n1 > n2 then n1 else n2 in
  let%success ans :=
    ifb code = DIVOP \/ code = POWOP then
      allocVector globals S RealSxp n
    else R_allocOrReuseVector S s1 s2 IntSxp n using S in
  ifb n = 0 then
    result_success S ans
  else
    run%success
      ifb code = PLUSOP then
        let pa := ans in
        let px1 := s1 in
        let px2 := s2 in
        do%let
        for i from 0 to n - 1 do
          let i1 := i mod n1 in
          let i2 := i mod n2 in
          read%Integer x1 := px1 at i1 using S in
          read%Integer x2 := px2 at i2 using S in
          write%Integer pa at i := R_integer_plus x1 x2 using S in
          result_skip S using S
      else ifb code = MINUSOP then
        let pa := ans in
        let px1 := s1 in
        let px2 := s2 in
        do%let
        for i from 0 to n - 1 do
          let i1 := i mod n1 in
          let i2 := i mod n2 in
          read%Integer x1 := px1 at i1 using S in
          read%Integer x2 := px2 at i2 using S in
          write%Integer pa at i := R_integer_minus x1 x2 using S in
          result_skip S using S
      else ifb code = TIMESOP then
        let pa := ans in
        let px1 := s1 in
        let px2 := s2 in
        do%let
        for i from 0 to n - 1 do
          let i1 := i mod n1 in
          let i2 := i mod n2 in
          read%Integer x1 := px1 at i1 using S in
          read%Integer x2 := px2 at i2 using S in
          write%Integer pa at i := R_integer_times x1 x2 using S in
          result_skip S using S
      else ifb code = DIVOP then
        let pa := ans in
        let px1 := s1 in
        let px2 := s2 in
        do%let
        for i from 0 to n - 1 do
          let i1 := i mod n1 in
          let i2 := i mod n2 in
          read%Integer x1 := px1 at i1 using S in
          read%Integer x2 := px2 at i2 using S in
          write%Real pa at i := R_integer_divide x1 x2 using S in
          result_skip S using S
      else ifb code = POWOP then
        let pa := ans in
        let px1 := s1 in
        let px2 := s2 in
        do%let
        for i from 0 to n - 1 do
          let i1 := i mod n1 in
          let i2 := i mod n2 in
          read%Integer x1 := px1 at i1 using S in
          read%Integer x2 := px2 at i2 using S in
          ifb x1 = 1 \/ x2 = 0 then
            write%Real pa at i := 1 using S in
            result_skip S
          else ifb x1 = NA_INTEGER \/ x2 = NA_INTEGER then
            write%Real pa at i := NA_REAL using S in
            result_skip S
          else unimplemented_function "R_POW" using S
      else ifb code = MODOP then
        let pa := ans in
        let px1 := s1 in
        let px2 := s2 in
        do%let
        for i from 0 to n - 1 do
          let i1 := i mod n1 in
          let i2 := i mod n2 in
          read%Integer x1 := px1 at i1 using S in
          read%Integer x2 := px2 at i2 using S in
          ifb x1 = NA_INTEGER \/ x2 = NA_INTEGER \/ x2 = 0 then
            write%Integer pa at i := NA_INTEGER using S in
            result_skip S
          else
            ifb x1 >= 0 /\ x2 > 0 then
              write%Integer pa at i := (x1 mod x2)%Z using S in
              result_skip S
            else unimplemented_function "myfmod" using S
      else ifb code = IDIVOP then
        let pa := ans in
        let px1 := s1 in
        let px2 := s2 in
        do%let
        for i from 0 to n - 1 do
          let i1 := i mod n1 in
          let i2 := i mod n2 in
          read%Integer x1 := px1 at i1 using S in
          read%Integer x2 := px2 at i2 using S in
          ifb x1 = NA_INTEGER \/ x2 = NA_INTEGER \/ x2 = 0 then
            write%Integer pa at i := NA_INTEGER using S in
            result_skip S
          else unimplemented_function "floor" using S
      else result_skip S using S in
    let%success s1_attr := ATTRIB S s1 using S in
    let%success s2_attr := ATTRIB S s2 using S in
    ifb s1_attr = R_NilValue /\ s2_attr = R_NilValue then
      result_success S ans
    else
      run%success
        ifb ans <> s2 /\ n = n2 /\ s2_attr <> R_NilValue then
          copyMostAttrib globals runs S s2 ans
        else result_skip S using S in
      run%success
        ifb ans <> s1 /\ n = n1 /\ s1_attr <> R_NilValue then
          copyMostAttrib globals runs S s1 ans
        else result_skip S using S in
      result_success S ans.

Definition real_binary S (code : int) s1 s2 : result SEXP :=
  add%stack "real_binary" in
  let%success n1 := XLENGTH S s1 using S in
  let%success n2 := XLENGTH S s2 using S in
  ifb n1 = 0 \/ n2 = 0 then
    allocVector globals S RealSxp 0
  else
    let n := ifb n1 > n2 then n1 else n2 in
    let%success ans := R_allocOrReuseVector S s1 s2 RealSxp n using S in
    run%success
      ifb code = PLUSOP then
        let%success s1_type := TYPEOF S s1 using S in
        let%success s2_type := TYPEOF S s2 using S in
        ifb s1_type = RealSxp /\ s2_type = RealSxp then
          let da := ans in
          let dx := s1 in
          let dy := s2 in
          ifb n2 = 1 then
            read%Real tmp := dy at 0 using S in
            do%let
            for i from 0 to n - 1 do
              read%Real dx_i := dx at i using S in
              write%Real da at i := Double.add dx_i tmp using S in
              result_skip S using S
          else ifb n1 = 1 then
            read%Real tmp := dx at 0 using S in
            do%let
            for i from 0 to n - 1 do
              read%Real dy_i := dy at i using S in
              write%Real da at i := Double.add tmp dy_i using S in
              result_skip S using S
          else ifb n1 = n2 then
            do%let
            for i from 0 to n - 1 do
              read%Real dx_i := dx at i using S in
              read%Real dy_i := dy at i using S in
              write%Real da at i := Double.add dx_i dy_i using S in
              result_skip S using S
          else
            do%let
            for i from 0 to n - 1 do
              let i1 := i mod n1 in
              let i2 := i mod n2 in
              read%Real dx_i1 := dx at i1 using S in
              read%Real dy_i2 := dy at i2 using S in
              write%Real da at i := Double.add dx_i1 dy_i2 using S in
              result_skip S using S
        else ifb s1_type = IntSxp then
          let da := ans in
          let px1 := s1 in
          let px2 := s2 in
          do%let
          for i from 0 to n - 1 do
            let i1 := i mod n1 in
            let i2 := i mod n2 in
            read%Integer px1_i1 := px1 at i1 using S in
            read%Real px2_i2 := px2 at i2 using S in
            write%Real da at i := Double.add (px1_i1 : double) px2_i2 using S in
            result_skip S using S
        else ifb s2_type = IntSxp then
          let da := ans in
          let px1 := s1 in
          let px2 := s2 in
          do%let
          for i from 0 to n - 1 do
            let i1 := i mod n1 in
            let i2 := i mod n2 in
            read%Real px1_i1 := px1 at i1 using S in
            read%Integer px2_i2 := px2 at i2 using S in
            write%Real da at i := Double.add px1_i1 (px2_i2 : double) using S in
            result_skip S using S
        else result_skip S
      else ifb code = MINUSOP then
        let%success s1_type := TYPEOF S s1 using S in
        let%success s2_type := TYPEOF S s2 using S in
        ifb s1_type = RealSxp /\ s2_type = RealSxp then
          let da := ans in
          let dx := s1 in
          let dy := s2 in
          ifb n2 = 1 then
            read%Real tmp := dy at 0 using S in
            do%let
            for i from 0 to n - 1 do
              read%Real dx_i := dx at i using S in
              write%Real da at i := Double.sub dx_i tmp using S in
              result_skip S using S
          else ifb n1 = 1 then
            read%Real tmp := dx at 0 using S in
            do%let
            for i from 0 to n - 1 do
              read%Real dy_i := dy at i using S in
              write%Real da at i := Double.sub tmp dy_i using S in
              result_skip S using S
          else ifb n1 = n2 then
            do%let
            for i from 0 to n - 1 do
              read%Real dx_i := dx at i using S in
              read%Real dy_i := dy at i using S in
              write%Real da at i := Double.sub dx_i dy_i using S in
              result_skip S using S
          else
            do%let
            for i from 0 to n - 1 do
              let i1 := i mod n1 in
              let i2 := i mod n2 in
              read%Real dx_i1 := dx at i1 using S in
              read%Real dy_i2 := dy at i2 using S in
              write%Real da at i := Double.sub dx_i1 dy_i2 using S in
              result_skip S using S
        else ifb s1_type = IntSxp then
          let da := ans in
          let px1 := s1 in
          let px2 := s2 in
          do%let
          for i from 0 to n - 1 do
            let i1 := i mod n1 in
            let i2 := i mod n2 in
            read%Integer px1_i1 := px1 at i1 using S in
            read%Real px2_i2 := px2 at i2 using S in
            write%Real da at i := Double.sub (px1_i1 : double) px2_i2 using S in
            result_skip S using S
        else ifb s2_type = IntSxp then
          let da := ans in
          let px1 := s1 in
          let px2 := s2 in
          do%let
          for i from 0 to n - 1 do
            let i1 := i mod n1 in
            let i2 := i mod n2 in
            read%Real px1_i1 := px1 at i1 using S in
            read%Integer px2_i2 := px2 at i2 using S in
            write%Real da at i := Double.sub px1_i1 (px2_i2 : double) using S in
            result_skip S using S
        else result_skip S
      else ifb code = TIMESOP then
        let%success s1_type := TYPEOF S s1 using S in
        let%success s2_type := TYPEOF S s2 using S in
        ifb s1_type = RealSxp /\ s2_type = RealSxp then
          let da := ans in
          let dx := s1 in
          let dy := s2 in
          ifb n2 = 1 then
            read%Real tmp := dy at 0 using S in
            do%let
            for i from 0 to n - 1 do
              read%Real dx_i := dx at i using S in
              write%Real da at i := Double.mult dx_i tmp using S in
              result_skip S using S
          else ifb n1 = 1 then
            read%Real tmp := dx at 0 using S in
            do%let
            for i from 0 to n - 1 do
              read%Real dy_i := dy at i using S in
              write%Real da at i := Double.mult tmp dy_i using S in
              result_skip S using S
          else ifb n1 = n2 then
            do%let
            for i from 0 to n - 1 do
              read%Real dx_i := dx at i using S in
              read%Real dy_i := dy at i using S in
              write%Real da at i := Double.mult dx_i dy_i using S in
              result_skip S using S
          else
            do%let
            for i from 0 to n - 1 do
              let i1 := i mod n1 in
              let i2 := i mod n2 in
              read%Real dx_i1 := dx at i1 using S in
              read%Real dy_i2 := dy at i2 using S in
              write%Real da at i := Double.mult dx_i1 dy_i2 using S in
              result_skip S using S
        else ifb s1_type = IntSxp then
          let da := ans in
          let px1 := s1 in
          let px2 := s2 in
          do%let
          for i from 0 to n - 1 do
            let i1 := i mod n1 in
            let i2 := i mod n2 in
            read%Integer px1_i1 := px1 at i1 using S in
            read%Real px2_i2 := px2 at i2 using S in
            write%Real da at i := Double.mult (px1_i1 : double) px2_i2 using S in
            result_skip S using S
        else ifb s2_type = IntSxp then
          let da := ans in
          let px1 := s1 in
          let px2 := s2 in
          do%let
          for i from 0 to n - 1 do
            let i1 := i mod n1 in
            let i2 := i mod n2 in
            read%Real px1_i1 := px1 at i1 using S in
            read%Integer px2_i2 := px2 at i2 using S in
            write%Real da at i := Double.mult px1_i1 (px2_i2 : double) using S in
            result_skip S using S
        else result_skip S
      else ifb code = DIVOP then
        let%success s1_type := TYPEOF S s1 using S in
        let%success s2_type := TYPEOF S s2 using S in
        ifb s1_type = RealSxp /\ s2_type = RealSxp then
          let da := ans in
          let dx := s1 in
          let dy := s2 in
          ifb n2 = 1 then
            read%Real tmp := dy at 0 using S in
            do%let
            for i from 0 to n - 1 do
              read%Real dx_i := dx at i using S in
              write%Real da at i := Double.div dx_i tmp using S in
              result_skip S using S
          else ifb n1 = 1 then
            read%Real tmp := dx at 0 using S in
            do%let
            for i from 0 to n - 1 do
              read%Real dy_i := dy at i using S in
              write%Real da at i := Double.div tmp dy_i using S in
              result_skip S using S
          else ifb n1 = n2 then
            do%let
            for i from 0 to n - 1 do
              read%Real dx_i := dx at i using S in
              read%Real dy_i := dy at i using S in
              write%Real da at i := Double.div dx_i dy_i using S in
              result_skip S using S
          else
            do%let
            for i from 0 to n - 1 do
              let i1 := i mod n1 in
              let i2 := i mod n2 in
              read%Real dx_i1 := dx at i1 using S in
              read%Real dy_i2 := dy at i2 using S in
              write%Real da at i := Double.div dx_i1 dy_i2 using S in
              result_skip S using S
        else ifb s1_type = IntSxp then
          let da := ans in
          let px1 := s1 in
          let px2 := s2 in
          do%let
          for i from 0 to n - 1 do
            let i1 := i mod n1 in
            let i2 := i mod n2 in
            read%Integer px1_i1 := px1 at i1 using S in
            read%Real px2_i2 := px2 at i2 using S in
            write%Real da at i := Double.div (px1_i1 : double) px2_i2 using S in
            result_skip S using S
        else ifb s2_type = IntSxp then
          let da := ans in
          let px1 := s1 in
          let px2 := s2 in
          do%let
          for i from 0 to n - 1 do
            let i1 := i mod n1 in
            let i2 := i mod n2 in
            read%Real px1_i1 := px1 at i1 using S in
            read%Integer px2_i2 := px2 at i2 using S in
            write%Real da at i := Double.div px1_i1 (px2_i2 : double) using S in
            result_skip S using S
        else result_skip S
      else ifb code = POWOP then
        unimplemented_function "R_POW"
      else ifb code = MODOP then
        result_not_implemented "myfmod"
      else ifb code = IDIVOP then
        result_not_implemented "myfloor"
      else result_skip S using S in
    let%success s1_attr := ATTRIB S s1 using S in
    let%success s2_attr := ATTRIB S s2 using S in
    ifb s1_attr = R_NilValue /\ s2_attr = R_NilValue then
      result_success S ans
    else
      run%success
        ifb ans <> s2 /\ n = n2 /\ s2_attr <> R_NilValue then
          copyMostAttrib globals runs S s2 ans
        else result_skip S using S in
      run%success
        ifb ans <> s1 /\ n = n1 /\ s1_attr <> R_NilValue then
          copyMostAttrib globals runs S s1 ans
        else result_skip S using S in
      result_success S ans.

Definition COERCE_IF_NEEDED S v tp :=
  add%stack "COERCE_IF_NEEDED" in
  let%success v_type := TYPEOF S v using S in
  ifb v_type <> tp then
    let%success vo := OBJECT S v using S in
    let%success v := coerceVector globals runs S v tp using S in
    run%success
      if vo then
        SET_OBJECT S v true
      else result_skip S using S in
    result_success S v
  else result_success S v.

Definition FIXUP_NULL_AND_CHECK_TYPES S v :=
  add%stack "FIXUP_NULL_AND_CHECK_TYPES" in
  let%success v_type := TYPEOF S v using S in
  match v_type with
  | NilSxp =>
    allocVector globals S IntSxp 0
  | CplxSxp
  | RealSxp
  | IntSxp
  | LglSxp =>
    result_success S v
  | _ =>
    result_error S "Non-numeric argument to binary operator."
  end.

Definition R_binary S (call op x y : SEXP) : result SEXP :=
  add%stack "R_binary" in
  let%success oper := PRIMVAL runs S op using S in
  let%success x := FIXUP_NULL_AND_CHECK_TYPES S x using S in
  let%success y := FIXUP_NULL_AND_CHECK_TYPES S y using S in
  let%success nx := XLENGTH S x using S in
  let%success ny := XLENGTH S y using S in
  let%success x_attrib := ATTRIB S x using S in
  let%success (xattr, xarray, xts, xS4) :=
    ifb x_attrib <> R_NilValue then
      let%success x_a := isArray globals runs S x using S in
      let%success x_ts := isTs globals runs S x using S in
      let%success x_s4 := isS4 S x using S in
      result_success S (true, x_a, x_ts, x_s4)
    else result_success S (false, false, false, false) using S in
  let%success y_attrib := ATTRIB S y using S in
  let%success (yattr, yarray, yts, yS4) :=
    ifb y_attrib <> R_NilValue then
      let%success y_a := isArray globals runs S y using S in
      let%success y_ts := isTs globals runs S y using S in
      let%success y_s4 := isS4 S y using S in
      result_success S (true, y_a, y_ts, y_s4)
    else result_success S (false, false, false, false) using S in
  run%success
    ifb xarray <> yarray then
      run%success
        ifb xarray /\ nx = 1 /\ ny <> 1 then
          ifb ny <> 0 then
            result_error S "Recycling array of length 1 in an array-vector arithmetic is depreciated."
          else
            let%success x := duplicate globals runs S x using S in
            run%success setAttrib globals runs S x R_DimSymbol R_NilValue using S in
            result_skip S
        else result_skip S using S in
      run%success
        ifb yarray /\ ny = 1 /\ nx <> 1 then
          ifb nx <> 0 then
            result_error S "Recycling array of length 1 in an array-vector arithmetic is depreciated."
          else
            let%success y := duplicate globals runs S y using S in
            run%success setAttrib globals runs S y R_DimSymbol R_NilValue using S in
            result_skip S
        else result_skip S using S in
      result_skip S
    else result_skip S using S in
  let%success (dims, xnames, ynames) :=
    ifb xarray \/ yarray then
      let%success dims :=
        ifb xarray /\ yarray then
          let%success c := conformable globals runs S x y using S in
          if negb c then
            result_error S "Non-conformable arrays."
          else getAttrib globals runs S x R_DimSymbol
        else ifb xarray /\ (ny <> 0 \/ nx = 0) then
          getAttrib globals runs S x R_DimSymbol
        else ifb yarray /\ (nx <> 0 \/ ny = 0) then
          getAttrib globals runs S y R_DimSymbol
        else result_success S (R_NilValue : SEXP) using S in
      let%success xnames :=
        if xattr then
          getAttrib globals runs S x R_DimNamesSymbol
        else result_success S (R_NilValue : SEXP) using S in
      let%success ynames :=
        if yattr then
          getAttrib globals runs S y R_DimNamesSymbol
        else result_success S (R_NilValue : SEXP) using S in
      result_success S (dims, xnames, ynames)
    else
      let dims := R_NilValue : SEXP in
      let%success xnames :=
        if xattr then
          getAttrib globals runs S x R_NamesSymbol
        else result_success S (R_NilValue : SEXP) using S in
      let%success ynames :=
        if yattr then
          getAttrib globals runs S y R_NamesSymbol
        else result_success S (R_NilValue : SEXP) using S in
      result_success S (dims, xnames, ynames) using S in
  let%success (tsp, klass) :=
    ifb xts \/ yts then
      ifb xts /\ yts then
        let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
        let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
        result_success S (tsp, klass)
      else if xts then
        ifb nx < ny then
          result_error S "Time-series/vector length mismatch."
        else
          let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
          let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
          result_success S (tsp, klass)
      else
        ifb ny < nx then
          result_error S "Time-series/vector length mismatch."
        else
          let%success tsp := getAttrib globals runs S y R_TspSymbol using S in
          let%success klass := getAttrib globals runs S y R_ClassSymbol using S in
          result_success S (tsp, klass)
    else result_success S (NULL, NULL) using S in
  (* A warning has been formalised out here. *)
  let%success x_type := TYPEOF S x using S in
  let%success y_type := TYPEOF S y using S in
  let%success val :=
    ifb x_type = CplxSxp \/ y_type = CplxSxp then
      let%success x := COERCE_IF_NEEDED S x CplxSxp using S in
      let%success y := COERCE_IF_NEEDED S y CplxSxp using S in
      complex_binary S oper x y
    else ifb x_type = RealSxp \/ y_type = RealSxp then
      let%success x :=
        ifb x_type <> IntSxp then
          COERCE_IF_NEEDED S x RealSxp
        else result_success S x using S in
      let%success y :=
        ifb y_type <> IntSxp then
          COERCE_IF_NEEDED S y RealSxp
        else result_success S y using S in
      real_binary S oper x y
    else integer_binary S oper x y call using S in
  ifb ~ xattr /\ ~ yattr then
    result_success S val
  else
    run%success
      ifb dims <> R_NilValue then
        run%success setAttrib globals runs S val R_DimSymbol dims using S in
        ifb xnames <> R_NilValue then
          run%success setAttrib globals runs S val R_DimNamesSymbol xnames using S in
          result_skip S
        else ifb ynames <> R_NilValue then
          run%success setAttrib globals runs S val R_DimNamesSymbol ynames using S in
          result_skip S
        else result_skip S
      else
        let%success val_len := XLENGTH S val using S in
        let%success xnames_len := xlength globals runs S xnames using S in
        ifb val_len = xnames_len then
          run%success setAttrib globals runs S val R_NamesSymbol xnames using S in
          result_skip S
        else
          let%success ynames_len := xlength globals runs S ynames using S in
          ifb val_len = ynames_len then
            run%success setAttrib globals runs S val R_NamesSymbol ynames using S in
            result_skip S
          else result_skip S using S in
    run%success
      ifb xts \/ yts then
        run%success setAttrib globals runs S val R_TspSymbol tsp using S in
        run%success setAttrib globals runs S val R_ClassSymbol klass using S in
        result_skip S
      else result_skip S using S in
    let%success val :=
      ifb xS4 \/ yS4 then
        asS4 globals runs S val true true
      else result_success S val using S in
    result_success S val.

Definition logical_unary S (code : int) s1 :=
  add%stack "logical_unary" in
  let%success n := XLENGTH S s1 using S in
  let%success names := getAttrib globals runs S s1 R_NamesSymbol using S in
  let%success dim := getAttrib globals runs S s1 R_DimSymbol using S in
  let%success dimnames := getAttrib globals runs S s1 R_DimNamesSymbol using S in
  read%VectorInteger s1_ := s1 using S in
  let px := VecSxp_data s1_ in
  let%success pa :=
    ifb code = PLUSOP then
      result_success S px
    else ifb code = MINUSOP then
      result_success S (ArrayListExtra.map (fun x =>
        ifb x = NA_INTEGER then NA_INTEGER
        else ifb x = 0 then 0 else -x) px)
    else result_error S "Invalid unary operator." using S in
  let (S, ans) := alloc_vector_int globals S pa in
  run%success
    ifb names <> R_NilValue then
      run%success setAttrib globals runs S ans R_NamesSymbol names using S in
      result_skip S
    else result_skip S using S in
  run%success
    ifb dim <> R_NilValue then
      run%success setAttrib globals runs S ans R_DimSymbol dim using S in
      result_skip S
    else result_skip S using S in
  run%success
    ifb dimnames <> R_NilValue then
      run%success setAttrib globals runs S ans R_DimNamesSymbol dimnames using S in
      result_skip S
    else result_skip S using S in
  result_success S ans.

Definition integer_unary S (code : int) s1 :=
  add%stack "integer_unary" in
  ifb code = PLUSOP then
    result_success S s1
  else ifb code = MINUSOP then
    let%success ans :=
      if%success NO_REFERENCES S s1 using S then
        result_success S s1
      else duplicate globals runs S s1 using S in
    read%VectorInteger s1_ := s1 using S in
    let px := VecSxp_data s1_ in
    let pa := ArrayListExtra.map (fun x =>
      ifb x = NA_INTEGER then NA_INTEGER
      else ifb x = 0 then 0 else -x) px in
    write%VectorInteger ans := pa using S in
    result_success S ans
  else result_error S "Invalid unary operator.".

Definition real_unary S (code : int) s1 :=
  add%stack "real_unary" in
  ifb code = PLUSOP then
    result_success S s1
  else ifb code = MINUSOP then
    let%success ans :=
      if%success NO_REFERENCES S s1 using S then
        result_success S s1
      else duplicate globals runs S s1 using S in
    read%VectorReal s1_ := s1 using S in
    let px := VecSxp_data s1_ in
    let pa := ArrayListExtra.map (fun x => Double.opp x) px in
    write%VectorReal ans := pa using S in
    result_success S ans
  else result_error S "Invalid unary operator.".

Definition R_unary S (call op s1 : SEXP) : result SEXP :=
  add%stack "R_unary" in
  let%success operation := PRIMVAL runs S op using S in
  let%success s1_type := TYPEOF S s1 using S in
  match s1_type with
  | LglSxp => logical_unary S operation s1
  | IntSxp => integer_unary S operation s1
  | RealSxp => real_unary S operation s1
  | CplxSxp => complex_unary globals runs S operation s1
  | _ => result_error S "Invalid argument to unary operator."
  end.

Definition do_arith S (call op args env : SEXP) : result SEXP :=
  add%stack "do_arith" in
  read%list args_car, args_cdr, _ := args using S in
  read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
  let%success argc :=
    ifb args = R_NilValue then
      result_success S 0
    else ifb args_cdr = R_NilValue then
      result_success S 1
    else ifb args_cdr_cdr = R_NilValue then
      result_success S 2
    else R_length globals runs S args using S in
  let arg1 := args_car in
  let arg2 := args_cdr_car in
  run%exit
    let%success arg1_attr := ATTRIB S arg1 using S in
    let%success arg2_attr := ATTRIB S arg2 using S in
    ifb arg1_attr <> R_NilValue \/ arg2_attr <> R_NilValue then
      if%defined ans := DispatchGroup globals runs S "Ops" call op args env using S then
        result_rreturn S ans
      else result_rskip S
    else ifb argc = 2 then
      let double_case S ans x1 x2 :=
        let%success op_val := PRIMVAL runs S op using S in
        ifb op_val = PLUSOP then
          run%success SET_SCALAR_DVAL S ans (Double.add x1 x2) using S in
          result_rreturn S ans
        else ifb op_val = MINUSOP then
          run%success SET_SCALAR_DVAL S ans (Double.sub x1 x2) using S in
          result_rreturn S ans
        else ifb op_val = TIMESOP then
          run%success SET_SCALAR_DVAL S ans (Double.mult x1 x2) using S in
          result_rreturn S ans
        else ifb op_val = DIVOP then
          run%success SET_SCALAR_DVAL S ans (Double.div x1 x2) using S in
          result_rreturn S ans
        else result_rskip S in
      if%success IS_SCALAR S arg1 RealSxp using S then
        let%success x1 := SCALAR_DVAL S arg1 using S in
        if%success IS_SCALAR S arg2 RealSxp using S then
          let%success x2 := SCALAR_DVAL S arg2 using S in
          let%success ans := ScalarValue2 globals S arg1 arg2 using S in
          double_case S ans x1 x2
        else
          if%success IS_SCALAR S arg2 IntSxp using S then
            let%success i2 := SCALAR_IVAL S arg2 using S in
            let x2 :=
              ifb i2 <> NA_INTEGER then
                (i2 : double)
              else NA_REAL in
            let%success ans := ScalarValue1 globals S arg1 using S in
            double_case S ans x1 x2
          else result_rskip S
      else
        if%success IS_SCALAR S arg1 IntSxp using S then
          let%success i1 := SCALAR_IVAL S arg1 using S in
          if%success IS_SCALAR S arg2 RealSxp using S then
            let x1 :=
              ifb i1 <> NA_INTEGER then
                (i1 : double)
              else NA_REAL in
            let%success x2 := SCALAR_DVAL S arg2 using S in
            let%success ans := ScalarValue1 globals S arg2 using S in
            double_case S ans x1 x2
          else
            if%success IS_SCALAR S arg2 IntSxp using S then
              let%success i2 := SCALAR_IVAL S arg2 using S in
              let%success op_val := PRIMVAL runs S op using S in
              ifb op_val = PLUSOP then
                let%success ans := ScalarValue2 globals S arg1 arg2 using S in
                run%success SET_SCALAR_IVAL S ans (R_integer_plus i1 i2) using S in
                result_rreturn S ans
              else ifb op_val = MINUSOP then
                let%success ans := ScalarValue2 globals S arg1 arg2 using S in
                run%success SET_SCALAR_IVAL S ans (R_integer_minus i1 i2) using S in
                result_rreturn S ans
              else ifb op_val = TIMESOP then
                let%success ans := ScalarValue2 globals S arg1 arg2 using S in
                run%success SET_SCALAR_IVAL S ans (R_integer_times i1 i2) using S in
                result_rreturn S ans
              else ifb op_val = DIVOP then
                let (S, ans) := ScalarReal globals S (R_integer_divide i1 i2) in
                result_rreturn S ans
              else result_rskip S
            else result_rskip S
        else result_rskip S
    else ifb argc = 1 then
      if%success IS_SCALAR S arg1 RealSxp using S then
        let%success op_val := PRIMVAL runs S op using S in
        ifb op_val = PLUSOP then
          result_rreturn S arg1
        else ifb op_val = MINUSOP then
          let%success ans := ScalarValue1 globals S arg1 using S in
          let%success v := SCALAR_DVAL S arg1 using S in
          run%success SET_SCALAR_DVAL S ans (Double.opp v) using S in
          result_rreturn S ans
        else result_rskip S
      else
        if%success IS_SCALAR S arg1 IntSxp using S then
          let%success op_val := PRIMVAL runs S op using S in
          ifb op_val = PLUSOP then
            result_rreturn S arg1
          else ifb op_val = MINUSOP then
            let%success ival := SCALAR_IVAL S arg1 using S in
            let%success ans := ScalarValue1 globals S arg1 using S in
            run%success SET_SCALAR_IVAL S ans (ifb ival = NA_INTEGER then NA_INTEGER else -ival) using S in
            result_rreturn S ans
          else result_rskip S
        else result_rskip S
    else result_rskip S using S in
  ifb argc = 2 then
    R_binary S call op arg1 arg2
  else ifb argc = 1 then
    R_unary S call op arg1
  else result_error S "Operator needs one or two arguments.".

Definition math1 S sa f (lcall : SEXP) :=
  add%stack "math1" in
  let%success sa_in := isNumeric globals runs S sa using S in
  if negb sa_in then
    result_error S "Non-numeric argument to mathematical function."
  else
    let%success n := XLENGTH S sa using S in
    let%success sa := coerceVector globals runs S sa RealSxp using S in
    let%success sy :=
      if%success NO_REFERENCES S sa using S then
        result_success S sa
      else allocVector globals S RealSxp n using S in
    do%success for i from 0 to n - 1 do
      read%Real x := sa at i using S in
      let fx := f x in
      write%Real sy at i := fx using S in
      if ISNAN fx then
        if ISNAN x then
          write%Real sy at i := x using S in
          result_skip S
        else result_skip S
      else result_skip S using S in
    (* A warning has been formalised out here. *)
    let%success sa_attrib := ATTRIB S sa using S in
    run%success
      ifb sa <> sy /\ sa_attrib <> R_NilValue then
        SHALLOW_DUPLICATE_ATTRIB globals runs S sy sa
      else result_skip S using S in
    result_success S sy.

Definition do_math1 S (call op args env : SEXP) : result SEXP :=
  add%stack "do_math1" in
  run%success Rf_checkArityCall globals runs S op args call using S in
  run%success Rf_check1arg globals S args call "x" using S in
  if%defined ans := DispatchGroup globals runs S "Ops" call op args env using S then
    result_success S ans
  else
    read%list args_car, _, _ := args using S in
    if%success isComplex S args_car using S then
      complex_math1 S call op args env
    else
      let%success op_val := PRIMVAL runs S op using S in
      let MATH1 x := math1 S args_car x call in
      match Z.to_nat op_val with
      | 1 => MATH1 Double.floor
      | 2 => MATH1 Double.ceil
      | 3 => MATH1 Double.sqrt
      | 4 => MATH1 sign
      | 10 => MATH1 Double.exp
      | 11 => MATH1 Double.expm1
      | 12 => MATH1 Double.log1p
      | 20 => MATH1 Double.cos
      | 21 => MATH1 Double.sin
      | 22 => MATH1 Double.tan
      | 23 => MATH1 Double.acos
      | 24 => MATH1 Double.asin
      | 25 => MATH1 Double.atan
      | 30 => MATH1 Double.cosh
      | 31 => MATH1 Double.sinh
      | 32 => MATH1 Double.tanh
      | 33 => result_not_implemented "acosh"
      | 34 => result_not_implemented "asinh"
      | 35 => result_not_implemented "atanh"
      | 40 => result_not_implemented "lgammafn"
      | 41 => result_not_implemented "gammafn"
      | 42 => result_not_implemented "digamma"
      | 43 => result_not_implemented "trigamma"
      | 47 => result_not_implemented "cospi"
      | 48 => result_not_implemented "sinpi"
      | 49 => result_not_implemented "tanpi"
      | _ => result_error S "Unimplemented real function of 1 argument."
      end.

End Parameters.

