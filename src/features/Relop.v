(** Features.Relop.
  The function names of this file correspond to the function names
  in the file main/relop.c. **)

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
Require Import Ascii.
Require Import Rcore.
Require Import Util.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition DO_SCALAR_RELOP_int S (oper x y : int) :=
  add%stack "DO_SCALAR_RELOP_int" in
  ifb oper = EQOP then
    result_success S (ScalarLogical globals (decide (x = y)))
  else ifb oper = NEOP then
    result_success S (ScalarLogical globals (decide (x <> y)))
  else ifb oper = LTOP then
    result_success S (ScalarLogical globals (decide (x < y)))
  else ifb oper = GTOP then
    result_success S (ScalarLogical globals (decide (x > y)))
  else ifb oper = LEOP then
    result_success S (ScalarLogical globals (decide (x <= y)))
  else ifb oper = GEOP then
    result_success S (ScalarLogical globals (decide (x >= y)))
  else result_impossible S "Unknown constructor.".

Definition DO_SCALAR_RELOP_double S (oper : int) (x y : double) :=
  add%stack "DO_SCALAR_RELOP_double" in
  ifb oper = EQOP then
    result_success S (ScalarLogical globals
      (ifb Double.is_zero x /\ Double.is_zero y then true
       else decide (x = y)))
  else ifb oper = NEOP then
    result_success S (ScalarLogical globals
      (ifb Double.is_zero x /\ Double.is_zero y then false
       else decide (x <> y)))
  else ifb oper = LTOP then
    result_success S (ScalarLogical globals (decide (x < y)))
  else ifb oper = GTOP then
    result_success S (ScalarLogical globals (decide (x > y)))
  else ifb oper = LEOP then
    result_success S (ScalarLogical globals (decide (x <= y)))
  else ifb oper = GEOP then
    result_success S (ScalarLogical globals (decide (x >= y)))
  else result_impossible S "Unknown constructor.".

Definition ISNA_INT x :=
  decide (x = NA_INTEGER).

(** The next three functions are originally untyped as they are defined
  in preprocessor.  Their translations into Coq are thus more flexible. **)
Definition NR_HELPER T1 T2 S (op : T1 -> T2 -> bool) ans n n1 n2 read1 read2 (ISNA1 ISNA2 : _ -> bool) :=
  add%stack "NR_HELPER" in
  do%let for i from 0 to n - 1 do
    let i1 := i mod n1 in
    let i2 := i mod n2 in
    let%success x1 := read1 S i1 using S in
    let%success x2 := read2 S i2 using S in
    ifb ISNA1 x1 \/ ISNA2 x2 then
      write%Logical ans at i := NA_LOGICAL using S in
      result_skip S
    else
      write%Logical ans at i := op x1 x2 using S in
      result_skip S using S.

Definition NUMERIC_RELOP_int S (code : int) ans n n1 n2 read1 read2 (ISNA1 ISNA2 : int -> bool) :=
  add%stack "NUMERIC_RELOP_int" in
  ifb code = EQOP then
    NR_HELPER S (fun x1 x2 => decide (x1 = x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = NEOP then
    NR_HELPER S (fun x1 x2 => decide (x1 <> x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LTOP then
    NR_HELPER S (fun x1 x2 => decide (x1 < x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GTOP then
    NR_HELPER S (fun x1 x2 => decide (x1 > x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LEOP then
    NR_HELPER S (fun x1 x2 => decide (x1 <= x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GEOP then
    NR_HELPER S (fun x1 x2 => decide (x1 >= x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else result_impossible S "Unknown constructor.".

Definition NUMERIC_RELOP_double T1 T2 (id1 : T1 -> double) (id2 : T2 -> double) S
    (code : int) ans n n1 n2 read1 read2 ISNA1 ISNA2 :=
  add%stack "NUMERIC_RELOP_double" in
  ifb code = EQOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 = id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = NEOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 <> id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LTOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 < id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GTOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 > id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LEOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 <= id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GEOP then
    NR_HELPER S (fun x1 x2 => decide (id1 x1 >= id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else result_impossible S "Unknown constructor.".

Definition numeric_relop S code s1 s2 :=
  add%stack "numeric_relop" in
  let%success n1 := XLENGTH S s1 using S in
  let%success n2 := XLENGTH S s2 using S in
  let n := ifb n1 > n2 then n1 else n2 in
  let%success ans := allocVector globals S LglSxp n using S in
  let%success s1_in := isInteger globals runs S s1 using S in
  let%success s1_lg := isLogical S s1 using S in
  let%success s2_in := isInteger globals runs S s2 using S in
  let%success s2_lg := isLogical S s2 using S in
  let readINTEGER s S i :=
    add%stack "readINTEGER" in
    read%Integer r := s at i using S in
    result_success S r in
  let readREAL s S i :=
    add%stack "readREAL" in
    read%Real r := s at i using S in
    result_success S r in
  run%success
    ifb s1_in \/ s1_lg then
      ifb s2_in \/ s2_lg then
        NUMERIC_RELOP_int S code ans n n1 n2 (readINTEGER s1) (readINTEGER s2) ISNA_INT ISNA_INT
      else
        NUMERIC_RELOP_double (id : int -> double) id S code ans n n1 n2 (readINTEGER s1) (readREAL s2) ISNA_INT ISNAN
    else ifb s2_in \/ s2_lg then
      NUMERIC_RELOP_double id (id : int -> double) S code ans n n1 n2 (readREAL s1) (readINTEGER s2) ISNAN ISNA_INT
    else
      NUMERIC_RELOP_double id id S code ans n n1 n2 (readREAL s1) (readREAL s2) ISNAN ISNAN using S in
  result_success S ans.

Definition string_relop (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  unimplemented_function "string_relop".

Definition complex_relop (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  unimplemented_function "complex_relop".

Definition raw_relop (S : state) (code : int) (s1 s2 : SEXP) : result SEXP :=
  unimplemented_function "raw_relop".

Definition do_relop_dflt S (call op x y : SEXP) : result SEXP :=
  add%stack "do_relop_dflt" in
  let%success op_val := PRIMVAL runs S op using S in
  run%exit
    if%success IS_SIMPLE_SCALAR globals S x IntSxp using S then
      let%success ix := SCALAR_IVAL S x using S in
      if%success IS_SIMPLE_SCALAR globals S y IntSxp using S then
        let%success iy := SCALAR_IVAL S y using S in
        ifb ix = NA_INTEGER \/ iy = NA_INTEGER then
          result_rreturn S (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_int S op_val ix iy using S in
          result_rreturn S r
      else if%success IS_SIMPLE_SCALAR globals S y RealSxp using S then
        let%success dy := SCALAR_DVAL S y using S in
        ifb ix = NA_INTEGER \/ ISNAN dy then
          result_rreturn S (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double S op_val ix dy using S in
          result_rreturn S r
      else result_rskip S
    else if%success IS_SIMPLE_SCALAR globals S x RealSxp using S then
      let%success dx := SCALAR_DVAL S x using S in
      if%success IS_SIMPLE_SCALAR globals S y IntSxp using S then
        let%success iy := SCALAR_IVAL S y using S in
        ifb ISNAN dx \/ iy = NA_INTEGER then
          result_rreturn S (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double S op_val dx iy using S in
          result_rreturn S r
      else if%success IS_SIMPLE_SCALAR globals S y RealSxp using S then
        let%success dy := SCALAR_DVAL S y using S in
        ifb ISNAN dx \/ ISNAN dy then
          result_rreturn S (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double S op_val dx dy using S in
          result_rreturn S r
      else result_rskip S
    else result_rskip S using S in
  let%success nx := xlength globals runs S x using S in
  let%success ny := xlength globals runs S y using S in
  let%success typex := TYPEOF S x using S in
  let%success typey := TYPEOF S y using S in
  read%defined x_ := x using S in
  read%defined y_ := y using S in
  ifb attrib x_ = R_NilValue /\ attrib y_ = R_NilValue
      /\ (typex = RealSxp \/ typex = IntSxp)
      /\ (typey = RealSxp \/ typey = IntSxp)
      /\ nx > 0 /\ ny > 0 /\ (nx = 1 \/ ny = 1) then
    numeric_relop S op_val x y
  else
    let%success x :=
      let%success iS := isSymbol S x using S in
      let%success x_type := TYPEOF S x using S in
      ifb iS \/ x_type = LangSxp then
        let%success tmp := allocVector globals S StrSxp 1 using S in
        let%success tmp_0 :=
          if iS then
            PRINTNAME S x
          else unimplemented_function "deparse1" using S in
        run%success SET_STRING_ELT S tmp 0 tmp_0 using S in
        result_success S tmp
      else result_success S x using S in
    let%success y :=
      let%success iS := isSymbol S y using S in
      let%success y_type := TYPEOF S y using S in
      ifb iS \/ y_type = LangSxp then
        let%success tmp := allocVector globals S StrSxp 1 using S in
        let%success tmp_0 :=
          if iS then
            PRINTNAME S y
          else unimplemented_function "deparse1" using S in
        run%success SET_STRING_ELT S tmp 0 tmp_0 using S in
        result_success S tmp
      else result_success S y using S in
    let%success x :=
      if%success isNull S x using S then
        allocVector globals S IntSxp 0
      else result_success S x using S in
    let%success y :=
      if%success isNull S y using S then
        allocVector globals S IntSxp 0
      else result_success S y using S in
    let%success x_vector := isVector S x using S in
    let%success y_vector := isVector S y using S in
    ifb ~ x_vector \/ ~ y_vector then
      result_error S "Comparison is possible only for atomic and list types"
    else
      let%success x_type := TYPEOF S x using S in
      let%success y_type := TYPEOF S y using S in
      ifb x_type = ExprSxp \/ y_type = ExprSxp then
        result_error S "Comparison is now allowed for expressions"
      else
        let%success xarray := isArray globals runs S x using S in
        let%success yarray := isArray globals runs S y using S in
        let%success xts := isTs globals runs S x using S in
        let%success yts := isTs globals runs S y using S in
        let%success (dims, xnames, ynames) :=
          ifb xarray \/ yarray then
            let%success dims :=
              ifb xarray /\ yarray then
                let%success conf := conformable globals runs S x y using S in
                if negb conf then
                  result_error S "Non-conformable arrays."
                else getAttrib globals runs S x R_DimSymbol
              else ifb xarray /\ (ny <> 0 \/ nx = 0) then
                getAttrib globals runs S x R_DimSymbol
              else ifb yarray /\ (nx <> 0 \/ ny = 0) then
                getAttrib globals runs S y R_DimSymbol
              else result_success S (R_NilValue : SEXP) using S in
            let%success xnames := getAttrib globals runs S x R_DimNamesSymbol using S in
            let%success ynames := getAttrib globals runs S y R_DimNamesSymbol using S in
            result_success S (dims, xnames, ynames)
          else
            let%success xnames := getAttrib globals runs S x R_NamesSymbol using S in
            let%success ynames := getAttrib globals runs S y R_NamesSymbol using S in
            result_success S (R_NilValue : SEXP, xnames, ynames) using S in
        let%success (tsp, klass) :=
          ifb xts \/ yts then
            ifb xts /\ yts then
              let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
              let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
              result_success S (tsp, klass)
            else
              let%success x_len := xlength globals runs S x using S in
              let%success y_len := xlength globals runs S y using S in
              if xts then
                ifb x_len < y_len then
                  result_error S "Time-series/vector length mismatch."
                else
                  let%success tsp := getAttrib globals runs S x R_TspSymbol using S in
                  let%success klass := getAttrib globals runs S x R_ClassSymbol using S in
                  result_success S (tsp, klass)
              else
                ifb y_len < x_len then
                  result_error S "Time-series/vector length mismatch."
                else
                  let%success tsp := getAttrib globals runs S y R_TspSymbol using S in
                  let%success klass := getAttrib globals runs S y R_ClassSymbol using S in
                  result_success S (tsp, klass)
          else result_success S (NULL, NULL) using S in
        let%success x :=
          ifb nx > 0 /\ ny > 0 then
            (* A warning has been formalised out here. *)
            let%success x_str := isString S x using S in
            let%success y_str := isString S y using S in
            ifb x_str \/ y_str then
              let%success x := coerceVector globals runs S x StrSxp using S in
              let%success y := coerceVector globals runs S y StrSxp using S in
              string_relop S op_val x y
            else
              let%success x_cplx := isComplex S x using S in
              let%success y_cplx := isComplex S y using S in
              ifb x_cplx \/ y_cplx then
                let%success x := coerceVector globals runs S x CplxSxp using S in
                let%success y := coerceVector globals runs S y CplxSxp using S in
                complex_relop S op_val x y
              else
                let%success x_num := isNumeric globals runs S x using S in
                let%success y_num := isNumeric globals runs S y using S in
                let%success x_lgl := isLogical S x using S in
                let%success y_lgl := isLogical S y using S in
                ifb (x_num \/ x_lgl) /\ (y_num \/ y_lgl) then
                  numeric_relop S op_val x y
                else
                  let%success x_real := isReal S x using S in
                  let%success y_real := isReal S y using S in
                  ifb x_real \/ y_real then
                    let%success x := coerceVector globals runs S x RealSxp using S in
                    let%success y := coerceVector globals runs S y RealSxp using S in
                    numeric_relop S op_val x y
                  else
                    let%success x_int := isInteger globals runs S x using S in
                    let%success y_int := isInteger globals runs S y using S in
                    ifb x_int \/ y_int then
                      let%success x := coerceVector globals runs S x IntSxp using S in
                      let%success y := coerceVector globals runs S y IntSxp using S in
                      numeric_relop S op_val x y
                    else ifb x_lgl \/ y_lgl then
                      let%success x := coerceVector globals runs S x LglSxp using S in
                      let%success y := coerceVector globals runs S y LglSxp using S in
                      numeric_relop S op_val x y
                    else ifb x_type = RawSxp \/ y_type = RawSxp then
                      let%success x := coerceVector globals runs S x RawSxp using S in
                      let%success y := coerceVector globals runs S y RawSxp using S in
                      raw_relop S op_val x y
                    else result_error S "Comparison of these types is not implemented."
          else allocVector globals S LglSxp 0 using S in
        run%success
          ifb dims <> R_NilValue then
            run%success setAttrib globals runs S x R_DimSymbol dims using S in
            ifb xnames <> R_NilValue then
              run%success setAttrib globals runs S x R_DimNamesSymbol xnames using S in
              result_skip S
            else ifb ynames <> R_NilValue then
              run%success setAttrib globals runs S x R_DimNamesSymbol ynames using S in
              result_skip S
            else result_skip S
          else
            let%success x_len := xlength globals runs S x using S in
            let%success xnames_len := xlength globals runs S xnames using S in
            ifb xnames <> R_NilValue /\ x_len = xnames_len then
              run%success setAttrib globals runs S x R_NamesSymbol xnames using S in
              result_skip S
            else
              let%success ynames_len := xlength globals runs S ynames using S in
              ifb ynames <> R_NilValue /\ x_len = ynames_len then
                run%success setAttrib globals runs S x R_NamesSymbol ynames using S in
                result_skip S
              else result_skip S using S in
        run%success
          ifb xts \/ yts then
            run%success setAttrib globals runs S x R_TspSymbol tsp using S in
            run%success setAttrib globals runs S x R_ClassSymbol klass using S in
            result_skip S
          else result_skip S using S in
        result_success S x.

Definition do_relop S (call op args env : SEXP) : result SEXP :=
  add%stack "do_relop" in
  read%list args_car, args_cdr, _ := args using S in
  read%list args_cdr_car, args_cdr_cdr, _ := args_cdr using S in
  let%success argc :=
    ifb args <> R_NilValue then
      ifb args_cdr <> R_NilValue then
        ifb args_cdr_cdr = R_NilValue then
          result_success S 2
        else R_length globals runs S args
      else R_length globals runs S args
   else R_length globals runs S args using S in
  let arg1 := args_car in
  let arg2 := args_cdr_car in
  read%defined arg1_ := arg1 using S in
  read%defined arg2_ := arg1 using S in
  run%exit
    ifb attrib arg1_ <> R_NilValue \/ attrib arg2_ <> R_NilValue then
      if%defined ans := DispatchGroup globals runs S "Ops" call op args env using S then
        result_rreturn S ans
      else result_rskip S
    else result_rskip S using S in
  ifb argc <> 2 then
    result_error S "Operator needs two arguments."
  else do_relop_dflt S call op arg1 arg2.

End Parameters.

