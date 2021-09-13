(** Features.FRelop.
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
From Lib Require Import Double.
From CoqR Require Import Rcore.
Require Import FUtil.

Section Parameters.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.

Local Coercion int_to_double : Z >-> double.


Definition DO_SCALAR_RELOP_int (oper x y : int) :=
  add%stack "DO_SCALAR_RELOP_int" in
  ifb oper = EQOP then
    result_success (ScalarLogical globals (decide (x = y)))
  else ifb oper = NEOP then
    result_success (ScalarLogical globals (decide (x <> y)))
  else ifb oper = LTOP then
    result_success (ScalarLogical globals (decide (x < y)))
  else ifb oper = GTOP then
    result_success (ScalarLogical globals (decide (x > y)))
  else ifb oper = LEOP then
    result_success (ScalarLogical globals (decide (x <= y)))
  else ifb oper = GEOP then
    result_success (ScalarLogical globals (decide (x >= y)))
  else result_impossible "Unknown constructor.".

Definition DO_SCALAR_RELOP_double (oper : int) (x y : double) :=
  add%stack "DO_SCALAR_RELOP_double" in
  ifb oper = EQOP then
    result_success (ScalarLogical globals
      (ifb Double.is_zero x /\ Double.is_zero y then true
       else decide (x = y)))
  else ifb oper = NEOP then
    result_success (ScalarLogical globals
      (ifb Double.is_zero x /\ Double.is_zero y then false
       else decide (x <> y)))
  else ifb oper = LTOP then
    result_success (ScalarLogical globals (decide (x < y)))
  else ifb oper = GTOP then
    result_success (ScalarLogical globals (decide (x > y)))
  else ifb oper = LEOP then
    result_success (ScalarLogical globals (decide (x <= y)))
  else ifb oper = GEOP then
    result_success (ScalarLogical globals (decide (x >= y)))
  else result_impossible "Unknown constructor.".

Definition ISNA_INT x :=
  decide (x = NA_INTEGER).

(** The next three functions are originally untyped as they are defined
  in preprocessor.  Their translations into Coq are thus more flexible. **)
Definition NR_HELPER T1 T2 (op : T1 -> T2 -> bool) ans n n1 n2 read1 read2 (ISNA1 ISNA2 : _ -> bool) :=
  add%stack "NR_HELPER" in
  do%let for i from 0 to n - 1 do
    let i1 := i mod n1 in
    let i2 := i mod n2 in
    let%success x1 := read1 i1 in
    let%success x2 := read2 i2 in
    ifb ISNA1 x1 \/ ISNA2 x2 then
      write%Logical ans at i := NA_LOGICAL in
      result_skip
    else
      write%Logical ans at i := op x1 x2 in
      result_skip.

Definition NUMERIC_RELOP_int (code : int) ans n n1 n2 read1 read2 (ISNA1 ISNA2 : int -> bool) :=
  add%stack "NUMERIC_RELOP_int" in
  ifb code = EQOP then
    NR_HELPER (fun x1 x2 => decide (x1 = x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = NEOP then
    NR_HELPER (fun x1 x2 => decide (x1 <> x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LTOP then
    NR_HELPER (fun x1 x2 => decide (x1 < x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GTOP then
    NR_HELPER (fun x1 x2 => decide (x1 > x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LEOP then
    NR_HELPER (fun x1 x2 => decide (x1 <= x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GEOP then
    NR_HELPER (fun x1 x2 => decide (x1 >= x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else result_impossible "Unknown constructor.".

Definition NUMERIC_RELOP_double T1 T2 (id1 : T1 -> double) (id2 : T2 -> double)
    (code : int) ans n n1 n2 read1 read2 ISNA1 ISNA2 :=
  add%stack "NUMERIC_RELOP_double" in
  ifb code = EQOP then
    NR_HELPER (fun x1 x2 => decide (id1 x1 = id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = NEOP then
    NR_HELPER (fun x1 x2 => decide (id1 x1 <> id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LTOP then
    NR_HELPER (fun x1 x2 => decide (id1 x1 < id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GTOP then
    NR_HELPER (fun x1 x2 => decide (id1 x1 > id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = LEOP then
    NR_HELPER (fun x1 x2 => decide (id1 x1 <= id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else ifb code = GEOP then
    NR_HELPER (fun x1 x2 => decide (id1 x1 >= id2 x2)) ans n n1 n2 read1 read2 ISNA1 ISNA2
  else result_impossible "Unknown constructor.".

Definition numeric_relop code s1 s2 :=
  add%stack "numeric_relop" in
  let%success n1 := XLENGTH s1 in
  let%success n2 := XLENGTH s2 in
  let n := ifb n1 > n2 then n1 else n2 in
  let%success ans := allocVector globals LglSxp n in
  let%success s1_in := isInteger globals runs s1 in
  let%success s1_lg := isLogical s1 in
  let%success s2_in := isInteger globals runs s2 in
  let%success s2_lg := isLogical s2 in
  let readINTEGER s i :=
    add%stack "readINTEGER" in
    read%Integer r := s at i in
    result_success r in
  let readREAL s i :=
    add%stack "readREAL" in
    read%Real r := s at i in
    result_success r in
  run%success
    ifb s1_in \/ s1_lg then
      ifb s2_in \/ s2_lg then
        NUMERIC_RELOP_int code ans n n1 n2 (readINTEGER s1) (readINTEGER s2) ISNA_INT ISNA_INT
      else
        NUMERIC_RELOP_double (id : int -> double) id code ans n n1 n2 (readINTEGER s1) (readREAL s2) ISNA_INT ISNAN
    else ifb s2_in \/ s2_lg then
      NUMERIC_RELOP_double id (id : int -> double) code ans n n1 n2 (readREAL s1) (readINTEGER s2) ISNAN ISNA_INT
    else
      NUMERIC_RELOP_double id id code ans n n1 n2 (readREAL s1) (readREAL s2) ISNAN ISNAN in
  result_success ans.

Definition string_relop (code : int) (s1 s2 : SEXP) : result_SEXP :=
  unimplemented_function "string_relop".

Definition complex_relop (code : int) (s1 s2 : SEXP) : result_SEXP :=
  unimplemented_function "complex_relop".

Definition raw_relop (code : int) (s1 s2 : SEXP) : result_SEXP :=
  unimplemented_function "raw_relop".

Definition do_relop_dflt (call op x y : SEXP) : result_SEXP :=
  add%stack "do_relop_dflt" in
  let%success op_val := PRIMVAL runs op in
  run%exit
    if%success IS_SIMPLE_SCALAR globals x IntSxp then
      let%success ix := SCALAR_IVAL x in
      if%success IS_SIMPLE_SCALAR globals y IntSxp then
        let%success iy := SCALAR_IVAL y in
        ifb ix = NA_INTEGER \/ iy = NA_INTEGER then
          result_rreturn (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_int op_val ix iy in
          result_rreturn r
      else if%success IS_SIMPLE_SCALAR globals y RealSxp then
        let%success dy := SCALAR_DVAL y in
        ifb ix = NA_INTEGER \/ ISNAN dy then
          result_rreturn (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double op_val ix dy in
          result_rreturn r
      else result_rskip
    else if%success IS_SIMPLE_SCALAR globals x RealSxp then
      let%success dx := SCALAR_DVAL x in
      if%success IS_SIMPLE_SCALAR globals y IntSxp then
        let%success iy := SCALAR_IVAL y in
        ifb ISNAN dx \/ iy = NA_INTEGER then
          result_rreturn (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double op_val dx iy in
          result_rreturn r
      else if%success IS_SIMPLE_SCALAR globals y RealSxp then
        let%success dy := SCALAR_DVAL y in
        ifb ISNAN dx \/ ISNAN dy then
          result_rreturn (ScalarLogical globals NA_LOGICAL)
        else
          let%success r := DO_SCALAR_RELOP_double op_val dx dy in
          result_rreturn r
      else result_rskip
    else result_rskip in
  let%success nx := xlength globals runs x in
  let%success ny := xlength globals runs y in
  let%success typex := TYPEOF x in
  let%success typey := TYPEOF y in
  let%success x_attrib := ATTRIB x in
  let%success y_attrib := ATTRIB y in
  ifb x_attrib = R_NilValue /\ y_attrib = R_NilValue
      /\ (typex = RealSxp \/ typex = IntSxp)
      /\ (typey = RealSxp \/ typey = IntSxp)
      /\ nx > 0 /\ ny > 0 /\ (nx = 1 \/ ny = 1) then
    numeric_relop op_val x y
  else
    let%success x :=
      let%success iS := isSymbol x in
      let%success x_type := TYPEOF x in
      ifb iS \/ x_type = LangSxp then
        let%success tmp := allocVector globals StrSxp 1 in
        let%success tmp_0 :=
          if iS then
            PRINTNAME x
          else unimplemented_function "deparse1" in
        run%success SET_STRING_ELT tmp 0 tmp_0 in
        result_success tmp
      else result_success x in
    let%success y :=
      let%success iS := isSymbol y in
      let%success y_type := TYPEOF y in
      ifb iS \/ y_type = LangSxp then
        let%success tmp := allocVector globals StrSxp 1 in
        let%success tmp_0 :=
          if iS then
            PRINTNAME y
          else unimplemented_function "deparse1" in
        run%success SET_STRING_ELT tmp 0 tmp_0 in
        result_success tmp
      else result_success y in
    let%success x :=
      if%success isNull x then
        allocVector globals IntSxp 0
      else result_success x in
    let%success y :=
      if%success isNull y then
        allocVector globals IntSxp 0
      else result_success y in
    let%success x_vector := isVector x in
    let%success y_vector := isVector y in
    ifb ~ x_vector \/ ~ y_vector then
      result_error "Comparison is possible only for atomic and list types"
    else
      let%success x_type := TYPEOF x in
      let%success y_type := TYPEOF y in
      ifb x_type = ExprSxp \/ y_type = ExprSxp then
        result_error "Comparison is now allowed for expressions"
      else
        let%success xarray := isArray globals runs x in
        let%success yarray := isArray globals runs y in
        let%success xts := isTs globals runs x in
        let%success yts := isTs globals runs y in
        let%success (dims, xnames, ynames) :=
          ifb xarray \/ yarray then
            let%success dims :=
              ifb xarray /\ yarray then
                let%success conf := conformable globals runs x y in
                if negb conf then
                  result_error "Non-conformable arrays."
                else getAttrib globals runs x R_DimSymbol
              else ifb xarray /\ (ny <> 0 \/ nx = 0) then
                getAttrib globals runs x R_DimSymbol
              else ifb yarray /\ (nx <> 0 \/ ny = 0) then
                getAttrib globals runs y R_DimSymbol
              else result_success (R_NilValue : SEXP) in
            let%success xnames := getAttrib globals runs x R_DimNamesSymbol in
            let%success ynames := getAttrib globals runs y R_DimNamesSymbol in
            result_success (dims, xnames, ynames)
          else
            let%success xnames := getAttrib globals runs x R_NamesSymbol in
            let%success ynames := getAttrib globals runs y R_NamesSymbol in
            result_success (R_NilValue : SEXP, xnames, ynames) in
        let%success (tsp, klass) :=
          ifb xts \/ yts then
            ifb xts /\ yts then
              let%success tsp := getAttrib globals runs x R_TspSymbol in
              let%success klass := getAttrib globals runs x R_ClassSymbol in
              result_success (tsp, klass)
            else
              let%success x_len := xlength globals runs x in
              let%success y_len := xlength globals runs y in
              if xts then
                ifb x_len < y_len then
                  result_error "Time-series/vector length mismatch."
                else
                  let%success tsp := getAttrib globals runs x R_TspSymbol in
                  let%success klass := getAttrib globals runs x R_ClassSymbol in
                  result_success (tsp, klass)
              else
                ifb y_len < x_len then
                  result_error "Time-series/vector length mismatch."
                else
                  let%success tsp := getAttrib globals runs y R_TspSymbol in
                  let%success klass := getAttrib globals runs y R_ClassSymbol in
                  result_success (tsp, klass)
          else result_success (NULL, NULL) in
        let%success x :=
          ifb nx > 0 /\ ny > 0 then
            (* A warning has been formalised out here. *)
            let%success x_str := isString x in
            let%success y_str := isString y in
            ifb x_str \/ y_str then
              let%success x := coerceVector globals runs x StrSxp in
              let%success y := coerceVector globals runs y StrSxp in
              string_relop op_val x y
            else
              let%success x_cplx := isComplex x in
              let%success y_cplx := isComplex y in
              ifb x_cplx \/ y_cplx then
                let%success x := coerceVector globals runs x CplxSxp in
                let%success y := coerceVector globals runs y CplxSxp in
                complex_relop op_val x y
              else
                let%success x_num := isNumeric globals runs x in
                let%success y_num := isNumeric globals runs y in
                let%success x_lgl := isLogical x in
                let%success y_lgl := isLogical y in
                ifb (x_num \/ x_lgl) /\ (y_num \/ y_lgl) then
                  numeric_relop op_val x y
                else
                  let%success x_real := isReal x in
                  let%success y_real := isReal y in
                  ifb x_real \/ y_real then
                    let%success x := coerceVector globals runs x RealSxp in
                    let%success y := coerceVector globals runs y RealSxp in
                    numeric_relop op_val x y
                  else
                    let%success x_int := isInteger globals runs x in
                    let%success y_int := isInteger globals runs y in
                    ifb x_int \/ y_int then
                      let%success x := coerceVector globals runs x IntSxp in
                      let%success y := coerceVector globals runs y IntSxp in
                      numeric_relop op_val x y
                    else ifb x_lgl \/ y_lgl then
                      let%success x := coerceVector globals runs x LglSxp in
                      let%success y := coerceVector globals runs y LglSxp in
                      numeric_relop op_val x y
                    else ifb x_type = RawSxp \/ y_type = RawSxp then
                      let%success x := coerceVector globals runs x RawSxp in
                      let%success y := coerceVector globals runs y RawSxp in
                      raw_relop op_val x y
                    else result_error "Comparison of these types is not implemented."
          else allocVector globals LglSxp 0 in
        run%success
          ifb dims <> R_NilValue then
            run%success setAttrib globals runs x R_DimSymbol dims in
            ifb xnames <> R_NilValue then
              run%success setAttrib globals runs x R_DimNamesSymbol xnames in
              result_skip
            else ifb ynames <> R_NilValue then
              run%success setAttrib globals runs x R_DimNamesSymbol ynames in
              result_skip
            else result_skip
          else
            let%success x_len := xlength globals runs x in
            let%success xnames_len := xlength globals runs xnames in
            ifb xnames <> R_NilValue /\ x_len = xnames_len then
              run%success setAttrib globals runs x R_NamesSymbol xnames in
              result_skip
            else
              let%success ynames_len := xlength globals runs ynames in
              ifb ynames <> R_NilValue /\ x_len = ynames_len then
                run%success setAttrib globals runs x R_NamesSymbol ynames in
                result_skip
              else result_skip in
        run%success
          ifb xts \/ yts then
            run%success setAttrib globals runs x R_TspSymbol tsp in
            run%success setAttrib globals runs x R_ClassSymbol klass in
            result_skip
          else result_skip in
        result_success x.

Definition do_relop (call op args env : SEXP) : result_SEXP :=
  add%stack "do_relop" in
  read%list args_car, args_cdr, _ := args in
  read%list args_cdr_car, args_cdr_cdr, _ := args_cdr in
  let%success argc :=
    ifb args <> R_NilValue then
      ifb args_cdr <> R_NilValue then
        ifb args_cdr_cdr = R_NilValue then
          result_success 2
        else R_length globals runs args
      else R_length globals runs args
   else R_length globals runs args in
  let arg1 := args_car in
  let arg2 := args_cdr_car in
  let%success arg1_attrib := ATTRIB arg1 in
  let%success arg2_attrib := ATTRIB arg1 in
  run%exit
    ifb arg1_attrib <> R_NilValue \/ arg2_attrib <> R_NilValue then
      if%defined ans := DispatchGroup globals runs "Ops" call op args env then
        result_rreturn ans
      else result_rskip
    else result_rskip in
  ifb argc <> 2 then
    result_error "Operator needs two arguments."
  else do_relop_dflt call op arg1 arg2.

End Parameters.

