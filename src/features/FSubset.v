(** Features.FSubset.
  The function names of this file correspond to the function names
  in the file main/subset.c. **)

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
Require Import FUtil.
Require Import FArithmetic.
Require Import FArray.

Section Parameters.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Local Coercion Pos.to_nat : positive >-> nat.
Local Coercion int_to_double : Z >-> double.


Definition CHKZLN S x :=
  add%stack "CHKZLN" in
    let%success x_length := STDVEC_LENGTH S x using S in
    let%success x_type := TYPEOF S x using S in
    ifb x_length = 0 /\ x_type <> CharSxp then
        result_error S "attempting to read/write elements of a zero-length vector"
    else
        result_skip S.

(* Slightly modified version of INTEGER_RO. It just checks types and length 
   of vector and returns the vector itself, instead of returning the vector 
   data. Therefore, after checking, one should do 'read%Integer' directly on 
   the vector *)
Definition INTEGER_RO S x :=
  add%stack "INTEGER_RO" in
    let%success x_type := TYPEOF S x using S in
    ifb x_type <> IntSxp /\ x_type <> LglSxp then
        result_error S "INTEGER can only be applied to an integer"
    else
    CHKZLN S x.
                     
Definition pstrmatch S (target input : SEXP) slen :=
  add%stack "pstrmatch" in
  ifb target = R_NilValue then
    result_success S NO_MATCH
  else
    let%success target_type := TYPEOF S target using S in
    let%success st :=
      match target_type with
      | SymSxp =>
        let%success target_name := PRINTNAME S target using S in
        CHAR S target_name
      | CharSxp =>
        translateChar S target
      | _ => result_impossible S "Invalid type."
      end using S in
    let%success si := translateChar S input using S in
    let si_0 := LibOption.unsome_default "000"%char (String.get 0 si) in
    ifb si_0 <> "000"%char /\ substring 0 slen st = substring 0 slen si then
      result_success S (ifb String.length st = slen then EXACT_MATCH else PARTIAL_MATCH)
    else result_success S NO_MATCH.

Definition R_DispatchOrEvalSP S call op generic args rho :=
  add%stack "R_DispatchOrEvalSP" in
  read%list args_car, args_cdr, _ := args using S in
  let%exit (prom, args) :=
    ifb args <> R_NilValue /\ args_car <> R_DotsSymbol then
      let%success x := eval globals runs S args_car rho using S in
      run%success INCREMENT_LINKS S x using S in
      let%success x_obj := OBJECT S x using S in
      if negb x_obj then
        let%success elkm :=
          evalListKeepMissing globals runs S args_cdr rho using S in
        let (S, ans) := CONS_NR globals S x elkm in
        run%success DECREMENT_LINKS S x using S in
        result_rreturn S (false, ans)
      else unimplemented_function "R_mkEVPROMISE_NR"
    else result_rsuccess S (NULL, args) using S in
  let%success (disp, ans) :=
    DispatchOrEval globals runs S call op generic args rho false false using S in
  run%success
    ifb prom <> NULL then
      let%success prom_value := PRVALUE S prom using S in
      DECREMENT_LINKS S prom_value
    else result_skip S using S in
  result_success S (disp, ans).

Definition scalarIndex S s :=
  add%stack "scalarIndex" in
  let%success s_attr := ATTRIB S s using S in
  ifb s_attr = R_NilValue then
    if%success IS_SCALAR S s IntSxp using S then
      let%success ival := SCALAR_IVAL S s using S in
      ifb ival <> NA_INTEGER then
        result_success S ival
      else result_success S (-1)%Z
    else if%success IS_SCALAR S s RealSxp using S then
      let%success rval := SCALAR_DVAL S s using S in
      if R_FINITE rval then
        result_success S (Double.double_to_int_zero rval)
      else result_success S (-1)%Z
    else result_success S (-1)%Z
  else result_success S (-1)%Z.

Definition ExtractArg S args arg_sym :=
  add%stack "ExtractArg" in
  fold%return prev_arg := args
  along args
  as arg, _, arg_list do
    ifb list_tagval arg_list = arg_sym then
      run%success
        ifb arg = prev_arg then
          result_skip S
        else
          set%cdr prev_arg := list_cdrval arg_list using S in
          result_skip S using S in
      result_rreturn S (list_carval arg_list)
    else result_rsuccess S arg using S, runs, globals in
  result_success S (R_NilValue : SEXP).

Definition ExtractDropArg S el :=
  add%stack "ExtractDropArg" in
  let%success dropArg := ExtractArg S el R_DropSymbol using S in
  let%success drop := asLogical globals S dropArg using S in
  ifb drop = NA_LOGICAL then
    result_success S true
  else result_success S (decide (drop <> 0)).

              
Definition ExtractSubset S (x indx call : SEXP) :=
  add%stack "ExtractSubset" in
    ifb x = R_NilValue then
        result_success S x
    else

    if%success ALTREP S x using S then
        unimplemented_function "ALTVEC_EXTRACT_SUBSET"
    else

    let%success n := XLENGTH S indx using S in
    let%success nx := xlength globals runs S x using S in
    let%success mode := TYPEOF S x using S in

    let%success result := allocVector globals S mode n using S in
    run%success
    match mode with
    | LglSxp =>
      let%success indx_type := TYPEOF S indx using S in
      ifb indx_type = IntSxp then
        run%success INTEGER_RO S indx using S in
        do%success
        for i from 0 to n - 1 do   
            read%Integer ii := indx at i using S in                  
            ifb 0%Z < ii /\ ii <= nx then
                let ii := Z.to_nat ii - 1 in
                let%success x_ii := LOGICAL_ELT S x ii using S in
                write%Logical result at i := x_ii using S in result_skip S
            else (* out of bounds or NA *)
                write%Logical result at i := NA_INTEGER using S in result_skip S
        using S in result_skip S
      else
        do%success
        for i from 0 to n - 1 do
            read%Real di := indx at i using S in
            let ii := (Z.to_nat (Double.double_to_int_zero di) - 1) : int in
            ifb R_FINITE di /\ 0%Z <= ii /\ ii < nx then
                let%success x_ii := LOGICAL_ELT S x (Z.to_nat ii) using S in
                write%Logical result at i := x_ii using S in result_skip S
            else
                write%Logical result at i := NA_INTEGER using S in result_skip S
        using S in result_skip S
                            
    | IntSxp =>
      let%success indx_type := TYPEOF S indx using S in
      ifb indx_type = IntSxp then
        run%success INTEGER_RO S indx using S in
        do%success
        for i from 0 to n - 1 do   
            read%Integer ii := indx at i using S in                  
            ifb 0%Z < ii /\ ii <= nx then
                let ii := Z.to_nat ii - 1 in
                let%success x_ii := INTEGER_ELT S x ii using S in
                write%Integer result at i := x_ii using S in result_skip S
            else (* out of bounds or NA *)
                write%Integer result at i := NA_INTEGER using S in result_skip S
        using S in result_skip S
      else
        do%success
        for i from 0 to n - 1 do
            read%Real di := indx at i using S in
            let ii := (Z.to_nat (Double.double_to_int_zero di) - 1) : int in
            ifb R_FINITE di /\ 0%Z <= ii /\ ii < nx then
                let%success x_ii := INTEGER_ELT S x (Z.to_nat ii) using S in
                write%Integer result at i := x_ii using S in result_skip S
            else
                write%Integer result at i := NA_INTEGER using S in result_skip S
        using S in result_skip S

    | RealSxp =>
      let%success indx_type := TYPEOF S indx using S in
      ifb indx_type = IntSxp then
        run%success INTEGER_RO S indx using S in
        do%success
        for i from 0 to n - 1 do   
            read%Integer ii := indx at i using S in                  
            ifb 0%Z < ii /\ ii <= nx then
                let ii := Z.to_nat ii - 1 in
                let%success x_ii := REAL_ELT S x ii using S in
                write%Real result at i := x_ii using S in result_skip S
            else (* out of bounds or NA *)
                write%Real result at i := NA_REAL using S in result_skip S
        using S in result_skip S
    else
        do%success
        for i from 0 to n - 1 do
            read%Real di := indx at i using S in
            let ii := (Z.to_nat (Double.double_to_int_zero di) - 1) : int in
            ifb R_FINITE di /\ 0%Z <= ii /\ ii < nx then
                let%success x_ii := REAL_ELT S x (Z.to_nat ii) using S in
                write%Real result at i := x_ii using S in result_skip S
            else
                 write%Real result at i := NA_REAL using S in result_skip S
        using S in result_skip S
     
    | CplxSxp => result_not_implemented "Complex case"
    | StrSxp =>
      let%success indx_type := TYPEOF S indx using S in
      ifb indx_type = IntSxp then
        run%success INTEGER_RO S indx using S in
        do%success
        for i from 0 to n - 1 do   
            read%Integer ii := indx at i using S in                  
            ifb 0%Z < ii /\ ii <= nx then
                let ii := Z.to_nat ii - 1 in
                let%success x_ii := STRING_ELT S x ii using S in
                SET_STRING_ELT S result i x_ii
            else (* out of bounds or NA *)
                SET_STRING_ELT S result i NA_STRING
        using S in result_skip S
      else
        do%success
        for i from 0 to n - 1 do
            read%Real di := indx at i using S in
            let ii := (Z.to_nat (Double.double_to_int_zero di) - 1) : int in
            ifb R_FINITE di /\ 0%Z <= ii /\ ii < nx then
                let%success x_ii := STRING_ELT S x (Z.to_nat ii) using S in
                SET_STRING_ELT S result i x_ii
            else
                SET_STRING_ELT S result i NA_STRING
        using S in result_skip S
      
    | VecSxp
    | ExprSxp => result_not_implemented "Expr case"
    | RawSxp => result_not_implemented "raw case"
    | ListSxp => result_impossible S "cannot happen: pairlists are coerced to lists"
    | LangSxp => result_impossible S "cannot happen: LANGSXPs are coerced to lists"
    | _ => result_error S "wrong type to extract"
    end
    using S in
    result_success S result.

Definition VectorSubset S (x s call : SEXP) :=
  add%stack "VectorSubset" in
  let stretch := 1 in
  ifb s = R_MissingArg then
    duplicate globals runs S x
  else
    let%success attrib := getAttrib globals runs S x R_DimSymbol using S in

    (* Check to see if we have special matrix subscripting. */
    /* If we do, make a real subscript vector and protect it. *)

    let%success s :=
      let%success s_mat := isMatrix globals runs S s using S in
      let%success x_arr := isArray globals runs S x using S in
      ifb s_mat /\ x_arr then
        let%success s_cols := ncols globals runs S s using S in
        let%success attrib_len := R_length globals runs S attrib using S in
        ifb s_cols = attrib_len then
          let%success s :=
            if%success isString S s using S then
              unimplemented_function "strmat2intmat"
            else result_success S s using S in
          let%success s_int := isInteger globals runs S s using S in
          let%success s_real := isReal S s using S in
          ifb s_int \/ s_real then
            unimplemented_function "mat2indsub"
          else result_success S s
        else result_success S s
      else result_success S s using S in

    (* Convert to a vector of integer subscripts */
    /* in the range 1:length(x). *)

    let%success (indx, stretch) := makeSubscript globals runs S x s stretch call using S in

    (* Allocate the result. *)
    
    let%success mode := TYPEOF S x using S in
    let%success result := ExtractSubset S x indx call using S in
    run%success
    ifb mode = VecSxp \/ mode = ExprSxp then
      set%named result := named_plural using S in result_skip S
    else result_skip S
    using S in  

    let%success result :=
    ifb result <> R_NilValue then
      let%success result :=
      let%success attrib := getAttrib globals runs S x R_NamesSymbol using S in
      ifb attrib <> R_NilValue then
        let%success nattrib := ExtractSubset S attrib indx call using S in
        setAttrib globals runs S result R_NamesSymbol nattrib  
      else
        let%success x_isArray := isArray globals runs S x using S in
        let%success x_attrib := getAttrib globals runs S x R_DimNamesSymbol using S in
        let%success x_attrib_length := R_length globals runs S x_attrib using S in
        let attrib := x_attrib in
        let%success attrib :=
           ifb attrib <> R_NilValue then GetRowNames globals S attrib
           else result_success S (R_NilValue : SEXP) using S in
        ifb x_isArray /\ x_attrib_length = 1 /\ attrib <> R_NilValue then
          let%success nattrib := ExtractSubset S attrib indx call using S in
          setAttrib globals runs S result R_NamesSymbol nattrib  
        else
          result_success S result
      using S in
      let%success attrib := getAttrib globals runs S x R_SrcrefSymbol using S in
      let%success attrib_type := TYPEOF S attrib using S in
      ifb attrib <> R_NilValue /\ attrib_type = VecSxp then
         let%success nattrib := ExtractSubset S attrib indx call using S in
         setAttrib globals runs S result R_SrcrefSymbol nattrib 
      else
        result_success S result
    else
      result_success S result
    using S in
  result_success S result.

Definition do_subset_dflt S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subset_dflt" in
  read%list args_car, args_cdr, _ := args using S in
  let cdrArgs := args_cdr in
  read%list cdrArgs_car, cdrArgs_cdr, cdrArgs_tag := cdrArgs using S in
  let cddrArgs := cdrArgs_cdr in
  read%list cddrArgs_car, cddrArgs_cdr, cddrArgs_tag := cddrArgs using S in
  run%exit
    ifb cdrArgs <> R_NilValue /\ cddrArgs = R_NilValue /\ cdrArgs_tag = R_NilValue then
      let x := args_car in
      let%success x_attr := ATTRIB S x using S in
      ifb x_attr = R_NilValue then
        let s := cdrArgs_car in
        let%success i := scalarIndex S s using S in
        let%success x_type := TYPEOF S x using S in
        match x_type with
        | RealSxp =>
          let%success len := XLENGTH S x using S in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := REAL_ELT S x (Z.to_nat (i - 1)) using S in
            let (S, r) := ScalarReal globals S x_imu in
            result_rreturn S r
          else result_rskip S
        | IntSxp =>
          let%success len := XLENGTH S x using S in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := INTEGER_ELT S x (Z.to_nat (i - 1)) using S in
            let (S, r) := ScalarInteger globals S x_imu in
            result_rreturn S r
          else result_rskip S
        | LglSxp =>
          let%success len := XLENGTH S x using S in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := LOGICAL_ELT S x (Z.to_nat (i - 1)) using S in
            result_rreturn S (ScalarLogical globals x_imu)
          else result_rskip S
        | CplxSxp =>
          let%success len := XLENGTH S x using S in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := COMPLEX_ELT S x (Z.to_nat (i - 1)) using S in
            let (S, r) := ScalarComplex globals S x_imu in
            result_rreturn S r
          else result_rskip S
        | RawSxp => result_not_implemented "Raw case."
        | _ => result_rskip S
        end
      else result_rskip S
    else ifb cddrArgs <> R_NilValue /\ cddrArgs_cdr = R_NilValue
          /\ cdrArgs_tag = R_NilValue /\ cddrArgs_tag = R_NilValue then
      let x := args_car in
      let%success attr := ATTRIB S x using S in
      read%list attr_car, attr_cdr, attr_tag := attr using S in
      ifb attr_tag = R_DimSymbol /\ attr_cdr = R_NilValue then
        let dim := attr_car in
        let%success dim_type := TYPEOF S dim using S in
        let%success dim_len := LENGTH globals S dim using S in
        ifb dim_type = IntSxp /\ dim_len = 2 then
          let si := cdrArgs_car in
          let sj := cddrArgs_car in
          let%success i := scalarIndex S si using S in
          let%success j := scalarIndex S sj using S in
          let%success nrow := INTEGER_ELT S dim 0 using S in
          let%success ncol := INTEGER_ELT S dim 1 using S in
          ifb i > 0 /\ j > 0 /\ i <= nrow /\ j <= ncol then
            let k := Z.to_nat (i - 1 + nrow * (j - 1))%Z in
            let%success x_type := TYPEOF S x using S in
            match x_type with
            | RealSxp =>
              let%success len := XLENGTH S x using S in
              ifb k <= len then
                let%success x_k := REAL_ELT S x k using S in
                let (S, r) := ScalarReal globals S x_k in
                result_rreturn S r
              else result_rskip S
            | IntSxp =>
              let%success len := XLENGTH S x using S in
              ifb k <= len then
                let%success x_k := INTEGER_ELT S x k using S in
                let (S, r) := ScalarInteger globals S x_k in
                result_rreturn S r
              else result_rskip S
            | LglSxp =>
              let%success len := XLENGTH S x using S in
              ifb k <= len then
                let%success x_k := LOGICAL_ELT S x k using S in
                result_rreturn S (ScalarLogical globals x_k)
              else result_rskip S
            | CplxSxp =>
              let%success len := XLENGTH S x using S in
              ifb k <= len then
                let%success x_k := COMPLEX_ELT S x k using S in
                let (S, r) := ScalarComplex globals S x_k in
                result_rreturn S r
              else result_rskip S
            | RawSxp => result_not_implemented "Raw case."
            | _ => result_rskip S
            end
          else result_rskip S
        else result_rskip S
      else result_rskip S
    else result_rskip S using S in
  let%success drop := ExtractDropArg S args using S in
  let x := args_car in
  ifb x = R_NilValue then
    result_success S x
  else
    let subs := args_cdr in
    let%success nsubs := R_length globals runs S subs using S in
    let%success type := TYPEOF S x using S in
    let%success ax :=
      if%success isVector S x using S then
        result_success S x
      else if%success isPairList S x using S then
        let%success dim := getAttrib globals runs S x R_DimSymbol using S in
        let%success ndim := R_length globals runs S dim using S in
        let%success ax :=
          ifb ndim > 1 then
            let%success ax := allocArray globals runs S VecSxp dim using S in
            let%success x_dimnames := getAttrib globals runs S x R_DimNamesSymbol using S in
            run%success setAttrib globals runs S ax R_DimNamesSymbol x_dimnames using S in
            run%success setAttrib globals runs S ax R_NamesSymbol x_dimnames using S in
            result_success S ax
          else
            let%success x_len := R_length globals runs S x using S in
            let%success ax := allocVector globals S VecSxp x_len using S in
            let%success x_names := getAttrib globals runs S x R_NamesSymbol using S in
            run%success setAttrib globals runs S ax R_NamesSymbol x_names using S in
            result_success S ax using S in
        fold%success i := 0
        along x
        as x_car, _ do
          run%success SET_VECTOR_ELT S ax i x_car using S in
          result_success S (1 + i) using S, runs, globals in
        result_success S ax
      else result_error S "Object is not subsettable." using S in

    (* This is the actual subsetting code. */
    /* The separation of arrays and matrices is purely an optimization. *)

    let%success ans :=
      ifb nsubs < 2 then
        let%success dim := getAttrib globals runs S x R_DimSymbol using S in
        let%success ndim := R_length globals runs S dim using S in
        read%list subs_car, _, _ := subs using S in
        let%success ans := VectorSubset S ax (ifb nsubs = 1 then subs_car else R_MissingArg) call using S in
        run%success
          ifb ndim = 1 then
            let%success len := R_length globals runs S ans using S in
            ifb ~ drop \/ len > 1 then
              let%success nm := getAttrib globals runs S ans R_NamesSymbol using S in
              let (S, attr) := ScalarInteger globals S len in
              run%success
                let%success dim_names := getAttrib globals runs S dim R_NamesSymbol using S in
                let%success dim_names_null := isNull S dim_names using S in
                if negb dim_names_null then
                  run%success setAttrib globals runs S attr R_NamesSymbol dim_names using S in
                  result_skip S
                else result_skip S using S in
              run%success setAttrib globals runs S ans R_DimSymbol attr using S in
              let%success attrib := getAttrib globals runs S x R_DimNamesSymbol using S in
              ifb attrib <> R_NilValue then
                let%success nattrib := duplicate globals runs S attrib using S in
                run%success SET_VECTOR_ELT S nattrib 0 nm using S in
                run%success setAttrib globals runs S ans R_DimNamesSymbol nattrib using S in
                run%success setAttrib globals runs S ans R_NamesSymbol R_NilValue using S in
                result_skip S
              else result_skip S
            else result_skip S
          else result_skip S using S in
        result_success S ans
      else
        let%success x_dim := getAttrib globals runs S x R_DimSymbol using S in
        let%success x_dim_len := R_length globals runs S x_dim using S in
        ifb nsubs <> x_dim_len then
          result_error S "Incorrect number of dimensions."
        else ifb nsubs = 2 then
          unimplemented_function "MatrixSubset"
        else unimplemented_function "ArraySubset" using S in
    let%success ans :=
      ifb type = LangSxp then
        let ax := ans in
        let%success ax_len := LENGTH globals S ax using S in
        let (S, ans) := allocList globals S ax_len in
        run%success
          ifb ax_len > 0 then
            set%type ans := LangSxp using S in
            fold%success i := 0
            along ans
            as px, _, _ do
              let%success ax_i := VECTOR_ELT S ax i using S in
              set%car px := ax_i using S in
              result_success S (1 + i) using S, runs, globals in
            run%success
              let%success ax_dim := getAttrib globals runs S ax R_DimSymbol using S in
              setAttrib globals runs S ans R_DimSymbol ax_dim using S in
            run%success
              let%success ax_dimn := getAttrib globals runs S ax R_DimNamesSymbol using S in
              setAttrib globals runs S ans R_DimNamesSymbol ax_dimn using S in
            run%success
              let%success ax_names := getAttrib globals runs S ax R_NamesSymbol using S in
              setAttrib globals runs S ans R_NamesSymbol ax_names using S in
            run%success
              let%success ax_named := NAMED S ax using S in
              RAISE_NAMED S ans ax_named using S in
            result_skip S
          else result_skip S using S in
        result_success S ans
      else result_success S ans using S in
    run%success
      let%success ans_attr := ATTRIB S ans using S in
      ifb ans_attr <> R_NilValue then
        run%success setAttrib globals runs S ans R_TspSymbol R_NilValue using S in
        run%success setAttrib globals runs S ans R_ClassSymbol R_NilValue using S in
        result_skip S
      else result_skip S using S in
    result_success S ans.

Definition do_subset S (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subset" in
  let%success (disp, ans) := R_DispatchOrEvalSP S call op "[" args rho using S in
  if disp then
    run%success
      let%success ans_named := NAMED S ans using S in
      ifb ans_named <> named_temporary then
        set%named ans := named_plural using S in
        result_skip S
      else result_skip S using S in
    result_success S ans
  else do_subset_dflt S call op ans rho.

Definition R_subset3_dflt (S : state) (x input call : SEXP) : result SEXP :=
  add%stack "R_subset3_dflt" in
    let%success input_translate := translateChar S input using S in
    let slen := String.length input_translate in

    let%success x_s4 := IS_S4_OBJECT S x using S in
    let%success x_type := TYPEOF S x using S in
    let%success x :=
    ifb x_s4 /\ x_type = S4Sxp then
      let%success x := unimplemented_function "R_getS4DataSlot" : result SEXP using S in
      ifb x = R_NilValue then
        result_error S "$ operator not defined for this S4 class."
      else
        result_success S x
    else result_success S x using S in

    if%success isPairList S x using S then
      fold%return (xmatch, havematch) := (R_NilValue : SEXP, 0) along x as y, _, y_list do
        let y_tag := list_tagval y_list in
        let y_car := list_carval y_list in

        let%success pstr := pstrmatch S y_tag input slen using S in
          match pstr with
            | EXACT_MATCH =>  let y := y_car in
                              let%success x_named := NAMED S x using S in
                              run%success RAISE_NAMED S y x_named using S in
                                result_rreturn S y
            | PARTIAL_MATCH => result_rsuccess S (y, 1 + havematch)
            | NO_MATCH => result_rsuccess S (xmatch, havematch)
          end using S, runs, globals in

        ifb havematch = 1 then
        (* A warning has been formalised out here. *)
          read%list xmatch_car, _, _ := xmatch using S in
          let y := xmatch_car in
          let%success x_named := NAMED S x using S in
          run%success RAISE_NAMED S y x_named using S in
            result_success S y
        else
          result_success S (R_NilValue : SEXP)
    else if%success isVectorList S x using S then
      let%success nlist := getAttrib globals runs S x R_NamesSymbol using S in

      let%success n := xlength globals runs S x using S in
      do%exit (imatch, havematch) := ((-1)%Z, 0)
      for i from 0 to n - 1 do
        let%success nlist_i := STRING_ELT S nlist i using S in
        let%success pstr := pstrmatch S nlist_i input slen using S in
        match pstr with
         | EXACT_MATCH => let%success y := VECTOR_ELT S x i using S in
                          let%success x_named := NAMED S x using S in
                          run%success RAISE_NAMED S y x_named using S in
                          result_rreturn S y
         | PARTIAL_MATCH => let havematch := havematch + 1 in
                            ifb havematch = 1 then
                              let%success y := VECTOR_ELT S x i using S in
                              set%named y := named_plural using S in
                              run%success SET_VECTOR_ELT S x i y using S in
                              result_rsuccess S (i : int, havematch)
                            else
                              result_rsuccess S (i : int, havematch)
         | NO_MATCH => result_rsuccess S (imatch, havematch)
        end
      using S in
      ifb havematch = 1 then
      (* A warning has been formalised out here. *)
        let%success y := VECTOR_ELT S x (Z.to_nat imatch) using S in
        let%success x_named := NAMED S x using S in
        run%success RAISE_NAMED S y x_named using S in
        result_success S y
      else
        result_success S (R_NilValue : SEXP)
    else if%success isEnvironment S x using S then
      let%success input_install := installTrChar globals runs S input using S in
      let%success y := findVarInFrame globals runs S x input_install using S in
      let%success y_type := TYPEOF S y using S in
      let%success y :=
        ifb y_type = PromSxp then
          eval globals runs S y R_GlobalEnv
        else result_success S y using S in
      ifb y <> R_UnboundValue then
        run%success
          let%success y_named := NAMED S y using S in
          ifb y_named <> named_temporary then
            set%named y := named_plural using S in
            result_skip S
          else
            let%success x_named := NAMED S x using S in
            RAISE_NAMED S y x_named using S in
        result_success S y
      else result_success S (R_NilValue : SEXP)
    else if%success isVectorAtomic S x using S then
      result_error S "$ operator is invalid for atomic vectors."
    else result_error S "This object is not subsettable.".

(* We choose not to formalise the last argument [syminp] in the following function. *)
Definition fixSubset3Args S (call args env : SEXP) :=
  add%stack "fixSubset3args" in
    let%success input := allocVector globals S StrSxp 1 using S in
    read%list _, args_cdr, _ := args using S in
    read%list args_cdr_car, _, _ := args_cdr using S in
    let nlist := args_cdr_car in
    let%success nlist_type := TYPEOF S nlist using S in
    let%success nlist :=  ifb nlist_type = PromSxp then
                            eval globals runs S nlist env
                          else result_success S nlist using S in

    run%success
    if%success isSymbol S nlist using S then
      let%success nlist_name := PRINTNAME S nlist using S in
      SET_STRING_ELT S input 0 nlist_name
    else if%success isString S nlist using S then
      let%success nlist0 := STRING_ELT S nlist 0 using S in
      SET_STRING_ELT S input 0 nlist0
    else result_error S "invalid subscript" using S in

    let%success args := shallow_duplicate globals runs S args using S in
    read%list _, args_cdr, _ := args using S in
    set%car args_cdr := input using S in
    result_success S args.


Definition do_subset3 S (call op args env : SEXP) : result SEXP :=
  add%stack "do_subset3" in
    run%success Rf_checkArityCall globals runs S op args call using S in
    let%success args := fixSubset3Args S call args env using S in

    let%success (disp, ans) := R_DispatchOrEvalSP S call op "$" args env using S in
    if disp then
      run%success
      let%success ans_named := NAMED S ans using S in
      ifb ans_named <> named_temporary then
        set%named ans := named_plural using S in
        result_skip S
      else result_skip S using S in
        result_success S ans
    else
      read%list ans_car, _, _ := ans using S in
      read%list _, args_cdr, _ := args using S in
      read%list args_cdr_car, _, _ := args_cdr using S in

      let%success args_cdr_car_0 := STRING_ELT S args_cdr_car 0 using S in
      let%success ans := R_subset3_dflt S ans_car  args_cdr_car_0 call using S in
      result_success S ans.

End Parameters.

