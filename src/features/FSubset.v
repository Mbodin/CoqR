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


Definition CHKZLN x :=
  add%stack "CHKZLN" in
    let%success x_length := STDVEC_LENGTH x in
    let%success x_type := TYPEOF x in
    ifb x_length = 0 /\ x_type <> CharSxp then
        result_error "attempting to read/write elements of a zero-length vector"
    else
        result_skip.

(* Slightly modified version of INTEGER_RO. It just checks types and length 
   of vector and returns the vector itself, instead of returning the vector 
   data. Therefore, after checking, one should do 'read%Integer' directly on 
   the vector *)
Definition INTEGER_RO x :=
  add%stack "INTEGER_RO" in
    let%success x_type := TYPEOF x in
    ifb x_type <> IntSxp /\ x_type <> LglSxp then
        result_error "INTEGER can only be applied to an integer"
    else
    CHKZLN x.
                     
Definition pstrmatch (target input : SEXP) slen :=
  add%stack "pstrmatch" in
  ifb target = R_NilValue then
    result_success NO_MATCH
  else
    let%success target_type := TYPEOF target in
    let%success st :=
      match target_type with
      | SymSxp =>
        let%success target_name := PRINTNAME target in
        CHAR target_name
      | CharSxp =>
        translateChar target
      | _ => result_impossible "Invalid type."
      end in
    let%success si := translateChar input in
    let si_0 := LibOption.unsome_default "000"%char (String.get 0 si) in
    ifb si_0 <> "000"%char /\ substring 0 slen st = substring 0 slen si then
      result_success (ifb String.length st = slen then EXACT_MATCH else PARTIAL_MATCH)
    else result_success NO_MATCH.

Definition R_DispatchOrEvalSP call op generic args rho :=
  add%stack "R_DispatchOrEvalSP" in
  read%list args_car, args_cdr, _ := args in
  let%exit (prom, args) :=
    ifb args <> R_NilValue /\ args_car <> R_DotsSymbol then
      let%success x := eval globals runs args_car rho in
      run%success INCREMENT_LINKS x in
      let%success x_obj := OBJECT x in
      if negb x_obj then
        let%success elkm :=
          evalListKeepMissing globals runs args_cdr rho in
        let%success ans := CONS_NR globals x elkm in
        run%success DECREMENT_LINKS x in
        result_rreturn (false, ans)
      else unimplemented_function "R_mkEVPROMISE_NR"
    else result_rsuccess (NULL, args) in
  let%success (disp, ans) :=
    DispatchOrEval globals runs call op generic args rho false false in
  run%success
    ifb prom <> NULL then
      let%success prom_value := PRVALUE prom in
      DECREMENT_LINKS prom_value
    else result_skip in
  result_success (disp, ans).

Definition scalarIndex s :=
  add%stack "scalarIndex" in
  let%success s_attr := ATTRIB s in
  ifb s_attr = R_NilValue then
    if%success IS_SCALAR s IntSxp then
      let%success ival := SCALAR_IVAL s in
      ifb ival <> NA_INTEGER then
        result_success ival
      else result_success (-1)%Z
    else if%success IS_SCALAR s RealSxp then
      let%success rval := SCALAR_DVAL s in
      if R_FINITE rval then
        result_success (Double.double_to_int_zero rval)
      else result_success (-1)%Z
    else result_success (-1)%Z
  else result_success (-1)%Z.

Definition ExtractArg args arg_sym :=
  add%stack "ExtractArg" in
  fold%return prev_arg := args
  along args
  as arg, _, arg_list do
    ifb list_tagval arg_list = arg_sym then
      run%success
        ifb arg = prev_arg then
          result_skip
        else
          set%cdr prev_arg := list_cdrval arg_list in
          result_skip in
      result_rreturn (list_carval arg_list)
    else result_rsuccess arg using runs, globals in
  result_success (R_NilValue : SEXP).

Definition ExtractDropArg el :=
  add%stack "ExtractDropArg" in
  let%success dropArg := ExtractArg el R_DropSymbol in
  let%success drop := asLogical globals dropArg in
  ifb drop = NA_LOGICAL then
    result_success true
  else result_success (decide (drop <> 0)).


(* Modified version, warnings are not implemented, therefore using true and false
   Extracts and, if present, removes the 'exact' argument from the
   argument list.  An integer code giving the desired exact matching
   behavior is returned:
       false  not exact
       true  exact
 *)
Definition ExtractExactArg args :=
  add%stack "ExtractExactArg" in
    let%success argval := ExtractArg args R_ExactSymbol in 
    let%success argval_isNull := isNull argval in
    if argval_isNull then
        result_success true
    else
    let%success exact := asLogical globals argval in
    ifb exact = NA_LOGICAL then
        result_success false
    else
        result_success (decide (exact <> 0)).


    
Definition ExtractSubset (x indx call : SEXP) :=
  add%stack "ExtractSubset" in
    ifb x = R_NilValue then
        result_success x
    else

    if%success ALTREP x then
        unimplemented_function "ALTVEC_EXTRACT_SUBSET"
    else

    let%success n := XLENGTH indx in
    let%success nx := xlength globals runs x in
    let%success mode := TYPEOF x in

    let%success result := allocVector globals mode n in
    run%success
    match mode with
    | LglSxp =>
      let%success indx_type := TYPEOF indx in
      ifb indx_type = IntSxp then
        run%success INTEGER_RO indx in
        do%success
        for i from 0 to n - 1 do   
            read%Integer ii := indx at i in                  
            ifb 0%Z < ii /\ ii <= nx then
                let ii := Z.to_nat ii - 1 in
                let%success x_ii := LOGICAL_ELT x ii in
                write%Logical result at i := x_ii in result_skip
            else (* out of bounds or NA *)
                write%Logical result at i := NA_INTEGER in result_skip
        in result_skip
      else
        do%success
        for i from 0 to n - 1 do
            read%Real di := indx at i in
            let ii := (Z.to_nat (Double.double_to_int_zero di) - 1) : int in
            ifb R_FINITE di /\ 0%Z <= ii /\ ii < nx then
                let%success x_ii := LOGICAL_ELT x (Z.to_nat ii) in
                write%Logical result at i := x_ii in result_skip
            else
                write%Logical result at i := NA_INTEGER in result_skip
        in result_skip
                            
    | IntSxp =>
      let%success indx_type := TYPEOF indx in
      ifb indx_type = IntSxp then
        run%success INTEGER_RO indx in
        do%success
        for i from 0 to n - 1 do   
            read%Integer ii := indx at i in                  
            ifb 0%Z < ii /\ ii <= nx then
                let ii := Z.to_nat ii - 1 in
                let%success x_ii := INTEGER_ELT x ii in
                write%Integer result at i := x_ii in result_skip
            else (* out of bounds or NA *)
                write%Integer result at i := NA_INTEGER in result_skip
        in result_skip
      else
        do%success
        for i from 0 to n - 1 do
            read%Real di := indx at i in
            let ii := (Z.to_nat (Double.double_to_int_zero di) - 1) : int in
            ifb R_FINITE di /\ 0%Z <= ii /\ ii < nx then
                let%success x_ii := INTEGER_ELT x (Z.to_nat ii) in
                write%Integer result at i := x_ii in result_skip
            else
                write%Integer result at i := NA_INTEGER in result_skip
        in result_skip

    | RealSxp =>
      let%success indx_type := TYPEOF indx in
      ifb indx_type = IntSxp then
        run%success INTEGER_RO indx in
        do%success
        for i from 0 to n - 1 do   
            read%Integer ii := indx at i in                  
            ifb 0%Z < ii /\ ii <= nx then
                let ii := Z.to_nat ii - 1 in
                let%success x_ii := REAL_ELT x ii in
                write%Real result at i := x_ii in result_skip
            else (* out of bounds or NA *)
                write%Real result at i := NA_REAL in result_skip
        in result_skip
    else
        do%success
        for i from 0 to n - 1 do
            read%Real di := indx at i in
            let ii := (Z.to_nat (Double.double_to_int_zero di) - 1) : int in
            ifb R_FINITE di /\ 0%Z <= ii /\ ii < nx then
                let%success x_ii := REAL_ELT x (Z.to_nat ii) in
                write%Real result at i := x_ii in result_skip
            else
                 write%Real result at i := NA_REAL in result_skip
        in result_skip
     
    | CplxSxp => result_not_implemented "Complex case"
    | StrSxp =>
      let%success indx_type := TYPEOF indx in
      ifb indx_type = IntSxp then
        run%success INTEGER_RO indx in
        do%success
        for i from 0 to n - 1 do   
            read%Integer ii := indx at i in                  
            ifb 0%Z < ii /\ ii <= nx then
                let ii := Z.to_nat ii - 1 in
                let%success x_ii := STRING_ELT x ii in
                SET_STRING_ELT result i x_ii
            else (* out of bounds or NA *)
                SET_STRING_ELT result i NA_STRING
        in result_skip
      else
        do%success
        for i from 0 to n - 1 do
            read%Real di := indx at i in
            let ii := (Z.to_nat (Double.double_to_int_zero di) - 1) : int in
            ifb R_FINITE di /\ 0%Z <= ii /\ ii < nx then
                let%success x_ii := STRING_ELT x (Z.to_nat ii) in
                SET_STRING_ELT result i x_ii
            else
                SET_STRING_ELT result i NA_STRING
        in result_skip
      
    | VecSxp
    | ExprSxp => result_not_implemented "Expr case"
    | RawSxp => result_not_implemented "raw case"
    | ListSxp => result_impossible "cannot happen: pairlists are coerced to lists"
    | LangSxp => result_impossible "cannot happen: LANGSXPs are coerced to lists"
    | _ => result_error "wrong type to extract"
    end
    in
    result_success result.

Definition VectorSubset (x s call : SEXP) :=
  add%stack "VectorSubset" in
  let stretch := 1 in
  ifb s = R_MissingArg then
    duplicate globals runs x
  else
    let%success attrib := getAttrib globals runs x R_DimSymbol in

    (* Check to see if we have special matrix subscripting. */
    /* If we do, make a real subscript vector and protect it. *)

    let%success s :=
      let%success s_mat := isMatrix globals runs s in
      let%success x_arr := isArray globals runs x in
      ifb s_mat /\ x_arr then
        let%success s_cols := ncols globals runs s in
        let%success attrib_len := R_length globals runs attrib in
        ifb s_cols = attrib_len then
          let%success s :=
            if%success isString s then
              unimplemented_function "strmat2intmat"
            else result_success s in
          let%success s_int := isInteger globals runs s in
          let%success s_real := isReal s in
          ifb s_int \/ s_real then
            unimplemented_function "mat2indsub"
          else result_success s
        else result_success s
      else result_success s in

    (* Convert to a vector of integer subscripts */
    /* in the range 1:length(x). *)

    let%success (indx, stretch) := makeSubscript globals runs x s stretch call in

    (* Allocate the result. *)
    
    let%success mode := TYPEOF x in
    let%success result := ExtractSubset x indx call in
    run%success
    ifb mode = VecSxp \/ mode = ExprSxp then
      set%named result := named_plural in result_skip
    else result_skip
    in  

    let%success result :=
    ifb result <> R_NilValue then
      let%success result :=
      let%success attrib := getAttrib globals runs x R_NamesSymbol in
      ifb attrib <> R_NilValue then
        let%success nattrib := ExtractSubset attrib indx call in
        setAttrib globals runs result R_NamesSymbol nattrib  
      else
        let%success x_isArray := isArray globals runs x in
        let%success x_attrib := getAttrib globals runs x R_DimNamesSymbol in
        let%success x_attrib_length := R_length globals runs x_attrib in
        let attrib := x_attrib in
        let%success attrib :=
           ifb attrib <> R_NilValue then GetRowNames globals attrib
           else result_success (R_NilValue : SEXP) in
        ifb x_isArray /\ x_attrib_length = 1 /\ attrib <> R_NilValue then
          let%success nattrib := ExtractSubset attrib indx call in
          setAttrib globals runs result R_NamesSymbol nattrib  
        else
          result_success result
      in
      let%success attrib := getAttrib globals runs x R_SrcrefSymbol in
      let%success attrib_type := TYPEOF attrib in
      ifb attrib <> R_NilValue /\ attrib_type = VecSxp then
         let%success nattrib := ExtractSubset attrib indx call in
         setAttrib globals runs result R_SrcrefSymbol nattrib 
      else
        result_success result
    else
      result_success result
    in
  result_success result.


Definition do_subset_dflt (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subset_dflt" in
  read%list args_car, args_cdr, _ := args in
  let cdrArgs := args_cdr in
  read%list cdrArgs_car, cdrArgs_cdr, cdrArgs_tag := cdrArgs in
  let cddrArgs := cdrArgs_cdr in
  read%list cddrArgs_car, cddrArgs_cdr, cddrArgs_tag := cddrArgs in
  run%exit
    ifb cdrArgs <> R_NilValue /\ cddrArgs = R_NilValue /\ cdrArgs_tag = R_NilValue then
      let x := args_car in
      let%success x_attr := ATTRIB x in
      ifb x_attr = R_NilValue then
        let s := cdrArgs_car in
        let%success i := scalarIndex s in
        let%success x_type := TYPEOF x in
        match x_type with
        | RealSxp =>
          let%success len := XLENGTH x in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := REAL_ELT x (Z.to_nat (i - 1)) in
            let%success r := ScalarReal globals x_imu in
            result_rreturn r
          else result_rskip
        | IntSxp =>
          let%success len := XLENGTH x in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := INTEGER_ELT x (Z.to_nat (i - 1)) in
            let%success r := ScalarInteger globals x_imu in
            result_rreturn r
          else result_rskip
        | LglSxp =>
          let%success len := XLENGTH x in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := LOGICAL_ELT x (Z.to_nat (i - 1)) in
            result_rreturn (ScalarLogical globals x_imu)
          else result_rskip
        | CplxSxp =>
          let%success len := XLENGTH x in
          ifb i >= 1 /\ i <= len then
            let%success x_imu := COMPLEX_ELT x (Z.to_nat (i - 1)) in
            let%success r := ScalarComplex globals x_imu in
            result_rreturn r
          else result_rskip
        | RawSxp => result_not_implemented "Raw case."
        | _ => result_rskip
        end
      else result_rskip
    else ifb cddrArgs <> R_NilValue /\ cddrArgs_cdr = R_NilValue
          /\ cdrArgs_tag = R_NilValue /\ cddrArgs_tag = R_NilValue then
      let x := args_car in
      let%success attr := ATTRIB x in
      read%list attr_car, attr_cdr, attr_tag := attr in
      ifb attr_tag = R_DimSymbol /\ attr_cdr = R_NilValue then
        let dim := attr_car in
        let%success dim_type := TYPEOF dim in
        let%success dim_len := LENGTH globals dim in
        ifb dim_type = IntSxp /\ dim_len = 2 then
          let si := cdrArgs_car in
          let sj := cddrArgs_car in
          let%success i := scalarIndex si in
          let%success j := scalarIndex sj in
          let%success nrow := INTEGER_ELT dim 0 in
          let%success ncol := INTEGER_ELT dim 1 in
          ifb i > 0 /\ j > 0 /\ i <= nrow /\ j <= ncol then
            let k := Z.to_nat (i - 1 + nrow * (j - 1))%Z in
            let%success x_type := TYPEOF x in
            match x_type with
            | RealSxp =>
              let%success len := XLENGTH x in
              ifb k <= len then
                let%success x_k := REAL_ELT x k in
                let%success r := ScalarReal globals x_k in
                result_rreturn r
              else result_rskip
            | IntSxp =>
              let%success len := XLENGTH x in
              ifb k <= len then
                let%success x_k := INTEGER_ELT x k in
                let%success r := ScalarInteger globals x_k in
                result_rreturn r
              else result_rskip
            | LglSxp =>
              let%success len := XLENGTH x in
              ifb k <= len then
                let%success x_k := LOGICAL_ELT x k in
                result_rreturn (ScalarLogical globals x_k)
              else result_rskip
            | CplxSxp =>
              let%success len := XLENGTH x in
              ifb k <= len then
                let%success x_k := COMPLEX_ELT x k in
                let%success r := ScalarComplex globals x_k in
                result_rreturn r
              else result_rskip
            | RawSxp => result_not_implemented "Raw case."
            | _ => result_rskip
            end
          else result_rskip
        else result_rskip
      else result_rskip
    else result_rskip in
  let%success drop := ExtractDropArg args in
  let x := args_car in
  ifb x = R_NilValue then
    result_success x
  else
    let subs := args_cdr in
    let%success nsubs := R_length globals runs subs in
    let%success type := TYPEOF x in
    let%success ax :=
      if%success isVector x then
        result_success x
      else if%success isPairList x then
        let%success dim := getAttrib globals runs x R_DimSymbol in
        let%success ndim := R_length globals runs dim in
        let%success ax :=
          ifb ndim > 1 then
            let%success ax := allocArray globals runs VecSxp dim in
            let%success x_dimnames := getAttrib globals runs x R_DimNamesSymbol in
            run%success setAttrib globals runs ax R_DimNamesSymbol x_dimnames in
            run%success setAttrib globals runs ax R_NamesSymbol x_dimnames in
            result_success ax
          else
            let%success x_len := R_length globals runs x in
            let%success ax := allocVector globals VecSxp x_len in
            let%success x_names := getAttrib globals runs x R_NamesSymbol in
            run%success setAttrib globals runs ax R_NamesSymbol x_names in
            result_success ax in
        fold%success i := 0
        along x
        as x_car, _ do
          run%success SET_VECTOR_ELT ax i x_car in
          result_success (1 + i) using runs, globals in
        result_success ax
      else result_error "Object is not subsettable." in

    (* This is the actual subsetting code. */
    /* The separation of arrays and matrices is purely an optimization. *)

    let%success ans :=
      ifb nsubs < 2 then
        let%success dim := getAttrib globals runs x R_DimSymbol in
        let%success ndim := R_length globals runs dim in
        read%list subs_car, _, _ := subs in
        let%success ans := VectorSubset ax (ifb nsubs = 1 then subs_car else R_MissingArg) call in
        run%success
          ifb ndim = 1 then
            let%success len := R_length globals runs ans in
            ifb ~ drop \/ len > 1 then
              let%success nm := getAttrib globals runs ans R_NamesSymbol in
              let%success attr := ScalarInteger globals len in
              run%success
                let%success dim_names := getAttrib globals runs dim R_NamesSymbol in
                let%success dim_names_null := isNull dim_names in
                if negb dim_names_null then
                  run%success setAttrib globals runs attr R_NamesSymbol dim_names in
                  result_skip
                else result_skip in
              run%success setAttrib globals runs ans R_DimSymbol attr in
              let%success attrib := getAttrib globals runs x R_DimNamesSymbol in
              ifb attrib <> R_NilValue then
                let%success nattrib := duplicate globals runs attrib in
                run%success SET_VECTOR_ELT nattrib 0 nm in
                run%success setAttrib globals runs ans R_DimNamesSymbol nattrib in
                run%success setAttrib globals runs ans R_NamesSymbol R_NilValue in
                result_skip
              else result_skip
            else result_skip
          else result_skip in
        result_success ans
      else
        let%success x_dim := getAttrib globals runs x R_DimSymbol in
        let%success x_dim_len := R_length globals runs x_dim in
        ifb nsubs <> x_dim_len then
          result_error "Incorrect number of dimensions."
        else ifb nsubs = 2 then
          unimplemented_function "MatrixSubset"
        else unimplemented_function "ArraySubset" in
    let%success ans :=
      ifb type = LangSxp then
        let ax := ans in
        let%success ax_len := LENGTH globals ax in
        let%success ans := allocList globals ax_len in
        run%success
          ifb ax_len > 0 then
            set%type ans := LangSxp in
            fold%success i := 0
            along ans
            as px, _, _ do
              let%success ax_i := VECTOR_ELT ax i in
              set%car px := ax_i in
              result_success (1 + i) using runs, globals in
            run%success
              let%success ax_dim := getAttrib globals runs ax R_DimSymbol in
              setAttrib globals runs ans R_DimSymbol ax_dim in
            run%success
              let%success ax_dimn := getAttrib globals runs ax R_DimNamesSymbol in
              setAttrib globals runs ans R_DimNamesSymbol ax_dimn in
            run%success
              let%success ax_names := getAttrib globals runs ax R_NamesSymbol in
              setAttrib globals runs ans R_NamesSymbol ax_names in
            run%success
              let%success ax_named := NAMED ax in
              RAISE_NAMED ans ax_named in
            result_skip
          else result_skip in
        result_success ans
      else result_success ans in
    run%success
      let%success ans_attr := ATTRIB ans in
      ifb ans_attr <> R_NilValue then
        run%success setAttrib globals runs ans R_TspSymbol R_NilValue in
        run%success setAttrib globals runs ans R_ClassSymbol R_NilValue in
        result_skip
      else result_skip in
    result_success ans.

Definition do_subset (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subset" in
  let%success (disp, ans) := R_DispatchOrEvalSP call op "[" args rho in
  if disp then
    run%success
      let%success ans_named := NAMED ans in
      ifb ans_named <> named_temporary then
        set%named ans := named_plural in
        result_skip
      else result_skip in
    result_success ans
  else do_subset_dflt call op ans rho.



Definition do_subset2_dflt (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subset2_dflt" in
    let%success drop := ExtractDropArg args in
    
    let%success exact := ExtractExactArg args in
    let pok := decide (exact <> false) in
    
    read%list args_car, args_cdr, _ := args in
    let x := args_car in

    ifb x = R_NilValue then
        result_success x
    else

    (* Get the subscripting and dimensioning information */
    /* and check that any array subscripting is compatible. *)

    let subs := args_cdr in
    let%success nsubs := R_length globals runs subs in
    ifb 0 = nsubs then
        result_error "no index specified"
    else
    let%success dims := getAttrib globals runs x R_DimSymbol in
    let%success ndims := R_length globals runs dims in
    ifb nsubs > 1 /\ nsubs <> ndims then
        result_error "incorrect number of subscripts"
    else

    (* code to allow classes to extend environment *)
    let%success x_type := TYPEOF x in
    let%success x :=
    ifb x_type = S4Sxp then
        unimplemented_function "R_getS4DataSlot"
    else
        result_success x
    in

    (* split out ENVSXP for now *)
    ifb x_type = EnvSxp then
        read%list subs_car, _, _ := subs in
        let%success subs_car_isString := isString subs_car in
        let%success subs_car_length := R_length globals runs subs_car in
        ifb nsubs <> 1 \/ ~subs_car_isString \/ subs_car_length <> 1 then
            result_error "wrong arguments for subsetting an environment"
        else
        let%success subs_car_0 := STRING_ELT subs_car 0 in
        let%success subs_car_0_inst := installTrChar globals runs subs_car_0 in
        let%success ans := findVarInFrame globals runs x subs_car_0_inst in
        let%success ans_type := TYPEOF ans in
        let%success ans :=
        ifb ans_type = PromSxp then
            eval globals runs ans R_GlobalEnv
        else
            set%named ans := named_plural in
            result_success ans
        in 
       
        ifb ans = R_UnboundValue then
            result_success (R_NilValue : SEXP)
        else
            run%success
            let%success ans_named := NAMED ans in
            ifb ans_named <> named_temporary then
                set%named ans := named_plural in
                result_skip
            else result_skip in
            result_success ans
    else

    (* back to the regular program *)
    let%success x_isVector := isVector x in
    let%success x_isList := isList globals x in
    let%success x_isLanguage := isLanguage globals x in
    ifb ~(x_isVector \/ x_isList \/ x_isLanguage) then
        result_error "object of this type is not subsettable"
    else 

    let%success named_x := NAMED x in

    let%exit (offset, named_x) :=
    ifb nsubs = 1 then   (* vector indexing *)
        read%list subs_car, _, _ := subs in
        let thesub := subs_car in
        let%success len := R_length globals runs thesub in

        let%success (x, named_x) :=
        ifb len > 1 then
            (* Considering SWITCH_TO_REFCNT false *)
            let%success x := vectorIndex x thesub 0%Z (len - 1%Z) pok call false in
            let%success named_x := NAMED x in
            result_success (x, named_x)
        else result_success (x, named_x)
        in

        let%success xnames := getAttrib globals runs x R_NamesSymbol in
        let%success x_xlength := xlength globals runs x in
        let%success offset := get1index globals runs thesub xnames x_xlength pok (ifb len > 1 then (len - 1) else (-1)%Z) call in

        ifb offset < 0 \/ offset >= x_xlength then
            (* a bold attempt to get the same behaviour for $ and [[ *)
            let%success x_isNewList := isNewList globals x in
            let%success x_isExpression := isExpression x in
            let%success x_isList := isList globals x in
            let%success x_isLanguage := isLanguage globals x in
            ifb offset < 0 /\ (x_isNewList \/ x_isExpression \/ x_isList \/ x_isLanguage) then
                result_rreturn (R_NilValue : SEXP)
            else
                result_error "subscript out of bounds"
        else result_rsuccess ((Z.to_nat offset), named_x)
                         
    else   (* matrix indexing *)
      (* Here we use the fact that: */
      /* CAR(R_NilValue) = R_NilValue */
      /* CDR(R_NilValue) = R_NilValue *) 
      
        let%success indx := allocVector globals IntSxp nsubs in
        run%success INTEGER_RO dims in
        let%success dimnames := getAttrib globals runs x R_DimNamesSymbol in
        let%success ndn := R_length globals runs dimnames in
        do%success subs := subs
        for i from 0 to nsubs - 1 do
            read%list subs_car, subs_cdr, _ := subs in
            let%success dimnames_i := ifb i < ndn then VECTOR_ELT dimnames i else result_success (R_NilValue : SEXP) in
            read%Integer indx_i := indx at i in
            let%success get1indx := get1index globals runs subs_car dimnames_i indx_i pok (-1)%Z call in
            write%Integer indx at i := get1indx in
            read%Integer dims_i := dims at i in
            ifb get1indx < 0 \/ get1indx >= dims_i then
                result_error "subscript out of bounds"
            else
                result_success subs_cdr
        in
        let offset := 0 in
        do%success offset := offset
        (* Doing iteration a bit differently, hopefully the same result *)                      
        for i from 0 to nsubs - 2 do
            read%Integer indx_i := indx at ((nsubs - 1) - i) in                      
            read%Integer dims_i_1 := dims at ((nsubs - 1) - i - 1) in
            result_success ((offset + (Z.to_nat indx_i)) * (Z.to_nat dims_i_1))
        in
        read%Integer indx_0 := indx at 0 in
        result_rsuccess ((offset + (Z.to_nat indx_0)), named_x)
    in

    let%success ans :=
    let%success x_isPairList := isPairList x in
    let%success x_isVectorList := isVectorList x in
    if x_isPairList then 
        let%success x_offset := nthcdr globals runs x offset in
        read%list x_offset_car, _, _ := x_offset in
        let ans := x_offset_car in
        run%success RAISE_NAMED ans named_x in
        result_success ans
    else if x_isVectorList then
        let%success ans := VECTOR_ELT x offset in 
        run%success RAISE_NAMED ans named_x in 
        result_success ans
    else                   
        let%success x_type := TYPEOF x in
        let%success ans := allocVector globals x_type 1 in
        match x_type with
        | LglSxp =>
          let%success x_offset := LOGICAL_ELT x offset in
          write%Logical ans at 0 := x_offset in
          result_success ans
        | IntSxp =>
          let%success x_offset := INTEGER_ELT x offset in
          write%Integer ans at 0 := x_offset in
          result_success ans
        | RealSxp =>
          let%success x_offset := REAL_ELT x offset in
          write%Real ans at 0 := x_offset in
          result_success ans
        | CplxSxp =>
          let%success x_offset := COMPLEX_ELT x offset in
          write%Complex ans at 0 := x_offset in
          result_success ans
        | StrSxp =>
          let%success x_offset := STRING_ELT x offset in
          run%success SET_STRING_ELT ans 0 x_offset in
          result_success ans
        | RawSxp => result_not_implemented "raw case"
        | _ => result_error "unimplemented type in do_subset2"
        end
    in
    result_success ans.
      
Definition do_subset2 (call op args rho : SEXP) : result SEXP :=
  add%stack "do_subset2" in
     let%success (disp, ans) := R_DispatchOrEvalSP call op "[[" args rho in
     if disp then
        run%success
        let%success ans_named := NAMED ans in
        ifb ans_named <> named_temporary then
            set%named ans := named_plural in
            result_skip
        else result_skip in
        result_success ans
  else do_subset2_dflt call op ans rho.



  
Definition R_subset3_dflt (x input call : SEXP) : result SEXP :=
  add%stack "R_subset3_dflt" in
    let%success input_translate := translateChar input in
    let slen := String.length input_translate in

    let%success x_s4 := IS_S4_OBJECT x in
    let%success x_type := TYPEOF x in
    let%success x :=
    ifb x_s4 /\ x_type = S4Sxp then
      let%success x := unimplemented_function "R_getS4DataSlot" : result SEXP in
      ifb x = R_NilValue then
        result_error "$ operator not defined for this S4 class."
      else
        result_success x
    else result_success x in

    if%success isPairList x then
      fold%return (xmatch, havematch) := (R_NilValue : SEXP, 0) along x as y, _, y_list do
        let y_tag := list_tagval y_list in
        let y_car := list_carval y_list in

        let%success pstr := pstrmatch y_tag input slen in
          match pstr with
            | EXACT_MATCH =>  let y := y_car in
                              let%success x_named := NAMED x in
                              run%success RAISE_NAMED y x_named in
                                result_rreturn y
            | PARTIAL_MATCH => result_rsuccess (y, 1 + havematch)
            | NO_MATCH => result_rsuccess (xmatch, havematch)
          end using runs, globals in

        ifb havematch = 1 then
        (* A warning has been formalised out here. *)
          read%list xmatch_car, _, _ := xmatch in
          let y := xmatch_car in
          let%success x_named := NAMED x in
          run%success RAISE_NAMED y x_named in
            result_success y
        else
          result_success (R_NilValue : SEXP)
    else if%success isVectorList x then
      let%success nlist := getAttrib globals runs x R_NamesSymbol in

      let%success n := xlength globals runs x in
      do%exit (imatch, havematch) := ((-1)%Z, 0)
      for i from 0 to n - 1 do
        let%success nlist_i := STRING_ELT nlist i in
        let%success pstr := pstrmatch nlist_i input slen in
        match pstr with
         | EXACT_MATCH => let%success y := VECTOR_ELT x i in
                          let%success x_named := NAMED x in
                          run%success RAISE_NAMED y x_named in
                          result_rreturn y
         | PARTIAL_MATCH => let havematch := havematch + 1 in
                            ifb havematch = 1 then
                              let%success y := VECTOR_ELT x i in
                              set%named y := named_plural in
                              run%success SET_VECTOR_ELT x i y in
                              result_rsuccess (i : int, havematch)
                            else
                              result_rsuccess (i : int, havematch)
         | NO_MATCH => result_rsuccess (imatch, havematch)
        end
      in
      ifb havematch = 1 then
      (* A warning has been formalised out here. *)
        let%success y := VECTOR_ELT x (Z.to_nat imatch) in
        let%success x_named := NAMED x in
        run%success RAISE_NAMED y x_named in
        result_success y
      else
        result_success (R_NilValue : SEXP)
    else if%success isEnvironment x then
      let%success input_install := installTrChar globals runs input in
      let%success y := findVarInFrame globals runs x input_install in
      let%success y_type := TYPEOF y in
      let%success y :=
        ifb y_type = PromSxp then
          eval globals runs y R_GlobalEnv
        else result_success y in
      ifb y <> R_UnboundValue then
        run%success
          let%success y_named := NAMED y in
          ifb y_named <> named_temporary then
            set%named y := named_plural in
            result_skip
          else
            let%success x_named := NAMED x in
            RAISE_NAMED y x_named in
        result_success y
      else result_success (R_NilValue : SEXP)
    else if%success isVectorAtomic x then
      result_error "$ operator is invalid for atomic vectors."
    else result_error "This object is not subsettable.".

(* We choose not to formalise the last argument [syminp] in the following function. *)
Definition fixSubset3Args (call args env : SEXP) :=
  add%stack "fixSubset3args" in
    let%success input := allocVector globals StrSxp 1 in
    read%list _, args_cdr, _ := args in
    read%list args_cdr_car, _, _ := args_cdr in
    let nlist := args_cdr_car in
    let%success nlist_type := TYPEOF nlist in
    let%success nlist :=  ifb nlist_type = PromSxp then
                            eval globals runs nlist env
                          else result_success nlist in

    run%success
    if%success isSymbol nlist then
      let%success nlist_name := PRINTNAME nlist in
      SET_STRING_ELT input 0 nlist_name
    else if%success isString nlist then
      let%success nlist0 := STRING_ELT nlist 0 in
      SET_STRING_ELT input 0 nlist0
    else result_error "invalid subscript" in

    let%success args := shallow_duplicate globals runs args in
    read%list _, args_cdr, _ := args in
    set%car args_cdr := input in
    result_success args.


Definition do_subset3 (call op args env : SEXP) : result SEXP :=
  add%stack "do_subset3" in
    run%success Rf_checkArityCall globals runs op args call in
    let%success args := fixSubset3Args call args env in

    let%success (disp, ans) := R_DispatchOrEvalSP call op "$" args env in
    if disp then
      run%success
      let%success ans_named := NAMED ans in
      ifb ans_named <> named_temporary then
        set%named ans := named_plural in
        result_skip
      else result_skip in
        result_success ans
    else
      read%list ans_car, _, _ := ans in
      read%list _, args_cdr, _ := args in
      read%list args_cdr_car, _, _ := args_cdr in

      let%success args_cdr_car_0 := STRING_ELT args_cdr_car 0 in
      let%success ans := R_subset3_dflt ans_car  args_cdr_car_0 call in
      result_success ans.

End Parameters.

