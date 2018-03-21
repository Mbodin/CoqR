(** Rcore.
  Describes how R evaluates expressions.
  The content of this file is the Coq equivalent of functions from R source code.
  Note that only relevant definitions are translated here. Some are just
  reinterpreted in Coq without following the original algorithm of the
  C source. See report for more details. **)

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
Require Export Loops.


Section Parameterised.

(** * Global Variables **)

Variable globals : Globals.

Let read_globals := read_globals globals.

Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition get_R_FunTab S :=
  add%stack "get_R_FunTab" in
  match runs_R_FunTab runs with
  | None => result_bottom S
  | Some t => result_success S t
  end.

Definition read_R_FunTab S n :=
  add%stack "read_R_FunTab" in
  let%success t := get_R_FunTab S using S in
  ifb n >= ArrayList.length t then
    result_impossible S "Out of bounds."
  else
    let c := ArrayList.read t n in
    result_success S c.


Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

(* We may want to make [INT_MIN] and [INT_MAX] a parameter of the formalisation,
  as it depends on the C compiler options. *)
Definition INT_MIN : int := - 2 ^ 31.
Definition INT_MAX : int := 2 ^ 31 - 1.

Definition R_INT_MAX := INT_MAX.
Definition R_INT_MIN := INT_MIN.

Definition R_NaInt := INT_MIN.
Definition NA_INTEGER := R_NaInt.
Definition NA_LOGICAL := R_NaInt.
Definition R_PosInf : double := Double.posInf.
Definition R_NegInf : double := Double.negInf.
Definition R_NaN : double := Double.NaN.
Definition R_NaReal : double := Double.NaN1954.
Definition NA_REAL : double := R_NaReal.

Definition R_NaString := NA_STRING.

Definition R_XLEN_T_MAX : int := Zpos 4503599627370496.

Definition PLUSOP := 1.
Definition MINUSOP := 2.
Definition TIMESOP := 3.
Definition DIVOP := 4.
Definition POWOP := 5.
Definition MODOP := 6.
Definition IDIVOP := 7.

Definition EQOP := 1.
Definition NEOP := 2.
Definition LTOP := 3.
Definition LEOP := 4.
Definition GEOP := 5.
Definition GTOP := 6.


(** * Interpreter functions **)

(** We recall from RinternalsAux.v that we write [p_] for the object
  referenced by the pointer [p], and [p_f] for the field [f] or it **)

(** ** Rmath.h **)

(** The function names of this section corresponds to the macro names
  in the file include/Rmath.h. **)

Definition ISNAN (x : double) :=
  Double.isNaN x.


(** ** Rinternals.h **)

(** The function names of this section corresponds to the macro names
  in the file include/Rinternals.h. **)

Definition TYPEOF S x :=
  add%stack "TYPEOF" in
  read%defined x_ := x using S in
  result_success S (type x_).

Definition ALTREP S x :=
  add%stack "ALTREP" in
  read%defined x_ := x using S in
  result_success S (alt x_).

Definition OBJECT S x :=
  add%stack "OBJECT" in
  read%defined x_ := x using S in
  result_success S (obj x_).

Definition SET_OBJECT S x v :=
  add%stack "SET_OBJECT" in
  map%pointer x with set_obj v using S in
  result_skip S.

Definition PRINTNAME S x :=
  add%stack "PRINTNAME" in
  read%sym _, x_sym := x using S in
  result_success S (sym_pname x_sym).

Definition CHAR S x :=
  add%stack "CHAR" in
  read%VectorChar x_vector := x using S in
  result_success S (list_to_string (ArrayList.to_list x_vector)).

Definition MISSING S x :=
  add%stack "MISSING" in
  read%defined x_ := x using S in
  result_success S (nbits_to_nat (sub_nbits 0 4 (gp x_) ltac:(nbits_ok))).

Definition SET_MISSING S e (m : nat) I :=
  add%stack "SET_MISSING" in
  map%gp e with @write_nbits 16 4 0 (nat_to_nbits m I) ltac:(nbits_ok) using S in
  result_skip S.
Arguments SET_MISSING : clear implicits.

Definition ATTRIB S x :=
  add%stack "ATTRIB" in
  read%defined x_ := x using S in
  result_success S (attrib x_).

Definition NAMED S x :=
  add%stack "NAMED" in
  read%defined x_ := x using S in
  result_success S (named x_).

Definition INCREMENT_NAMED S x :=
  add%stack "INCREMENT_NAMED" in
  let%success x_named := NAMED S x using S in
  match x_named with
  | named_temporary =>
    map%pointer x with set_named_unique using S in
    result_skip S
  | named_unique =>
    map%pointer x with set_named_plural using S in
    result_skip S
  | named_plural =>
    result_skip S
  end.

Definition INCREMENT_LINKS S x :=
  add%stack "INCREMENT_LINKS" in
  INCREMENT_NAMED S x.

Definition DECREMENT_NAMED S x :=
  add%stack "DECREMENT_NAMED" in
  let%success x_named := NAMED S x using S in
  match x_named with
  | named_temporary =>
    result_skip S
  | named_unique =>
    map%pointer x with set_named_temporary using S in
    result_skip S
  | named_plural =>
    map%pointer x with set_named_unique using S in
    result_skip S
  end.

Definition DECREMENT_LINKS S x :=
  add%stack "DECREMENT_LINKS" in
  DECREMENT_NAMED S x.

Definition NO_REFERENCES S x :=
  add%stack "NO_REFERENCES" in
  let%success x_named := NAMED S x using S in
  result_success S (decide (x_named = named_temporary)).

Definition MAYBE_REFERENCED S x :=
  add%stack "MAYBE_REFERENCED" in
  let%success r := NO_REFERENCES S x using S in
  result_success S (negb r).

Definition MAYBE_SHARED S x :=
  add%stack "MAYBE_SHARED" in
  let%success x_named := NAMED S x using S in
  result_success S (decide (x_named = named_plural)).

Definition MARK_NOT_MUTABLE S x :=
  add%stack "MARK_NOT_MUTABLE" in
  map%pointer x with set_named_plural using S in
  result_skip S.

Definition ENSURE_NAMED S x :=
  add%stack "ENSURE_NAMED" in
  let%success x_named := NAMED S x using S in
  match x_named with
  | named_temporary =>
    map%pointer x with set_named_unique using S in
    result_skip S
  | _ => result_skip S
  end.

Definition SETTER_CLEAR_NAMED S x :=
  add%stack "SETTER_CLEAR_NAMED" in
  let%success x_named := NAMED S x using S in
  ifb x_named = named_unique then
    map%pointer x with set_named_temporary using S in
    result_skip S
  else result_skip S.

Definition RAISE_NAMED S x n :=
  add%stack "RAISE_NAMED" in
  let%success x_named := NAMED S x using S in
  match x_named, n with
  | (named_temporary | named_unique), named_plural
  | named_temporary, named_unique =>
    map%pointer x with set_named n using S in
    result_skip S
  | _, _ => result_skip S
  end.


Definition DDVAL_BIT := 0.

Definition DDVAL S x :=
  add%stack "DDVAL" in
  read%defined x_ := x using S in
  result_success S (nth_bit DDVAL_BIT (gp x_) ltac:(nbits_ok)).

Definition SET_DDVAL_BIT S x :=
  add%stack "SET_DDVAL_BIT" in
  map%gp x with @write_nbit 16 DDVAL_BIT ltac:(nbits_ok) true using S in
  result_skip S.

Definition UNSET_DDVAL_BIT S x :=
  add%stack "UNSET_DDVAL_BIT" in
  map%gp x with @write_nbit 16 DDVAL_BIT ltac:(nbits_ok) false using S in
  result_skip S.

Definition SET_DDVAL S x v :=
  add%stack "SET_DDVAL" in
  map%gp x with @write_nbit 16 DDVAL_BIT ltac:(nbits_ok) v using S in
  result_skip S.

Definition S4_OBJECT_BIT := 4.

Definition IS_S4_OBJECT S x :=
  add%stack "IS_S4_OBJECT" in
  read%defined x_ := x using S in
  result_success S (nth_bit S4_OBJECT_BIT (gp x_) ltac:(nbits_ok)).

Definition SET_S4_OBJECT S x :=
  add%stack "SET_S4_OBJECT" in
  map%gp x with @write_nbit 16 S4_OBJECT_BIT ltac:(nbits_ok) true using S in
  result_skip S.

Definition UNSET_S4_OBJECT S x :=
  add%stack "UNSET_S4_OBJECT" in
  map%gp x with @write_nbit 16 S4_OBJECT_BIT ltac:(nbits_ok) false using S in
  result_skip S.

Definition GROWABLE_BIT := 5.

Definition IS_GROWABLE S x :=
  add%stack "IS_GROWABLE" in
  read%defined x_ := x using S in
  result_success S (nth_bit GROWABLE_BIT (gp x_) ltac:(nbits_ok)).

Definition IS_SCALAR S x t :=
  add%stack "IS_SCALAR" in
  read%defined x_ := x using S in
  result_success S (decide (type x_ = t /\ scalar x_)).

Definition IS_SIMPLE_SCALAR S x t :=
  add%stack "IS_SIMPLE_SCALAR" in
  let%success x_scal := IS_SCALAR S x t using S in
  read%defined x_ := x using S in
  result_success S (decide (x_scal /\ attrib x_ = R_NilValue)).

Definition isLogical S s :=
  add%stack "isLogical" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = LglSxp)).

Definition IS_LOGICAL := isLogical.

Definition isSymbol S s :=
  add%stack "isSymbol" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = SymSxp)).

Definition isString S s :=
  add%stack "isString" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = StrSxp)).

Definition isReal S s :=
  add%stack "isReal" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = RealSxp)).

Definition isNull S s :=
  add%stack "isNull" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = NilSxp)).

Definition isComplex S s :=
  add%stack "isComplex" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = CplxSxp)).

Definition isObject S s :=
  add%stack "isObject" in
  OBJECT S s.

Definition isEnvironment S s :=
  add%stack "isEnvironment" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s_type = EnvSxp)).

Definition isByteCode S x :=
  add%stack "isByteCode" in
  let%success x_type := TYPEOF S x using S in
  result_success S (decide (x_type = BcodeSxp)).

Definition BCODE_CODE S x :=
  add%stack "BCODE_CODE" in
  read%list x_car, _, _ := x using S in
  result_success S x_car.

Definition BCODE_CONSTS S x :=
  add%stack "BCODE_CONSTS" in
  read%list _, x_cdr, _ := x using S in
  result_success S x_cdr.

Definition BCODE_EXPR S x :=
  add%stack "BCODE_EXPR" in
  read%list _, _, x_tag := x using S in
  result_success S x_tag.

Definition STDVEC_LENGTH S x :=
  add%stack "STDVEC_LENGTH" in
  read%defined x_ := x using S in
  match x_ with
  | SExpRec_NonVector _ => result_impossible S "Not a vector."
  | SExpRec_VectorChar x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorInteger x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorComplex x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorReal x_ => result_success S (VecSxp_length x_)
  | SExpRec_VectorPointer x_ => result_success S (VecSxp_length x_)
  end.

Definition STDVEC_TRUELENGTH S x :=
  add%stack "STDVEC_LENGTH" in
  read%defined x_ := x using S in
  match x_ with
  | SExpRec_NonVector _ => result_impossible S "Not a vector."
  | SExpRec_VectorChar x_ => result_success S (VecSxp_truelength x_)
  | SExpRec_VectorInteger x_ => result_success S (VecSxp_truelength x_)
  | SExpRec_VectorComplex x_ => result_success S (VecSxp_truelength x_)
  | SExpRec_VectorReal x_ => result_success S (VecSxp_truelength x_)
  | SExpRec_VectorPointer x_ => result_success S (VecSxp_truelength x_)
  end.

Definition SET_STDVEC_TRUELENGTH S x v :=
  add%stack "SET_STDVEC_TRUELENGTH" in
  read%defined x_ := x using S in
  let%success x_ :=
    match x_ with
    | SExpRec_NonVector _ => result_impossible S "Not a vector."
    | SExpRec_VectorChar x_ => result_success S (SExpRec_VectorChar (Vector_SExpRec_with_truelength x_ v))
    | SExpRec_VectorInteger x_ => result_success S (SExpRec_VectorInteger (Vector_SExpRec_with_truelength x_ v))
    | SExpRec_VectorComplex x_ => result_success S (SExpRec_VectorComplex (Vector_SExpRec_with_truelength x_ v))
    | SExpRec_VectorReal x_ => result_success S (SExpRec_VectorReal (Vector_SExpRec_with_truelength x_ v))
    | SExpRec_VectorPointer x_ => result_success S (SExpRec_VectorPointer (Vector_SExpRec_with_truelength x_ v))
    end using S in
  write%defined x := x_ using S in
  result_skip S.

Definition SET_TRUELENGTH S x v :=
  add%stack "SET_TRUELENGTH" in
  if%success ALTREP S x using S then
    result_error S "Can’t set ALTREP truelength."
  else
    SET_STDVEC_TRUELENGTH S x v.


(** ** Defn.h **)

(** The function names of this section corresponds to the function names
  in the file include/Defn.h. **)

Definition SPECIAL_SYMBOL_BIT := 12.

Definition IS_SPECIAL_SYMBOL S b :=
  add%stack "IS_SPECIAL_SYMBOL" in
  read%defined b_ := b using S in
  result_success S (nth_bit SPECIAL_SYMBOL_BIT (gp b_) ltac:(nbits_ok)).

(** This macro definition was already redundant in C. **)
Definition NO_SPECIAL_SYMBOLS S x :=
  add%stack "NO_SPECIAL_SYMBOLS" in
  read%defined x_ := x using S in
  result_success S (nth_bit SPECIAL_SYMBOL_BIT (gp x_) ltac:(nbits_ok)).

Definition SET_SPECIAL_SYMBOL S x v :=
  add%stack "SET_SPECIAL_SYMBOL" in
  map%gp x with @write_nbit 16 SPECIAL_SYMBOL_BIT ltac:(nbits_ok) v using S in
  result_skip S.

Definition ACTIVE_BINDING_BIT := 15.

Definition IS_ACTIVE_BINDING S symbol :=
  add%stack "IS_ACTIVE_BINDING" in
  read%defined symbol_ := symbol using S in
  result_success S (nth_bit ACTIVE_BINDING_BIT (gp symbol_) ltac:(nbits_ok)).

Definition BINDING_LOCK_BIT := 14.

Definition BINDING_IS_LOCKED S symbol :=
  add%stack "BINDING_IS_LOCKED" in
  read%defined symbol_ := symbol using S in
  result_success S (nth_bit BINDING_LOCK_BIT (gp symbol_) ltac:(nbits_ok)).

Definition LOCK_BINDING S x :=
  add%stack "LOCK_BINDING" in
  map%gp x with @write_nbit 16 BINDING_LOCK_BIT ltac:(nbits_ok) true using S in
  result_skip S.

Definition CACHED_BIT := 5.

Definition SET_CACHED S x v :=
  add%stack "SET_CACHED" in
  map%gp x with @write_nbit 16 CACHED_BIT ltac:(nbits_ok) v using S in
  result_skip S.

Definition IS_CACHED S x :=
  add%stack "IS_CACHED" in
  read%defined x_ := x using S in
  result_success S (nth_bit CACHED_BIT (gp x_) ltac:(nbits_ok)).

Definition PRSEEN S x :=
  add%stack "PRSEEN" in
  read%defined x_ := x using S in
  result_success S (nbits_to_nat (gp x_)).

Definition SET_PRSEEN S x v I :=
  add%stack "SET_PRSEEN" in
  set%gp x with @nat_to_nbits 16 v I using S in
  result_skip S.
Arguments SET_PRSEEN : clear implicits.

Definition PRSEEN_direct S x :=
  add%stack "PRSEEN_direct" in
  read%defined x_ := x using S in
  result_success S (gp x_).

Definition SET_PRSEEN_direct S x v :=
  add%stack "SET_PRSEEN_direct" in
  set%gp x with v using S in
  result_skip S.

Definition PRENV S p :=
  add%stack "PRENV" in
  read%prom _, p_prom := p using S in
  result_success S (prom_env p_prom).

Definition PRVALUE S p :=
  add%stack "PRVALUE" in
  read%prom _, p_prom := p using S in
  result_success S (prom_value p_prom).


(** ** memory.c **)

(** The function names of this section corresponds to the function
  names in the file main/memory.c. **)

Definition CONS S (car cdr : SEXP) : state * SEXP :=
  let e_ := make_SExpRec_list R_NilValue car cdr R_NilValue in
  alloc_SExp S e_.

Definition CONS_NR := CONS.

Fixpoint allocList_aux S n p :=
  match n with
  | 0 => (S, p)
  | S n =>
    let (S, p) := allocList_aux S n p in
    CONS S R_NilValue p
  end.

Definition allocList S (n : nat) : state * SEXP :=
  allocList_aux S n R_NilValue.

Definition SET_ATTRIB S x v :=
  add%stack "SET_ATTRIB" in
  let%success v_type := TYPEOF S v using S in
  ifb v_type <> ListSxp /\ v_type <> NilSxp then
    result_error S "The value must be a pairlist or NULL."
  else
    set%attrib x := v using S in
    result_skip S.

Definition STRING_ELT S (x : SEXP) i : result SEXP :=
  add%stack "STRING_ELT" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> StrSxp then
    result_error S "Not a character vector."
  else
    read%Pointer r := x at i using S in
    result_success S r.

Definition VECTOR_ELT S x i :=
  add%stack "VECTOR_ELT" in
  read%Pointer x_i := x at i using S in
  result_success S x_i.

Definition SET_PRVALUE S x v :=
  add%stack "SET_PRVALUE" in
  read%prom x_, x_prom := x using S in
  let x_prom := {|
      prom_value := v ;
      prom_expr := prom_expr x_prom ;
      prom_env := prom_env x_prom
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_prom
    |} in
  write%defined x := x_ using S in
  result_skip S.

Definition SET_PRCODE S x v :=
  add%stack "SET_PRCODE" in
  read%prom x_, x_prom := x using S in
  let x_prom := {|
      prom_value := prom_value x_prom ;
      prom_expr := v ;
      prom_env := prom_env x_prom
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_prom
    |} in
  write%defined x := x_ using S in
  result_skip S.

Definition SET_SYMVALUE S x v :=
  add%stack "SET_SYMVALUE" in
  read%sym x_, x_sym := x using S in
  let x_sym := {|
      sym_pname := sym_pname x_sym ;
      sym_value := v ;
      sym_internal := sym_internal x_sym
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_sym
    |} in
  write%defined x := x_ using S in
  result_skip S.

(** Note: there is a macro definition renaming [NewEnvironment] to
  [Rf_NewEnvironment] in the file include/Defn.h. As a consequence,
  the compiled C files references [Rf_NewEnvironment] and not
  [NewEnvironment]. These two functions are exactly the same.
  This is a relatively frequent scheme in R source code. **)
Definition NewEnvironment S (namelist valuelist rho : SEXP) : result SEXP :=
  add%stack "NewEnvironment" in
  let (S, newrho) := alloc_SExp S (make_SExpRec_env R_NilValue valuelist rho) in
  do%success (v, n) := (valuelist, namelist)
  whileb v <> R_NilValue /\ n <> R_NilValue do
    read%list _, n_cdr, n_tag := n using S in
    set%tag v := n_tag using S in
    read%list _, v_cdr, _ := v using S in
    result_success S (v_cdr, n_cdr) using S, runs in
  result_success S newrho.

(** Similarly, there is a macro renaming [mkPROMISE] to [Rf_mkPROMISE]. **)
Definition mkPromise S (expr rho : SEXP) : result SEXP :=
  add%stack "mkPromise" in
  map%pointer expr with set_named_plural using S in
  let (S, s) := alloc_SExp S (make_SExpRec_prom R_NilValue R_UnboundValue expr rho) in
  result_success S s.

Definition R_mkEVPROMISE_NR S expr val :=
  add%stack "R_mkEVPROMISE_NR" in
  let%success prom := mkPromise S expr R_NilValue using S in
  run%success SET_PRVALUE S prom val using S in
  result_success S prom.

(** The way this function has originally been defined is not
  implementable in Coq.  This is thus a loosy translation. **)
Definition allocFormalsList S l :=
  add%stack "allocFormalsList" in
  let (S, res) :=
    fold_left (fun _ (Sres : _ * SEXP) =>
        let (S, res) := Sres in
        CONS S R_NilValue res) (S, R_NilValue : SEXP) l in
  do%success n := res
  for sym in%list l do
    set%tag n := sym using S in
    run%success MARK_NOT_MUTABLE S n using S in
    read%list _, n_cdr, _ := n using S in
    result_success S n_cdr using S in
  result_success S res.

Definition allocFormalsList2 S sym1 sym2 :=
  add%stack "allocFormalsList2" in
  allocFormalsList S [sym1; sym2].

Definition allocFormalsList3 S sym1 sym2 sym3 :=
  add%stack "allocFormalsList3" in
  allocFormalsList S [sym1; sym2; sym3].

Definition allocFormalsList4 S sym1 sym2 sym3 sym4 :=
  add%stack "allocFormalsList4" in
  allocFormalsList S [sym1; sym2; sym3; sym4].

Definition allocFormalsList5 S sym1 sym2 sym3 sym4 sym5 :=
  add%stack "allocFormalsList5" in
  allocFormalsList S [sym1; sym2; sym3; sym4; sym5].

Definition allocFormalsList6 S sym1 sym2 sym3 sym4 sym5 sym6 :=
  add%stack "allocFormalsList6" in
  allocFormalsList S [sym1; sym2; sym3; sym4; sym5; sym6].


(** ** Rinlinedfuns.c **)

(** The function names of this section corresponds to the function
  names in the file include/Rinlinedfuns.c. **)

(** The way the original functions [allocVector], [allocVector3], etc.
  from R source code are defined is not compatible with the way the
  memory of the C language has been formalised here. The functions
  below are thus slightly different from their C counterparts.  The
  [repeat] function of Coq can be used to initialise their data. **)

Definition alloc_vector_char S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_char R_NilValue v_data).

Definition alloc_vector_lgl S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_lgl R_NilValue v_data).

Definition alloc_vector_int S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_int R_NilValue v_data).

Definition alloc_vector_real S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_real R_NilValue v_data).

Definition alloc_vector_cplx S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_cplx R_NilValue v_data).

(** The following allocators uses pointers. Note that the original
  [allocVector] function initialises them to [R_NilValue] (and not
  [NULL], for instance) by default. **)

Definition alloc_vector_str S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_str R_NilValue v_data).

Definition alloc_vector_vec S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_vec R_NilValue v_data).

Definition alloc_vector_expr S v_data : state * SEXP :=
  alloc_SExp S (make_SExpRec_expr R_NilValue v_data).

(** We however propose the following smart constructor, based on
  [allocVector]/[allocVector3] from main/memory.c. **)
(** Note: using [arbitrary] would here be more natural than these default values
  for the base cases, but it would not behave well in the extraction. **)
Definition allocVector S type (length : nat) :=
  add%stack "allocVector" in
  ifb (length : int) > R_XLEN_T_MAX then
    result_error S "Vector is too large"
  else
    let alloc {T} (allocator : state -> ArrayList.array T -> state * SEXP) (base : T) :=
      let (S, v) := allocator S (ArrayList.from_list (repeat base length)) in
      result_success S v in
    match type with
    | NilSxp =>
      result_success S (R_NilValue : SEXP)
    | RawSxp =>
      result_not_implemented "Raw type."
    | CharSxp =>
      alloc alloc_vector_char Ascii.zero
    | LglSxp =>
      alloc alloc_vector_lgl (NA_LOGICAL)
    | IntSxp =>
      alloc alloc_vector_int (NA_INTEGER)
    | RealSxp =>
      alloc alloc_vector_real (NA_REAL)
    | CplxSxp =>
      alloc alloc_vector_cplx (make_Rcomplex NA_REAL NA_REAL)
    | StrSxp =>
      alloc alloc_vector_str (R_NilValue : SEXP)
    | ExprSxp =>
      alloc alloc_vector_expr (R_NilValue : SEXP)
    | VecSxp =>
      alloc alloc_vector_vec (R_NilValue : SEXP)
    | LangSxp =>
      ifb length = 0 then result_success S (R_NilValue : SEXP)
      else
        let (S, s) := allocList S length in
        map%pointer s with set_type LangSxp using S in
        result_success S s
    | ListSxp =>
      let (S, s) := allocList S length in
      result_success S s
    | _ => result_error S "Invalid type in vector allocation."
    end.

Definition ScalarLogical x : SEXP :=
  ifb x = NA_LOGICAL then
    R_LogicalNAValue
  else ifb x <> 0 then
    R_TrueValue
  else R_FalseValue.

Definition ScalarInteger S x : state * SEXP :=
  alloc_vector_int S (ArrayList.from_list [x]).

Definition ScalarReal S x : state * SEXP :=
  alloc_vector_real S (ArrayList.from_list [x]).

Definition ScalarComplex S x : state * SEXP :=
  alloc_vector_cplx S (ArrayList.from_list [x]).

Definition ScalarString S (x : SEXP) : result SEXP :=
  add%stack "ScalarString" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> CharSxp then
    result_error S "The given argument is not of type ‘CharSxp’."
  else
    let (S, s) := alloc_vector_str S (ArrayList.from_list [x]) in
    result_success S s.

Definition isPairList S s :=
  add%stack "isPairList" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | NilSxp
  | ListSxp
  | LangSxp
  | DotSxp =>
    result_success S true
  | _ =>
    result_success S false
  end.

Definition isVectorList S s :=
  add%stack "isVectorList" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | VecSxp
  | ExprSxp =>
    result_success S true
  | _ =>
    result_success S false
  end.

(** The following function is actually from main/altrep.c. It has been
  placed here to solve a circular file dependency. **)

Definition ALTREP_LENGTH (S : state) (x : SEXP) : result nat :=
  unimplemented_function "ALTREP_LENGTH".

Definition XLENGTH_EX S x :=
  add%stack "XLENGTH_EX" in
  read%defined x_ := x using S in
  if alt x_ then ALTREP_LENGTH S x
  else STDVEC_LENGTH S x.

Definition XLENGTH := XLENGTH_EX.

Definition LENGTH_EX S (x : SEXP) :=
  add%stack "LENGTH_EX" in
  ifb x = R_NilValue then
    result_success S 0
  else XLENGTH S x.

Definition LENGTH := LENGTH_EX.

Definition xlength S s :=
  add%stack "xlength" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | NilSxp =>
    result_success S 0
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | CharSxp
  | VecSxp
  | ExprSxp
  | RawSxp =>
    LENGTH S s
  | ListSxp
  | LangSxp
  | DotSxp =>
    do%success (s, i) := (s, 0)
    whileb s <> NULL /\ s <> R_NilValue do
      read%list _, s_cdr, _ := s using S in
      result_success S (s_cdr, 1 + i) using S, runs in
    result_success S i
  | EnvSxp =>
    unimplemented_function "Rf_envlength"
  | _ =>
    result_success S 1
  end.
(** Named [length] in the C source file. **)
Definition R_length S s :=
  add%stack "R_length" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | NilSxp => result_success S 0
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | CharSxp
  | VecSxp
  | ExprSxp
  | RawSxp =>
    read%defined s_ := s using S in
    let%defined l := get_VecSxp_length s_ using S in
    result_success S l
  | ListSxp
  | LangSxp
  | DotSxp =>
    do%success (s, i) := (s, 0)
    whileb s <> NULL /\ s <> R_NilValue do
      read%list _, s_cdr, _ := s using S in
      result_success S (s_cdr, 1 + i) using S, runs in
    result_success S i
  | EnvSxp =>
    unimplemented_function "Rf_envlength"
  | _ =>
    result_success S 1
  end.

Definition inherits S s name :=
  add%stack "inherits" in
  read%defined s_ := s using S in
  if obj s_ then
    let%success klass := runs_getAttrib runs S s R_ClassSymbol using S in
    read%VectorPointer klass_vector := klass using S in
    do%success b := false
    for str in%array VecSxp_data klass_vector do
      if b then result_success S true
      else
        let%success str_ := CHAR S str using S in
        result_success S (decide (str_ = name)) using S in
    result_success S b
  else result_success S false.

Definition isVectorAtomic S s :=
  add%stack "isVectorAtomic" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | RawSxp => result_success S true
  | _ => result_success S false
  end.

Definition isInteger S s :=
  add%stack "isInteger" in
  let%success s_type := TYPEOF S s using S in
  let%success inh := inherits S s "factor" using S in
  result_success S (decide (s_type = IntSxp /\ ~ inh)).

Definition isList S s :=
  add%stack "isList" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s = R_NilValue \/ s_type = ListSxp)).

Definition isLanguage S s :=
  add%stack "isLanguage" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s = R_NilValue \/ s_type = LangSxp)).

Definition isNumeric S s :=
  add%stack "isNumeric" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | IntSxp =>
    let%success inh := inherits S s "factor" using S in
    result_success S (negb inh)
  | LglSxp
  | RealSxp =>
    result_success S true
  | _ => result_success S false
  end.

Definition isNumber S s :=
  add%stack "isNumber" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | IntSxp =>
    let%success inh := inherits S s "factor" using S in
    result_success S (negb inh)
  | LglSxp
  | RealSxp
  | CplxSxp =>
    result_success S true
  | _ => result_success S false
  end.

Definition isFrame S s :=
  add%stack "isFrame" in
  if%success OBJECT S s using S then
    let%success klass := runs_getAttrib runs S s R_ClassSymbol using S in
    let%success klass_len := R_length S klass using S in
    do%exit
    for i from 0 to klass_len - 1 do
      let%success str := STRING_ELT S klass i using S in
      let%success str_ := CHAR S str using S in
      ifb str_ = "data.frame"%string then
        result_rreturn S true
      else result_rskip S using S in
    result_success S false
  else result_success S false.

Definition isNewList S s :=
  add%stack "isNewList" in
  let%success s_type := TYPEOF S s using S in
  result_success S (decide (s = R_NilValue \/ s_type = VecSxp)).

Definition SCALAR_LVAL S x :=
  add%stack "SCALAR_LVAL" in
  read%Logical r := x at 0 using S in
  result_success S r.

Definition SCALAR_IVAL S x :=
  add%stack "SCALAR_IVAL" in
  read%Integer r := x at 0 using S in
  result_success S r.

Definition SCALAR_DVAL S x :=
  add%stack "SCALAR_DVAL" in
  read%Real r := x at 0 using S in
  result_success S r.

Definition SET_SCALAR_LVAL S x v :=
  add%stack "SET_SCALAR_LVAL" in
  write%Logical x at 0 := v using S in
  result_skip S.

Definition SET_SCALAR_IVAL S x v :=
  add%stack "SET_SCALAR_IVAL" in
  write%Integer x at 0 := v using S in
  result_skip S.

Definition SET_SCALAR_DVAL S x v :=
  add%stack "SET_SCALAR_DVAL" in
  write%Real x at 0 := v using S in
  result_skip S.


Definition lcons S car cdr :=
  add%stack "lcons" in
  let (S, e) := CONS S car cdr in
  map%pointer e with set_type LangSxp using S in
  result_success S e.

Definition LCONS := lcons.

Definition list1 S s :=
  CONS S s R_NilValue.

Definition list2 S s t :=
  let (S, l) := list1 S t in
  CONS S s l.

Definition list3 S s t u :=
  let (S, l) := list2 S t u in
  CONS S s l.

Definition list4 S s t u v :=
  let (S, l) := list3 S t u v in
  CONS S s l.

Definition list5 S s t u v w :=
  let (S, l) := list4 S t u v w in
  CONS S s l.

Definition list6 S s t u v w x :=
  let (S, l) := list5 S t u v w x in
  CONS S s l.

Definition lang1 S s :=
  add%stack "lang1" in
  lcons S s R_NilValue.

Definition lang2 S s t :=
  add%stack "lang2" in
  let (S, l) := list1 S t in
  lcons S s l.

Definition lang3 S s t u :=
  add%stack "lang3" in
  let (S, l) := list2 S t u in
  lcons S s l.

Definition lang4 S s t u v :=
  add%stack "lang4" in
  let (S, l) := list3 S t u v in
  lcons S s l.

Definition lang5 S s t u v w :=
  add%stack "lang5" in
  let (S, l) := list4 S t u v w in
  lcons S s l.

Definition lang6 S s t u v w x :=
  add%stack "lang6" in
  let (S, l) := list5 S t u v w x in
  lcons S s l.


Definition ALTLOGICAL_ELT S x i :=
  add%stack "ALTLOGICAL_ELT" in
  read%Logical x_i := x at i using S in
  result_success S x_i.

Definition LOGICAL_ELT S x i :=
  add%stack "LOGICAL_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTLOGICAL_ELT S x i
  else
    read%Logical x_i := x at i using S in
    result_success S x_i.

Definition ALTINTEGER_ELT (S : state) (x : SEXP) (i : nat) : result int :=
  unimplemented_function "ALTINTEGER_ELT".

Definition INTEGER_ELT S x i :=
  add%stack "INTEGER_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTINTEGER_ELT S x i
  else
    read%Integer x_i := x at i using S in
    result_success S x_i.

Definition ALTREAL_ELT (S : state) (x : SEXP) (i : nat) : result double :=
  unimplemented_function "ALTREAL_ELT".

Definition REAL_ELT S x i :=
  add%stack "REAL_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTREAL_ELT S x i
  else
    read%Real x_i := x at i using S in
    result_success S x_i.

Definition ALTCOMPLEX_ELT (S : state) (x : SEXP) (i : nat) : result Rcomplex :=
  unimplemented_function "ALTCOMPLEX_ELT".

Definition COMPLEX_ELT S x i :=
  add%stack "COMPLEX_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTCOMPLEX_ELT S x i
  else
    read%Complex x_i := x at i using S in
    result_success S x_i.

Definition ALTRAW_ELT S x i :=
  add%stack "ALTRAW_ELT" in
  read%Pointer x_i := x at i using S in
  result_success S x_i.

Definition RAW_ELT S x i :=
  add%stack "RAW_ELT" in
  read%defined x_ := x using S in
  ifb alt x_ then ALTRAW_ELT S x i
  else
    read%Pointer x_i := x at i using S in
    result_success S x_i.

(** The following function is actually from main/altrep.c. It has been
  placed here to solve a circular file dependency. **)

Definition ALTREP_TRUELENGTH S (x : SEXP) :=
  add%stack "ALTREP_TRUELENGTH" in
  result_success S 0.

Definition XTRUELENGTH S x :=
  add%stack "XTRUELENGTH" in
  if%success ALTREP S x using S then
    ALTREP_TRUELENGTH S x
  else STDVEC_TRUELENGTH S x.


(** ** duplicate.c **)

(** The function names of this section corresponds to the function names
  in the file main/duplicate.c. **)

Definition lazy_duplicate S s :=
  add%stack "lazy_duplicate" in
  let%success s_t := TYPEOF S s using S in
  run%success
    match s_t with
    | NilSxp
    | SymSxp
    | EnvSxp
    | SpecialSxp
    | BuiltinSxp
    | ExtptrSxp
    | BcodeSxp
    | WeakrefSxp
    | CharSxp
    | PromSxp =>
      result_skip S
    | CloSxp
    | ListSxp
    | LangSxp
    | DotSxp
    | ExprSxp
    | VecSxp
    | LglSxp
    | IntSxp
    | RealSxp
    | CplxSxp
    | RawSxp
    | StrSxp
    | S4Sxp =>
      map%pointer s with set_named_plural using S in
      result_skip S
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S s.

Definition DUPLICATE_ATTRIB S vto vfrom deep :=
  add%stack "DUPLICATE_ATTRIB" in
  let%success a := ATTRIB S vfrom using S in
  ifb a <> R_NilValue then
    let%success a_duplicate := runs_duplicate1 runs S a deep using S in
    run%success SET_ATTRIB S vto a_duplicate using S in
    let%success vfrom_object := OBJECT S vfrom using S in
    run%success SET_OBJECT S vto vfrom_object using S in
    if%success IS_S4_OBJECT S vfrom using S then
      SET_S4_OBJECT S vto
    else UNSET_S4_OBJECT S vto
  else result_skip S.

Definition duplicate_child S s (deep : bool) :=
  add%stack "duplicate_child" in
  if deep then
    runs_duplicate1 runs S s true
  else lazy_duplicate S s.

Definition duplicate_list S s deep :=
  add%stack "duplicate_list" in
  fold%success val := (R_NilValue : SEXP)
  along s
  as _, _ do
    let (S, val) := CONS S R_NilValue val in
    result_success S val using S, runs, globals in
  fold%success vp := val
  along s
  as s, _, s_list do
    let sp_car := list_carval s_list in
    let%success sp_car_duplicate := duplicate_child S sp_car deep using S in
    set%car vp := sp_car_duplicate using S in
    set%tag vp := list_tagval s_list using S in
    run%success DUPLICATE_ATTRIB S vp s deep using S in
    read%list _, vp_cdr, _ := vp using S in
    result_success S vp_cdr using S, runs, globals in
  result_success S val.

(** The following two functions are actually from main/memory.c. They
  are placed here to solve a circular file dependency. **)

Definition SET_VECTOR_ELT S x i v :=
  add%stack "SET_VECTOR_ELT" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> VecSxp /\ x_type <> ExprSxp /\ x_type <> WeakrefSxp then
    result_error S "It can onlybe applied to a list."
  else
    let%success x_len := XLENGTH S x using S in
    ifb i < 0 \/ i >= x_len then
      result_error S "Outbound index."
    else
      write%Pointer x at i := v using S in
      result_success S v.

Definition SET_STRING_ELT S (x : SEXP) i v : result unit :=
  add%stack "SET_STRING_ELT" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> StrSxp then
    result_error S "It can only be applied to a character vector."
  else
    let%success v_type := TYPEOF S v using S in
    ifb v_type <> CharSxp then
      result_error S "The value must be a CharSxp."
    else
      let%success x_len := XLENGTH S x using S in
      ifb i < 0 \/ i >= x_len then
        result_error S "Outbound index."
      else
        write%Pointer x at i := v using S in
        result_skip S.

Definition COPY_TRUELENGTH S (vto vfrom : SEXP) :=
  add%stack "COPY_TRUELENGTH" in
  let%success vfrom_growable := IS_GROWABLE S vfrom using S in
  if negb vfrom_growable then
    let%success vfrom_len := XTRUELENGTH S vfrom using S in
    SET_TRUELENGTH S vto vfrom_len
  else result_skip S.

Definition duplicate1 S s deep :=
  add%stack "duplicate1" in
  run%exit
    if%success ALTREP S s using S then
      unimplemented_function "ALTREP_DUPLICATE_EX"
    else result_rskip S using S in
  let%success s_type := TYPEOF S s using S in
  let%exit t :=
    match s_type with
    | NilSxp
    | SymSxp
    | EnvSxp
    | SpecialSxp
    | BuiltinSxp
    | ExtptrSxp
    | BcodeSxp
    | WeakrefSxp =>
      result_rreturn S s
    | CloSxp =>
      read%clo _, s_clo := s using S in
      let t_ :=
        make_SExpRec_clo R_NilValue
          (clo_formals s_clo) (clo_body s_clo) (clo_env s_clo) in
      let (S, t) := alloc_SExp S t_ in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      (** JIT functions have been ignored here. **)
      result_rsuccess S t
    | ListSxp =>
      let%success t := duplicate_list S s deep using S in
      result_rsuccess S t
    | LangSxp =>
      let%success t := duplicate_list S s deep using S in
      map%pointer s with set_type LangSxp using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      result_rsuccess S t
    | DotSxp =>
      let%success t := duplicate_list S s deep using S in
      map%pointer s with set_type DotSxp using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      result_rsuccess S t
    | CharSxp =>
      result_rreturn S s
    | ExprSxp
    | VecSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector S s_type n using S in
      do%success
      for i from 0 to n - 1 do
        let%success s_i := VECTOR_ELT S s i using S in
        let%success s_i_duplicated := duplicate_child S s_i deep using S in
        run%success SET_VECTOR_ELT S t i s_i_duplicated using S in
        result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | LglSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector S s_type n using S in
      run%success
        ifb n = 1 then
          read%Logical s_0 := s at 0 using S in
          write%Logical t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorLogical s_ := s using S in
          write%VectorLogical t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | IntSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector S s_type n using S in
      run%success
        ifb n = 1 then
          read%Integer s_0 := s at 0 using S in
          write%Integer t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorInteger s_ := s using S in
          write%VectorInteger t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | RealSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector S s_type n using S in
      run%success
        ifb n = 1 then
          read%Real s_0 := s at 0 using S in
          write%Real t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorReal s_ := s using S in
          write%VectorReal t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | CplxSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector S s_type n using S in
      run%success
        ifb n = 1 then
          read%Complex s_0 := s at 0 using S in
          write%Complex t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorComplex s_ := s using S in
          write%VectorComplex t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | RawSxp =>
      result_not_implemented "Raw case."
    | StrSxp =>
      let%success n := XLENGTH S s using S in
      let%success t := allocVector S s_type n using S in
      run%success
        ifb n = 1 then
          read%Pointer s_0 := s at 0 using S in
          write%Pointer t at 0 := s_0 using S in
          result_skip S
        else
          read%VectorPointer s_ := s using S in
          write%VectorPointer t := s_ using S in
          result_skip S using S in
      run%success DUPLICATE_ATTRIB S t s deep using S in
      run%success COPY_TRUELENGTH S t s using S in
      result_rsuccess S t
    | PromSxp =>
      result_rreturn S s
    | S4Sxp =>
      unimplemented_function "allocS4Object"
    | _ => result_error S "Unimplemented type."
    end using S in
  let%success t_type := TYPEOF S t using S in
  run%success
    ifb t_type = s_type then
      let%success s_obj := OBJECT S s using S in
      run%success SET_OBJECT S t s_obj using S in
      if%success IS_S4_OBJECT S s using S then
        SET_S4_OBJECT S t
      else UNSET_S4_OBJECT S t
    else result_skip S using S in
  result_success S t.

Definition duplicate S s :=
  add%stack "duplicate" in
  duplicate1 S s true.

Definition shallow_duplicate S s :=
  add%stack "shallow_duplicate" in
  duplicate1 S s false.

(** The following function is actually from main/memory.c. It has been
  placed here to solve a circular file dependency. **)
Definition SHALLOW_DUPLICATE_ATTRIB S vto vfrom :=
  add%stack "SHALLOW_DUPLICATE_ATTRIB" in
  read%defined vfrom_ := vfrom using S in
  let%success vfrom_attrib := shallow_duplicate S (attrib vfrom_) using S in
  run%success SET_ATTRIB S vto vfrom_attrib using S in
  map%pointer vto with set_obj (obj vfrom_) using S in
  run%success
    if%success IS_S4_OBJECT S vfrom using S then
      SET_S4_OBJECT S vto
    else UNSET_S4_OBJECT S vto using S in
  result_skip S.


Definition isVector S s :=
  add%stack "isVector" in
  let%success s_type := TYPEOF S s using S in
  match s_type with
  | LglSxp
  | IntSxp
  | RealSxp
  | CplxSxp
  | StrSxp
  | RawSxp
  | VecSxp
  | ExprSxp =>
    result_success S true
  | _ =>
    result_success S false
  end.

Definition isMatrix S s :=
  add%stack "isMatrix" in
  if%success isVector S s using S then
    let%success t := runs_getAttrib runs S s R_DimSymbol using S in
    let%success t_type := TYPEOF S t using S in
    ifb t_type = IntSxp then
      let%success t_len := LENGTH S t using S in
      ifb t_len = 2 then
        result_success S true
      else result_success S false
    else result_success S false
  else result_success S false.

Definition R_cycle_detected S s child :=
  add%stack "R_cycle_detected" in
  let%success child_type := TYPEOF S child using S in
  ifb s = child then
    match child_type with
    | NilSxp
    | SymSxp
    | EnvSxp
    | SpecialSxp
    | BuiltinSxp
    | ExtptrSxp
    | BcodeSxp
    | WeakrefSxp =>
      result_success S false
    | _ =>
      result_success S true
    end
  else
    run%exit
      read%defined child_ := child using S in
      ifb attrib child_ <> R_NilValue then
        if%success runs_R_cycle_detected runs S s (attrib child_) using S then
          result_rreturn S true
        else result_rskip S
      else result_rskip S using S in
    if%success isPairList S child using S then
      fold%return
      along child
      as el, el_, el_list do
        let%success r :=
          runs_R_cycle_detected runs S s (list_carval el_list) using S in
        ifb s = el \/ r then
          result_rreturn S true
        else
          let%success r :=
            runs_R_cycle_detected runs S s (attrib el_) using S in
          ifb attrib el_ <> R_NilValue /\ r then
            result_rreturn S true
          else result_rskip S
      using S, runs, globals in
      result_success S false
    else
      if%success isVectorList S child using S then
        read%VectorPointer child_ := child using S in
        do%let r := false
        for e in%array VecSxp_data child_ do
          if r then result_success S r
          else runs_R_cycle_detected runs S s e using S
      else result_success S false.


(** ** dstruct.c **)

(** The function names of this section corresponds to the function names
  in the file main/dstruct.c. **)

Definition mkPRIMSXP S (offset : nat) (type : bool) : result SEXP :=
  add%stack "mkPRIMSXP" in
  let type := if type then BuiltinSxp else SpecialSxp in
  let%success R_FunTab := get_R_FunTab S using S in
  let FunTabSize := ArrayList.length R_FunTab in
  (** The initialisation of the array is performed in [mkPRIMSXP_init] in [Rinit]. **)
  ifb offset >= FunTabSize then
    result_error S "Offset is out of range"
  else
    read%Pointer result := mkPRIMSXP_primCache at offset using S in
    ifb result = R_NilValue then
      let (S, result) := alloc_SExp S (make_SExpRec_prim R_NilValue offset type) in
      write%Pointer mkPRIMSXP_primCache at offset := result using S in
      result_success S result
    else
      let%success result_type := TYPEOF S result using S in
      ifb result_type <> type then
        result_error S "Requested primitive type is not consistent with cached value."
      else result_success S result.

Definition mkCLOSXP S (formals body rho : SEXP) :=
  add%stack "mkCLOSXP" in
  let%success body_type := TYPEOF S body using S in
  match body_type with
  | CloSxp
  | BuiltinSxp
  | SpecialSxp
  | DotSxp
  | AnySxp =>
    result_error S "Invalid body argument."
  | _ =>
    let env :=
      ifb rho = R_NilValue then
        (R_GlobalEnv : SEXP)
      else rho in
    let (S, c) := alloc_SExp S (make_SExpRec_clo R_NilValue formals body env) in
    result_success S c
  end.


(** ** Rinlinedfuns.c **)

(** The function names of this section corresponds to the function
  names in the file include/Rinlinedfuns.c.  The most important
  functions of eval.c are however only shown in a previous section.**)

Definition R_FixupRHS S x y :=
  add%stack "R_FixupRHS" in
  let%success y_named := NAMED S y using S in
  ifb y <> R_NilValue /\ y_named <> named_temporary then
    if%success R_cycle_detected S x y using S then
      duplicate S y
    else
      map%pointer y with set_named_plural using S in
      result_success S y
  else result_success S y.

Definition isVectorizable S (s : SEXP) :=
  add%stack "isVectorizable" in
  ifb s = R_NilValue then
    result_success S true
  else if%success isNewList S s using S then
    let%success n := XLENGTH S s using S in
    do%exit
    for i from 0 to n - 1 do
      let%success s_i := VECTOR_ELT S s i using S in
      let%success s_i_iv := isVector S s_i using S in
      let%success s_i_len := LENGTH S s_i using S in
      ifb ~ s_i_iv \/ s_i_len > 1 then
        result_rreturn S false
      else result_rskip S using S in
    result_success S true
  else if%success isList S s using S then
    fold%return
    along s
    as s_car, _ do
      let%success s_car_iv := isVector S s_car using S in
      let%success s_car_len := LENGTH S s_car using S in
      ifb ~ s_car_iv \/ s_car_len > 1 then
        result_rreturn S false
      else result_rskip S using S, runs, globals in
    result_success S true
  else result_success S false.

Definition isArray S s :=
  add%stack "isArray" in
  if%success isVector S s using S then
    let%success t := runs_getAttrib runs S s R_DimSymbol using S in
    let%success t_type := TYPEOF S t using S in
    let%success t_len := LENGTH S t using S in
    ifb t_type = IntSxp /\ t_len > 0 then
      result_success S true
    else result_success S false
  else result_success S false.

Definition isTs S s :=
  add%stack "isTs" in
  if%success isVector S s using S then
    let%success a := runs_getAttrib runs S s R_TspSymbol using S in
    result_success S (decide (a <> R_NilValue))
  else result_success S false.

Definition conformable S x y :=
  add%stack "conformable" in
  let%success x := runs_getAttrib runs S x R_DimSymbol using S in
  let%success y := runs_getAttrib runs S y R_DimSymbol using S in
  let%success x_len := R_length S x using S in
  let%success y_len := R_length S y using S in
  ifb x_len <> y_len then
    result_success S false
  else
    let n := x_len in
    do%exit
    for i from 0 to n - 1 do
      read%Integer x_i := x at i using S in
      read%Integer y_i := y at i using S in
      ifb x_i <> y_i then
        result_rreturn S false
      else result_rskip S using S in
    result_success S true.

Definition isValidString S x :=
  add%stack "isValidString" in
  let%success x_type := TYPEOF S x using S in
  let%success x_len := LENGTH S x using S in
  let%success x_0 := STRING_ELT S x 0 using S in
  let%success x_0_type := TYPEOF S x_0 using S in
  result_success S (decide (x_type = StrSxp /\ x_len > 0 /\ x_0_type <> NilSxp)).


(** ** eval.c **)

(** The function names of this section corresponds to the function
  names in the file main/eval.c. The most important functions of
  eval.c are however only shown in a later section. **)

Definition BCCONSTS S e :=
  add%stack "BCCONSTS" in
  BCODE_CONSTS S e.

Definition bytecodeExpr S e :=
  add%stack "bytecodeExpr" in
  if%success isByteCode S e using S then
    let%success e := BCCONSTS S e using S in
    let%success e_len := LENGTH S e using S in
    ifb e_len > 0 then
      VECTOR_ELT S e 0
    else result_success S (R_NilValue : SEXP)
  else result_success S e.

Definition R_PromiseExpr S p :=
  add%stack "R_PromiseExpr" in
  read%prom _, p_prom := p using S in
  bytecodeExpr S (prom_expr p_prom).

Definition PREXPR S e :=
  add%stack "PREXPR" in
  R_PromiseExpr S e.


(** ** arithmetic.c **)

(** The function names of this section corresponds to the function names
  in the file main/arithmetic.c. **)

Definition R_IsNA (x : double) :=
  decide (Double.getNaNData x = Some 1954)%positive.

Definition R_IsNaN x :=
  match Double.getNaNData x with
  | Some i => decide (i <> 1954)%positive
  | None => false
  end.

Definition ScalarValue1 S x :=
  add%stack "ScalarValue1" in
  if%success NO_REFERENCES S x using S then
    result_success S x
  else
    let%success x_type := TYPEOF S x using S in
    allocVector S x_type 1.

Definition ScalarValue2 S x y :=
  add%stack "ScalarValue2" in
  if%success NO_REFERENCES S x using S then
    result_success S x
  else
    if%success NO_REFERENCES S y using S then
      result_success S y
    else
      let%success x_type := TYPEOF S x using S in
      allocVector S x_type 1.


(** ** util.c **)

(** The function names of this section corresponds to the function names
  in the file main/util.c. **)

Definition type2rstr S (t : SExpType) :=
  add%stack "type2rstr" in
  let res := Type2Table_rstrName (ArrayList.read (global_Type2Table globals) t) in
  ifb res <> NULL then result_success S res
  else result_success S (R_NilValue : SEXP).

Definition nthcdr S s n :=
  add%stack "nthcdr" in
  let%success s_li := isList S s using S in
  let%success s_la := isLanguage S s using S in
  let%success s_fr := isFrame S s using S in
  let%success s_t := TYPEOF S s using S in
  ifb s_li \/ s_la \/ s_fr \/ s_t = DotSxp then
    do%success (s, n) := (s, n)
    whileb n > 0 do
      ifb s = R_NilValue then
        result_error S "List too short."
      else
        read%list _, s_cdr, _ := s using S in
        result_success S (s, n - 1) using S, runs in
    result_success S s
  else result_error S "No CDR.".


(** ** printutils.c **)

(** The function names of this section corresponds to the function names
  in the file main/printutils.c. **)

Definition EncodeLogical x :=
  ifb x = NA_LOGICAL then "NA"%string
  else ifb x <> 0 then "TRUE"%string
  else "FALSE"%string.

Definition StringFromReal S x :=
  add%stack "StringFromReal" in
  if R_IsNA x then
    result_success S (NA_STRING : SEXP)
  else unimplemented_function "EncodeRealDrop0".


(** ** envir.c **)

(** The function names of this section corresponds to the function
  names in the file main/envir.c. The most important functions of
  envir.c are however only shown in a later section. **)

(** The function [mkChar] from the R source code performs a lot of things.
  It deals with encoding, for embedded zero-characters, as well as avoid
  allocated twice the same string, by looking through the already
  allocated strings. We do none of the above. **)
(* FIXME: What is the difference between [intCHARSXP] and [CHARSXP]? *)
Definition mkChar S (str : string) : state * SEXP :=
  (* Note that values are not cached, in contrary to the original code. *)
  alloc_vector_char S (ArrayList.from_list (string_to_list str)).

Definition mkString S (str : string) : state * SEXP :=
  let (S, c) := mkChar S str in
  alloc_vector_str S (ArrayList.from_list [c]).


(** ** dstruct.c **)

(** The function names of this section corresponds to the function names
  in the file main/dstruct.c. **)

Definition iSDDName S (name : SEXP) :=
  add%stack "iSDDName" in
  let%success buf := CHAR S name using S in
  ifb substring 0 2 buf = ".."%string /\ String.length buf > 2 then
    let buf := substring 2 (String.length buf) buf in
    (** I am simplifying the C code here. **)
    result_success S (decide (Forall (fun c : Ascii.ascii =>
        Mem c (["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"])%char)
      (string_to_list buf)))
  else
  result_success S false.

Definition mkSYMSXP S (name value : SEXP) :=
  add%stack "mkSYMSXP" in
  let%success i := iSDDName S name using S in
  let (S, c) := alloc_SExp S (make_SExpRec_sym R_NilValue name value R_NilValue) in
  run%success SET_DDVAL S c i using S in
  result_success S c.


(** ** names.c **)

(** The function names of this section corresponds to the function names
  in the file main/names.c. **)

Definition mkSymMarker S pname :=
  add%stack "mkSymMarker" in
  let (S, ans) := alloc_SExp S (make_SExpRec_sym R_NilValue pname NULL R_NilValue) in
  write%defined ans := make_SExpRec_sym R_NilValue pname ans R_NilValue using S in
  result_success S ans.

Definition install S name_ : result SEXP :=
  add%stack "install" in
  (** As said in the description of [InitNames] in Rinit.v,
    the hash table present in [R_SymbolTable] has not been
    formalised as such.
    Instead, it is represented as a single list, and not
    as [HSIZE] different lists.
    This approach is slower, but equivalent. **)
  fold%return
  along R_SymbolTable S
  as sym_car, _ do
    let%success str_sym := PRINTNAME S sym_car using S in
    let%success str_name_ := CHAR S str_sym using S in
    ifb name_ = str_name_ then
      result_rreturn S sym_car
    else result_rskip S using S, runs, globals in
  ifb name_ = ""%string then
    result_error S "Attempt to use zero-length variable name."
  else
    let (S, str) := mkChar S name_ in
    let%success sym := mkSYMSXP S str R_UnboundValue using S in
    let (S, SymbolTable) := CONS S sym (R_SymbolTable S) in
    let S := update_R_SymbolTable S SymbolTable in
    result_success S sym.

(** We here choose to model [installChar] as its specification
  given by the associated comment in the C source file. **)
Definition installChar S charSXP :=
  add%stack "installChar" in
  let%success str := CHAR S charSXP using S in
  install S str.


(** ** sysutils.c **)

(** The function names of this section corresponds to the function names
  in the file main/sysutils.c. **)

Definition translateChar S x :=
  add%stack "translateChar" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> CharSxp then
    result_error S "Must be called on a CharSxp."
  else
    (** The original C program deals with encoding here. **)
    CHAR S x.

Definition installTrChar S x :=
  add%stack "installTrChar" in
  let%success x_type := TYPEOF S x using S in
  ifb x_type <> CharSxp then
    result_error S "Must be called on a CharSxp."
  else
    (** The original C program deals with encoding here. **)
    installChar S x.


(** ** gram.y **)

(** The function names of this section corresponds to the function names
  in the file main/gram.y. **)

Definition mkTrue S :=
  alloc_vector_lgl S (ArrayList.from_list [1 : int]).

Definition mkFalse S :=
  alloc_vector_lgl S (ArrayList.from_list [0 : int]).

Definition mkNA S :=
  alloc_vector_lgl S (ArrayList.from_list [NA_LOGICAL : int]).


Definition NewList S :=
  add%stack "NewList" in
  let (S, s) := CONS S R_NilValue R_NilValue in
  set%car s := s using S in
  result_success S s.

Definition GrowList S l s :=
  add%stack "GrowList" in
  let (S, tmp) := CONS S s R_NilValue in
  read%list l_car, _, _ := l using S in
  set%cdr l_car := tmp using S in
  set%car l := tmp using S in
  result_success S l.

Definition TagArg S arg tag :=
  add%stack "TagArg" in
  let%success tag_type := TYPEOF S tag using S in
  match tag_type with
  | StrSxp =>
    let%success tag_ := STRING_ELT S tag 0 using S in
    let%success tag := installTrChar S tag_ using S in
    lang2 S arg tag
  | NilSxp
  | SymSxp =>
    lang2 S arg tag
  | _ =>
    result_error S "Incorrect tag type."
  end.

Definition FirstArg S s tag :=
  add%stack "FirstArg" in
  let%success tmp := NewList S using S in
  let%success tmp := GrowList S tmp s using S in
  read%list tmp_car, _, _ := tmp using S in
  set%tag tmp_car := tag using S in
  result_success S tmp.

Definition NextArg S l s tag :=
  add%stack "NextArg" in
  let%success l := GrowList S l s using S in
  read%list l_car, _, _ := l using S in
  set%tag l_car := tag using S in
  result_success S l.

Definition CheckFormalArgs S formlist new :=
  add%stack "CheckFormalArgs" in
  fold%success
  along formlist
  as _, formlist_tag do
    ifb formlist_tag = new then
      result_error S "Repeated formal argument."
    else result_skip S using S, runs, globals in
  result_skip S.


(** ** context.c **)

(** The function names of this section corresponds to the function names
  in the file main/context.c. **)

(** Instead of updating a context given as its first argument, it returns it. **)
Definition begincontext S flags syscall env sysp promargs callfun :=
  add%stack "begincontext" in
  let cptr := {|
     context_nextcontext := Some (R_GlobalContext S) ;
     context_cjmpbuf := 1 + context_cjmpbuf (R_GlobalContext S) ;
     context_callflag := flags ;
     context_promargs := promargs ;
     context_callfun := callfun ;
     context_sysparent := sysp ;
     context_call := syscall ;
     context_cloenv := env ;
     context_conexit := R_NilValue ;
     context_returnValue := NULL ;
     context_jumptarget := None ;
     context_jumpmask := empty_context_type
   |} in
  let S := state_with_context S cptr in
  result_success S cptr.

Fixpoint first_jump_target_loop S c cptr mask :=
  ifb c = cptr then
    result_success S cptr
  else
    ifb context_cloenv c <> R_NilValue /\ context_conexit c <> R_NilValue then
      let c := context_with_jumptarget c (Some cptr) in
      let c := context_with_jumpmask c mask in
      result_success S c
    else
      match context_nextcontext c with
      | None => result_success S cptr
      | Some c => first_jump_target_loop S c cptr mask
      end.

Definition first_jump_target S cptr mask :=
  add%stack "first_jump_target" in
  first_jump_target_loop S (R_GlobalContext S) cptr mask.

Fixpoint R_run_onexits_loop S c cptr :=
  ifb c = cptr then
    result_skip S
  else
    run%success
      ifb context_cloenv c <> R_NilValue /\ context_conexit c <> R_NilValue then
        let s := context_conexit c in
        let savecontext := R_ExitContext S in
        let c := context_with_conexit c R_NilValue in
        let c := context_with_returnValue c NULL in
        let S := update_R_ExitContext S (Some c) in
        fold%success
        along s
        as _, _, s_list do
          let c := context_with_conexit c (list_cdrval s_list) in
          let S := state_with_context S c in
          run%success
            runs_eval runs S (list_carval s_list) (context_cloenv cptr) using S in
            result_skip S using S, runs, globals in
        let S := update_R_ExitContext S savecontext in
        result_skip S
      else result_skip S using S in
    run%success
      ifb R_ExitContext S = Some c then
        let S := update_R_ExitContext S None in
        result_skip S
      else result_skip S using S in
    match context_nextcontext c with
    | None => result_impossible S "Bad target context."
    | Some c => R_run_onexits_loop S c cptr
    end.

Definition R_run_onexits S cptr :=
  add%stack "R_run_onexits" in
  R_run_onexits_loop S (R_GlobalContext S) cptr.

Definition R_restore_globals S (cptr : context) :=
  add%stack "R_restore_globals" in
  result_skip S.

Definition R_jumpctxt A S targetcptr mask val : result A :=
  add%stack "R_jumpctxt" in
  let%success cptr := first_jump_target S targetcptr mask using S in
  run%success R_run_onexits S cptr using S in
  let S := update_R_ReturnedValue S val in
  let S := state_with_context S cptr in
  run%success R_restore_globals S (R_GlobalContext S) using S in
  result_longjump S (context_cjmpbuf cptr) mask.
Arguments R_jumpctxt [A].

Definition endcontext S cptr :=
  add%stack "endcontext" in
  let jmptarget := context_jumptarget cptr in
  run%success
    ifb context_cloenv cptr <> R_NilValue /\ context_conexit cptr <> R_NilValue then
      let s := context_conexit cptr in
      let savecontext := R_ExitContext S in
      let cptr := context_with_conexit cptr R_NilValue in
      let cptr := context_with_jumptarget cptr None in
      let S := update_R_ExitContext S (Some cptr) in
      fold%success
      along s
      as _, _, s_list do
        let cptr := context_with_conexit cptr (list_cdrval s_list) in
        let S := state_with_context S cptr in
        run%success
          runs_eval runs S (list_carval s_list) (context_cloenv cptr) using S in
        result_skip S using S, runs, globals in
      let S := update_R_ExitContext S savecontext in
      result_skip S
    else result_skip S using S in
  run%success
    ifb R_ExitContext S = Some cptr then
      let S := update_R_ExitContext S None in
      result_skip S
    else result_skip S using S in
  run%success
    match jmptarget with
    | None => result_skip S
    | Some jmptarget =>
      R_jumpctxt S jmptarget (context_jumpmask cptr) (R_ReturnedValue S)
    end using S in
  let%defined c := context_nextcontext cptr using S in
  let S := state_with_context S c in
  result_skip S.

Fixpoint findcontext_loop A S cptr env mask mask_against val err : result A :=
  ifb context_type_mask (context_callflag cptr) mask_against /\ context_cloenv cptr = env then
    R_jumpctxt S cptr mask val
  else
    let error S := result_error S err in
    match context_nextcontext cptr with
    | None => error S
    | Some cptr =>
      ifb context_callflag cptr = Ctxt_TopLevel then error S
      else findcontext_loop _ S cptr env mask mask_against val err
    end.
Arguments findcontext_loop [A].

Definition findcontext A S mask env val : result A :=
  add%stack "findcontext" in
  ifb context_type_mask Ctxt_Loop mask then
    findcontext_loop S (R_GlobalContext S) env mask Ctxt_Loop val "No loop for break/next, jumping to top level."
  else
    findcontext_loop S (R_GlobalContext S) env mask mask val "No function to return from, jumping to top level.".
Arguments findcontext [A].


(** ** match.c **)

(** The function names of this section corresponds to the function names
  in the file main/match.c. **)

Definition psmatch f t exact :=
  if exact : bool then
    decide (f = t)
  else
    String.prefix t f.

Definition pmatch S (formal tag : SEXP) exact : result bool :=
  add%stack "pmatch" in
  let get_name str :=
    let%success str_type := TYPEOF S str using S in
    match str_type with
    | SymSxp =>
      let%success str_name := PRINTNAME S str using S in
      CHAR S str_name
    | CharSxp =>
      CHAR S str
    | StrSxp =>
      let%success str_ := STRING_ELT S str 0 using S in
      result_not_implemented "translateChar(str_)"
    | _ =>
      result_error S "Invalid partial string match."
    end in
  let%success f := get_name formal using S in
  let%success t := get_name tag using S in
  result_success S (psmatch f t exact).

(** The function [matchArgs] matches the arguments supplied to a given
  call with the formal, expected arguments.
  This is more complex as it may seem as arguments in R can be named
  (and thus provided in any order), or can be ‘...’.
  The algorithm presented in this function is thus crucial to understand
  the semantics of function calls in R.
  It is furthermore rather complicated.
  This is a large function and is divided into all its three passes for
  readability purposes. **)

(** The function makes use of some bits from the general purpose pool
  to mark some arguments as being used or missing. **)

Definition argused e_ :=
  nbits_to_nat (gp e_).

Definition set_argused (used : nat) I :=
  set_gp (nat_to_nbits used I).
Arguments set_argused : clear implicits.

Definition matchArgs_first S formals actuals supplied : result (list nat) :=
  add%stack "matchArgs_first" in
  fold%success (a, fargusedrev) := (actuals, nil)
  along formals
  as _, f_tag do
    let%success f_tag_sym_name := PRINTNAME S f_tag using S in
    let%success ftag_name := CHAR S f_tag_sym_name using S in
    let%success fargusedi :=
      ifb f_tag <> R_DotsSymbol /\ f_tag <> R_NilValue then
        fold%let fargusedi := 0
        along supplied
        as b, b_, b_list do
          let b_tag := list_tagval b_list in
          ifb b_tag <> R_NilValue then
            let%success b_tag_sym_name := PRINTNAME S b_tag using S in
            let%success btag_name := CHAR S b_tag_sym_name using S in
            ifb ftag_name = btag_name then
              ifb fargusedi = 2 then
                result_error S "Formal argument matched by multiple actual arguments."
              else ifb argused b_ = 2 then
                result_error S "Actual argument matches several formal arguments."
              else
                set%car a := list_carval b_list using S in
                run%success
                  ifb list_carval b_list <> R_MissingArg then
                    SET_MISSING S a 0 ltac:(nbits_ok)
                  else result_skip S using S in
                map%pointer b with set_argused 2 ltac:(nbits_ok) using S in
                result_success S 2
            else result_success S fargusedi
          else result_success S fargusedi using S, runs, globals
      else result_success S 0 using S in
    read%list _, a_cdr, _ := a using S in
    result_success S (a_cdr, fargusedi :: fargusedrev) using S, runs, globals in
  result_success S (List.rev fargusedrev).

Definition matchArgs_second S actuals formals supplied fargused :=
  add%stack "matchArgs_second" in
  fold%success (a, fargused, dots, seendots) :=
    (actuals, fargused, R_NilValue : SEXP, false)
  along formals
  as _, f_tag do
    match fargused with
    | nil =>
      result_impossible S "The list/array “fargused” has an unexpected size."
    | fargusedi :: fargused =>
      let%success (dots, seendots) :=
        ifb fargusedi = 0 then
          ifb f_tag = R_DotsSymbol /\ ~ seendots then
            result_success S (a, true)
          else
            fold%success fargusedi := fargusedi
            along supplied
            as b, b_, b_list do
              let b_tag := list_tagval b_list in
              ifb argused b_ <> 2 /\ b_tag <> R_NilValue then
                if%success pmatch S f_tag b_tag seendots using S then
                  ifb argused b_ <> 0 then
                    result_error S "Actual argument matches several formal arguments."
                  else ifb fargusedi = 1 then
                    result_error S "Formal argument matched by multiple actual arguments."
                  else
                    set%car a := list_carval b_list using S in
                    run%success
                      ifb list_carval b_list <> R_MissingArg then
                        SET_MISSING S a 0 ltac:(nbits_ok)
                      else result_skip S using S in
                    map%pointer b with set_argused 1 ltac:(nbits_ok) using S in
                    result_success S 1
                else result_success S fargusedi
              else result_success S fargusedi using S, runs, globals in
            result_success S (dots, seendots)
        else result_success S (dots, seendots) using S in
      read%list _, a_cdr, _ := a using S in
      result_success S (a_cdr, fargused, dots, seendots)
    end using S, runs, globals in
  result_success S dots.

Definition matchArgs_third S (formals actuals supplied : SEXP) :=
  add%stack "matchArgs_third" in
  do%success (f, a, b, seendots) := (formals, actuals, supplied, false)
  whileb f <> R_NilValue /\ b <> R_NilValue /\ ~ seendots do
    read%list _, f_cdr, f_tag := f using S in
    read%list a_car, a_cdr, _ := a using S in
    ifb f_tag = R_DotsSymbol then
      result_success S (f_cdr, a_cdr, b, true)
    else ifb a_car <> R_MissingArg then
      result_success S (f_cdr, a_cdr, b, seendots)
    else
      read%list b_, b_car, b_cdr, b_tag := b using S in
      ifb argused b_ <> 0 \/ b_tag <> R_NilValue then
        result_success S (f, a, b_cdr, seendots)
      else
        set%car a := b_car using S in
        run%success
          ifb b_car <> R_MissingArg then
            SET_MISSING S a 0 ltac:(nbits_ok)
          else result_skip S using S in
        map%pointer b with set_argused 1 ltac:(nbits_ok) using S in
        result_success S (f_cdr, a_cdr, b_cdr, seendots) using S, runs in
  result_skip S.

Definition matchArgs_dots S dots supplied :=
  add%stack "matchArgs_dots" in
  run%success SET_MISSING S dots 0 ltac:(nbits_ok) using S in
  fold%success i := 0
  along supplied
  as _, a_, _ do
    ifb argused a_ = 0 then
      result_success S (1 + i)
    else
      result_success S i using S, runs, globals in
  ifb i <> 0 then
    let (S, a) := allocList S i in
    map%pointer a with set_type DotSxp using S in
    fold%success f := a
    along supplied
    as _, b_, b_list do
      ifb argused b_ = 0 then
        set%car f := list_carval b_list using S in
        set%tag f := list_tagval b_list using S in
        read%list _, f_cdr, _ := f using S in
        result_success S f_cdr
      else result_success S f using S, runs, globals in
    set%car dots := a using S in
    result_skip S
  else result_skip S.

Definition matchArgs_check S supplied :=
  add%stack "matchArgs_check" in
  fold%success (unused, last) := (R_NilValue : SEXP, R_NilValue : SEXP)
  along supplied
  as _, b_, b_list do
    ifb argused b_ = 0 then
      ifb last = R_NilValue then
        let (S, unused) := CONS S (list_carval b_list) R_NilValue in
        set%tag unused := list_tagval b_list using S in
        result_success S (unused, unused)
      else
        let (S, l) := CONS S (list_carval b_list) R_NilValue in
        set%cdr last := l using S in
        read%list _, last_cdr, _ := last using S in
        let last := last_cdr in
        set%tag last := list_tagval b_list using S in
        result_success S (unused, last)
    else result_success S (unused, last) using S, runs, globals in
  ifb last <> R_NilValue then
    result_error S "Unused argument(s)."
  else
    result_skip S.


Definition matchArgs S formals supplied (call : SEXP) :=
  add%stack "matchArgs" in
  fold%success (actuals, argi) := (R_NilValue : SEXP, 0)
  along formals
  as _, _ do
    let (S, actuals) := CONS_NR S R_MissingArg actuals in
    run%success SET_MISSING S actuals 1 ltac:(nbits_ok) using S in
    result_success S (actuals, 1 + argi) using S, runs, globals in
  fold%success
  along supplied
  as b, _ do
    map%pointer b with set_argused 0 ltac:(nbits_ok) using S in
    result_skip S using S, runs, globals in
  let%success fargused := matchArgs_first S formals actuals supplied using S in
  let%success dots := matchArgs_second S actuals formals supplied fargused using S in
  run%success matchArgs_third S formals actuals supplied using S in
  ifb dots <> R_NilValue then
    run%success matchArgs_dots S dots supplied using S in
    result_success S actuals
  else
    run%success matchArgs_check S supplied using S in
    result_success S actuals.


(** ** envir.c **)

(** The function names of this section corresponds to the function names
  in the file main/envir.c. **)

Definition R_NewHashedEnv S (enclos size : SEXP) :=
  add%stack "R_NewHashedEnv" in
  let%success s := NewEnvironment S R_NilValue R_NilValue enclos using S in
  (** As we do not model hashtabs, we are here skipping the most
    important part of this function.  This is thus only a
    simplification of the original function. **)
  result_success S s.

Definition R_envHasNoSpecialSymbols S (env : SEXP) :=
  add%stack "R_envHasNoSpecialSymbols" in
  read%env env_, env_env := env using S in
  (** A note about hashtabs has been commented out. **)
  fold%let b := true
  along env_frame env_env
  as frame_car, frame_tag do
    if%success IS_SPECIAL_SYMBOL S frame_tag using S then
      result_success S false
    else result_success S b using S, runs, globals.

Definition SET_FRAME S x v :=
  add%stack "SET_FRAME" in
  read%env x_, x_env := x using S in
  let x_env := {|
      env_frame := v ;
      env_enclos := env_enclos x_env
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_env
    |} in
  write%defined x := x_ using S in
  result_skip S.

Definition addMissingVarsToNewEnv S (env addVars : SEXP) :=
  add%stack "addMissingVarsToNewEnv" in
  ifb addVars = R_NilValue then
    result_skip S
  else
    let%success addVars_type := TYPEOF S addVars using S in
    ifb addVars_type = EnvSxp then
      result_error S "Additional variables should be passed as a list."
    else
      read%list addVars_car, addVars_cdr, _ := addVars using S in
      fold%success aprev := addVars
      along addVars_cdr
      as a, _, _ do
        result_success S a using S, runs, globals in
      read%env _, env_env := env using S in
      set%cdr aprev := env_frame env_env using S in
      run%success SET_FRAME S env addVars using S in
      fold%let
      along addVars_cdr
      as endp, _, endp_list do
        let endTag := list_tagval endp_list in
        do%success (addVars, s, sprev) := (addVars, addVars, R_NilValue : SEXP)
        whileb s <> endp do
          read%list _, s_cdr, s_tag := s using S in
            ifb s_tag = endTag then
              ifb sprev = R_NilValue then
                let addVars := s_cdr in
                run%success SET_FRAME S env addVars using S in
                result_success S (addVars, s_cdr, sprev)
              else
                set_cdr S s_cdr sprev (fun S =>
                  result_success S (addVars, s_cdr, sprev))
            else result_success S (addVars, s_cdr, s) using S, runs in
        result_skip S using S, runs, globals.

Definition FRAME_LOCK_BIT := 14.

Definition FRAME_IS_LOCKED S rho :=
  add%stack "FRAME_IS_LOCKED" in
  read%defined rho_ := rho using S in
  result_success S (nth_bit FRAME_LOCK_BIT (gp rho_) ltac:(nbits_ok)).

Definition getActiveValue S f :=
  add%stack "getActiveValue" in
  let%success expr := lcons S f R_NilValue using S in
  runs_eval runs S expr R_GlobalEnv.

Definition SYMBOL_BINDING_VALUE S s :=
  add%stack "SYMBOL_BINDING_VALUE" in
  read%sym _, s_sym := s using S in
  if%success IS_ACTIVE_BINDING S s using S then
    getActiveValue S (sym_value s_sym)
  else result_success S (sym_value s_sym).

Definition setActiveValue S (vfun val : SEXP) :=
  add%stack "setActiveValue" in
  let%success arg_tail := lcons S val R_NilValue using S in
  let%success arg := lcons S R_QuoteSymbol arg_tail using S in
  let%success expr_tail := lcons S arg R_NilValue using S in
  let%success expr := lcons S vfun expr_tail using S in
  run%success runs_eval runs S expr R_GlobalEnv using S in
  result_skip S.

Definition SET_BINDING_VALUE S b val :=
  add%stack "SET_BINDING_VALUE" in
  if%success BINDING_IS_LOCKED S b using S then
    result_error S "Can not change value of locked binding."
  else
    if%success IS_ACTIVE_BINDING S b using S then
      read%list b_car, _, _ := b using S in
      setActiveValue S b_car val
    else
      set%car b := val using S in
      result_skip S.

Definition R_SetVarLocValue S vl value :=
  add%stack "R_SetVarLocValue" in
  SET_BINDING_VALUE S vl value.

Definition R_GetVarLocSymbol S vl :=
  add%stack "R_GetVarLocSymbol" in
  read%list _, _, vl_tag := vl using S in
  result_success S vl_tag.

Definition BINDING_VALUE S b :=
  add%stack "BINDING_VALUE" in
  read%list b_car, _, _ := b using S in
  if%success IS_ACTIVE_BINDING S b using S then
    getActiveValue S b_car
  else result_success S b_car.

Definition IS_USER_DATABASE S rho :=
  add%stack "IS_USER_DATABASE" in
  read%defined rho_ := rho using S in
  let%success inh := inherits S rho "UserDefinedDatabase" using S in
  result_success S (obj rho_ && inh).

Definition SET_SYMBOL_BINDING_VALUE S sym val :=
  add%stack "SET_SYMBOL_BINDING_VALUE" in
  if%success BINDING_IS_LOCKED S sym using S then
    result_error S "Cannot change value of locked binding."
  else if%success IS_ACTIVE_BINDING S sym using S then
    read%sym _, sym_sym := sym using S in
    setActiveValue S (sym_value sym_sym) val
  else SET_SYMVALUE S sym val.

Definition gsetVar S (symbol value rho : SEXP) : result unit :=
  add%stack "gsetVar" in
  if%success FRAME_IS_LOCKED S rho using S then
    read%sym symbol_, symbol_sym := symbol using S in
    ifb sym_value symbol_sym = R_UnboundValue then
      result_error S "Can not add such a binding to the base environment."
    else result_skip S in
  SET_SYMBOL_BINDING_VALUE S symbol value.

Definition defineVar S (symbol value rho : SEXP) : result unit :=
  add%stack "defineVar" in
  ifb rho = R_EmptyEnv then
    result_error S "Can not assign values in the empty environment."
  else if%success IS_USER_DATABASE S rho using S then
    result_not_implemented "R_ObjectTable"
  else ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
    gsetVar S symbol value rho
  else
    if%success IS_SPECIAL_SYMBOL S symbol using S then
      run%success SET_SPECIAL_SYMBOL S rho false using S in
      result_skip S in
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho using S in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifb list_tagval frame_list = symbol then
        run%success SET_BINDING_VALUE S frame value using S in
        run%success SET_MISSING S frame 0 ltac:(nbits_ok) using S in
        result_rreturn S tt
      else result_rskip S using S, runs, globals in
    if%success FRAME_IS_LOCKED S rho using S then
      result_error S "Can not add a binding to a locked environment."
    else
      let (S, l) := CONS S value (env_frame rho_env) in
      run%success SET_FRAME S rho l using S in
      set%tag l := symbol using S in
      result_skip S.

Definition setVarInFrame S (rho symbol value : SEXP) :=
  add%stack "setVarInFrame" in
  ifb rho = R_EmptyEnv then
    result_success S (R_NilValue : SEXP)
  else if%success IS_USER_DATABASE S rho using S then
    result_not_implemented "R_ObjectTable"
  else ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
    read%sym _, symbol_sym := symbol using S in
    ifb sym_value symbol_sym = R_UnboundValue then
      result_success S (R_NilValue : SEXP)
    else
      run%success SET_SYMBOL_BINDING_VALUE S symbol value using S in
      result_success S symbol
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho using S in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifb list_tagval frame_list = symbol then
        run%success SET_BINDING_VALUE S frame value using S in
        run%success SET_MISSING S frame 0 ltac:(nbits_ok) using S in
        result_rreturn S symbol
      else result_rskip S using S, runs, globals in
      result_success S (R_NilValue : SEXP).

Definition setVar S (symbol value rho : SEXP) :=
  add%stack "setVar" in
  do%return rho := rho
  whileb rho <> R_EmptyEnv do
    let%success vl :=
      setVarInFrame S rho symbol value using S in
    ifb vl <> R_NilValue then
      result_rreturn S tt
    else
      read%env rho_, rho_env := rho using S in
      result_rsuccess S (env_enclos rho_env)
  using S, runs in
  defineVar S symbol value R_GlobalEnv.

Definition findVarInFrame3 S rho symbol (doGet : bool) :=
  add%stack "findVarInFrame3" in
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type = NilSxp then
    result_error S "Use of NULL environment is defunct."
  else ifb rho = R_BaseNamespace \/ rho = R_BaseEnv then
    SYMBOL_BINDING_VALUE S symbol
  else ifb rho = R_EmptyEnv then
    result_success S (R_UnboundValue : SEXP)
  else
    if%success IS_USER_DATABASE S rho using S then
      result_not_implemented "R_ObjectTable"
    else
      (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
      read%defined rho_ := rho using S in
      let%env _, rho_env := rho_ using S in
      fold%return
      along env_frame rho_env
      as frame, _, frame_list do
        ifb list_tagval frame_list = symbol then
          let%success r := BINDING_VALUE S frame using S in
          result_rreturn S r
        else result_rskip S using S, runs, globals in
      result_success S (R_UnboundValue : SEXP).

Definition findVarInFrame S rho symbol :=
  add%stack "findVarInFrame" in
  findVarInFrame3 S rho symbol true.

Definition EnsureLocal S symbol rho :=
  add%stack "EnsureLocal" in
  let%success vl := findVarInFrame3 S rho symbol true using S in
  ifb vl <> R_UnboundValue then
    let%success vl := runs_eval runs S symbol rho using S in
    let%success vl :=
      if%success MAYBE_SHARED S vl using S then
        let%success vl := shallow_duplicate S vl using S in
        run%success defineVar S symbol vl rho using S in
        run%success INCREMENT_NAMED S vl using S in
        result_success S vl
      else result_success S vl using S in
    result_success S vl
  else
    read%env _, rho_env := rho using S in
    let%success vl := runs_eval runs S symbol (env_enclos rho_env) using S in
    ifb vl = R_UnboundValue then
      result_error S "Object not found."
    else
      let%success vl := shallow_duplicate S vl using S in
      run%success defineVar S symbol vl rho using S in
      run%success INCREMENT_NAMED S vl using S in
      result_success S vl.

Definition findVar S symbol rho :=
  add%stack "findVar" in
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type = NilSxp then
    result_error S "Use of NULL environment is defunct."
  else ifb rho_type <> EnvSxp then
    result_error S "Argument ‘rho’ is not an environment."
  else
    do%return rho := rho
    whileb rho <> R_EmptyEnv do
      let%success vl := findVarInFrame3 S rho symbol true using S in
      ifb vl <> R_UnboundValue then
        result_rreturn S vl
      else
        read%env _, rho_env := rho using S in
        result_rsuccess S (env_enclos rho_env) using S, runs in
    result_success S (R_UnboundValue : SEXP).

Definition findVarLocInFrame S (rho symbol : SEXP) :=
  add%stack "findVarLocInFrame" in
  ifb rho = R_BaseEnv \/ rho = R_BaseNamespace then
    result_error S "It can’t be used in the base environment."
  else ifb rho = R_EmptyEnv then
    result_success S (R_NilValue : SEXP)
  else if%success IS_USER_DATABASE S rho using S then
    unimplemented_function "R_ExternalPtrAddr"
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho using S in
    fold%return
    along env_frame rho_env
    as frame, _, frame_list do
      ifb list_tagval frame_list = symbol then
        result_rreturn S frame
      else result_rskip S using S, runs, globals in
    result_success S (R_NilValue : SEXP).

Definition R_findVarLocInFrame S rho symbol :=
  add%stack "R_findVarLocInFrame" in
  let%success binding := findVarLocInFrame S rho symbol using S in
  ifb binding = R_NilValue then
    result_success S NULL
  else result_success S binding.

Definition RemoveFromList S (thing list : SEXP) :=
  add%stack "RemoveFromList" in
  ifb list = R_NilValue then
    result_success S None
  else
    read%list _, list_cdr, list_tag := list using S in
    ifb list_tag = thing then
      set%car list := R_UnboundValue using S in
      run%success LOCK_BINDING S list using S in
      let rest := list_cdr in
      set%cdr list := R_NilValue using S in
      result_success S (Some rest)
    else
      let next := list_cdr in
      fold%return last := list
      along next
      as next, _, next_list do
        ifb list_tagval next_list = thing then
          set%car next := R_UnboundValue using S in
          run%success LOCK_BINDING S next using S in
          set%cdr last := list_cdrval next_list using S in
          set%cdr next := R_NilValue using S in
          result_rreturn S (Some list)
        else result_rsuccess S next using S, runs, globals in
      result_success S None.


Definition unbindVar S (symbol rho : SEXP) :=
  add%stack "unbindVar" in
  ifb rho = R_BaseNamespace then
    result_error S "Can’t unbind in the base namespace."
  else ifb rho = R_BaseEnv then
    result_error S "Unbinding in the base environment is unimplemented."
  else if%success FRAME_IS_LOCKED S rho using S then
    result_error S "Can’t remove bindings from a locked environment."
  else
    (** As we do not model hashtabs, we consider that the hashtab is not defined here. **)
    read%env _, rho_env := rho using S in
    if%defined list := RemoveFromList S symbol (env_frame rho_env) using S then
      SET_FRAME S rho list
    else result_skip S.

Definition ddVal S symbol :=
  add%stack "ddVal" in
  let%success symbol_name := PRINTNAME S symbol using S in
  let%success buf := CHAR S symbol_name using S in
  ifb substring 0 2 buf = ".."%string /\ String.length buf > 2 then
    let buf := substring 2 (String.length buf - 2) in
    unimplemented_function "strtol"
  else result_success S 0.

Definition ddfindVar (S : state) (symbol rho : SEXP) : result SEXP :=
  unimplemented_function "ddfindVar".


Definition findFun3 S symbol rho (call : SEXP) : result SEXP :=
  add%stack "findFun3" in
  let%success rho :=
    if%success IS_SPECIAL_SYMBOL S symbol using S then
      do%success rho := rho
      while let%success special := NO_SPECIAL_SYMBOLS S rho using S in
            result_success S (decide (rho <> R_EmptyEnv /\ special)) do
        read%env _, rho_env := rho using S in
        result_success S (env_enclos rho_env)
      using S, runs in
      result_success S rho
    else result_success S rho using S in
  do%return rho := rho
  whileb rho <> R_EmptyEnv do
    let%success vl := findVarInFrame3 S rho symbol true using S in
    run%return
      ifb vl <> R_UnboundValue then
        let%success vl_type := TYPEOF S vl using S in
        let%success vl :=
          ifb vl_type = PromSxp then
            runs_eval runs S vl rho
          else result_success S vl using S in
        let%success vl_type := TYPEOF S vl using S in
        ifb vl_type = CloSxp \/ vl_type = BuiltinSxp \/ vl_type = SpecialSxp then
          result_rreturn S vl
        else ifb vl = R_MissingArg then
          let%success str_symbol := PRINTNAME S symbol using S in
          let%success str_symbol_ := CHAR S str_symbol using S in
          result_error S ("Argument “" ++ str_symbol_ ++ "” is missing, with no default.")
        else result_rskip S
      else result_rskip S using S in
    read%env _, rho_env := rho using S in
    result_rsuccess S (env_enclos rho_env)
  using S, runs in
  let%success str_symbol := PRINTNAME S symbol using S in
  let%success str_symbol_ := CHAR S str_symbol using S in
  result_error S ("Could not find function “" ++ str_symbol_ ++ "”.").

Definition findRootPromise S p :=
  add%stack "findRootPromise" in
  let%success p_type := TYPEOF S p using S in
  ifb p_type = PromSxp then
    do%success p := p
    while
      let%success p := PREXPR S p using S in
      let%success p_type := TYPEOF S p using S in
      result_success S (decide (p_type = PromSxp))
    do
      PREXPR S p using S, runs in
    result_success S p
  else result_success S p.

Definition R_isMissing S (symbol rho : SEXP) :=
  add%stack "R_isMissing" in
  ifb symbol = R_MissingArg then
    result_success S true
  else
    let%success (s, ddv) :=
      if%success DDVAL S symbol using S then
        let%success d := ddVal S symbol using S in
        result_success S (R_DotsSymbol : SEXP, d)
      else result_success S (symbol, 0) using S in
    ifb rho = R_BaseEnv \/ rho = R_BaseNamespace then
      result_success S false
    else
      let%success vl := findVarLocInFrame S rho s using S in
      ifb vl <> R_NilValue then
        let%exit vl :=
          if%success DDVAL S symbol using S then
            read%list vl_car, _, _ := vl using S in
            let%success vl_car_len := R_length S vl_car using S in
            ifb vl_car_len < ddv \/ vl_car = R_MissingArg then
              result_rreturn S true
            else
              let%success n := nthcdr S vl_car (ddv - 1) using S in
              result_rsuccess S n
          else result_rsuccess S vl using S in
        let%success vl_mis := MISSING S vl using S in
        read%list vl_car, _, _ := vl using S in
        ifb vl_mis = true \/ vl_car = R_MissingArg then
          result_success S true
        else if%success IS_ACTIVE_BINDING S vl using S then
          result_success S false
        else
          let%success vl_car_rp := findRootPromise S vl_car using S in
          set%car vl := vl_car_rp using S in
          let vl_cat := vl_car_rp in
          let%success vl_car_type := TYPEOF S vl_car using S in
          ifb vl_car_type = PromSxp then
            read%prom _, vl_car_prom := vl_car using S in
            let%success vl_car_expr := PREXPR S vl_car using S in
            let%success vl_car_expr_type := TYPEOF S vl_car_expr using S in
            ifb prom_value vl_car_prom = R_UnboundValue /\ vl_car_expr_type = SymSxp then
              let%success vl_car_prseen := PRSEEN S vl_car using S in
              ifb vl_car_prseen = 1 then
                result_success S true
              else
                let%success oldseen := PRSEEN_direct S vl_car using S in
                run%success SET_PRSEEN S vl_car 1 ltac:(nbits_ok) using S in
                let%success val :=
                  let%success vl_car_prexpr := PREXPR S vl_car using S in
                  let%success vl_car_prenv := PRENV S vl_car using S in
                  runs_R_isMissing runs S vl_car_prexpr vl_car_prenv using S in
                run%success SET_PRSEEN_direct S vl_car oldseen using S in
                result_success S val
            else result_success S false
          else result_success S false
      else result_success S false.


(** ** altrep.c **)

(** The function names of this section corresponds to the function names
  in the file main/altrep.c. **)

(** The alternative representation ALTREP is meant to symbolically
  represent some operations, to avoid allocating trivial arrays into
  the memory.  The relevant code is however under active
  developpement, and it would not make sense to start formalising it
  right now.  We thus implement the following function using the
  traditionnal representation, although it needs more memory and time
  resources. **)

Definition new_compact_intseq S n (n1 inc : int) :=
  add%stack "new_compact_intseq" in
  ifb n = 1 then
    let (S, r) := ScalarInteger S n1 in
    result_success S r
  else ifb inc <> 1 /\ inc <> (-1)%Z then
    result_error S "Compact sequences can only have an increment of -1 or 1."
  else
    let%success ans := allocVector S IntSxp n using S in
    let generate :=
      fix generate start length :=
        match length with
        | 0 => nil
        | S length =>
          start :: generate (start + inc)%Z length
        end in
    write%VectorInteger ans := ArrayList.from_list (generate n1 n) using S in
    result_success S ans.

Definition new_compact_realseq S n (n1 inc : double) :=
  add%stack "new_compact_realseq" in
  ifb n = 1 then
    let (S, r) := ScalarReal S n1 in
    result_success S r
  else ifb inc <> 1 /\ inc <> (-1)%Z then
    result_error S "Compact sequences can only have an increment of -1 or 1."
  else
    let%success ans := allocVector S RealSxp n using S in
    let generate :=
      fix generate start length :=
        match length with
        | 0 => nil
        | S length =>
          start :: generate (Double.add start inc) length
        end in
    write%VectorReal ans := ArrayList.from_list (generate n1 n) using S in
    result_success S ans.

Definition R_compact_intrange S (n1 n2 : nat) :=
  add%stack "R_compact_intrange" in
  let n :=
    ifb n1 <= n2 then
      n2 - n1 + 1
    else n1 - n2 + 1 in
  ifb (n1 : int) <= INT_MIN \/ (n1 : int) > INT_MAX
      \/ (n2 : int) <= INT_MIN \/ (n2 : int) > INT_MAX then
    new_compact_realseq S n n1 (ifb n1 <= n2 then 1 else (-1)%Z)
  else new_compact_intseq S n n1 (ifb n1 <= n2 then 1 else (-1)%Z).


(** ** utils.c **)

(** The function names of this section corresponds to the function names
  in the file main/utils.c. **)

Definition truenames : list string :=
  ["T"; "True"; "TRUE"; "true"]%string.

Definition StringTrue name :=
  decide (Mem name truenames).

Definition falsenames : list string :=
  ["F"; "False"; "FALSE"; "false"]%string.

Definition StringFalse name :=
  decide (Mem name falsenames).

Definition isspace c :=
  decide (Mem c [" " ; "009" (** '\t' **) ; "010" (** '\n' **) ; "011" (** '\v' **) ; "012" (** '\f' **) ; "013" (** '\r' **)]%char).

Definition isBlankString s :=
  decide (Forall (fun c => isspace c) (string_to_list s)).


(** ** coerce.c **)

(** The function names of this section corresponds to the function names
  in the file main/coerce.c. **)

Definition LogicalFromString S (x : SEXP) :=
  add%stack "LogicalFromString" in
  ifb x <> R_NaString then
    let%success c := CHAR S x using S in
    if StringTrue c then result_success S (1 : int)
    else if StringFalse c then result_success S (0 : int)
    else result_success S NA_LOGICAL
  else result_success S NA_LOGICAL.

Definition LogicalFromInteger S (x : int) : result int :=
  add%stack "LogicalFromInteger" in
  ifb x = NA_INTEGER then result_success S NA_LOGICAL
  else result_success S (decide (x <> 0) : int).

Definition LogicalFromReal S x : result int :=
  add%stack "LogicalFromReal" in
  ifb ISNAN x then result_success S NA_LOGICAL
  else result_success S (negb (Double.is_zero x) : int).

Definition LogicalFromComplex S x : result int :=
  add%stack "LogicalFromComplex" in
  ifb ISNAN (Rcomplex_r x) \/ ISNAN (Rcomplex_i x) then result_success S NA_LOGICAL
  else result_success S (decide (~ Double.is_zero (Rcomplex_r x)
                                 \/ ~ Double.is_zero (Rcomplex_i x)) : int).

Definition asLogical S x :=
  add%stack "asLogical" in
  if%success isVectorAtomic S x using S then
    let%success len := XLENGTH S x using S in
    ifb len < 1 then
      result_success S NA_LOGICAL
    else
      read%defined x_ := x using S in
      match type x_ with
      | LglSxp => LOGICAL_ELT S x 0
      | IntSxp =>
        let%success i := INTEGER_ELT S x 0 using S in
        LogicalFromInteger S i
      | RealSxp =>
        let%success r := REAL_ELT S x 0 using S in
        LogicalFromReal S r
      | CplxSxp =>
        let%success c := COMPLEX_ELT S x 0 using S in
        LogicalFromComplex S c
      | StrSxp =>
        let%success s := STRING_ELT S x 0 using S in
        LogicalFromString S s
      | RawSxp =>
        let%success s := RAW_ELT S x 0 using S in
        LogicalFromString S s
      | _ => result_error S "Unimplemented type."
      end
  else
    let%success x_type := TYPEOF S x using S in
    ifb x_type = CharSxp then
      LogicalFromString S x
    else result_success S NA_LOGICAL.

Definition IntegerFromString S (x : SEXP) :=
  add%stack "IntegerFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR S x using S in
      result_success S (negb (isBlankString c))
    else result_success S false using S then
    unimplemented_function "R_strtod."
  else result_success S NA_INTEGER.

Definition IntegerFromLogical x :=
  ifb x = NA_LOGICAL then
    NA_INTEGER
  else x.

Definition IntegerFromReal x :=
  if ISNAN x then
    NA_INTEGER
  else ifb x >= Double.add (int_to_double (INT_MAX)) (1 : double) \/ x <= (INT_MIN : double) then
    (* A warning has been formalised out here. *)
    NA_INTEGER
  else Double.double_to_int_zero x.

Definition IntegerFromComplex x :=
  ifb ISNAN (Rcomplex_r x) \/ ISNAN (Rcomplex_i x) then
    NA_INTEGER
  else ifb (Rcomplex_r x) >= Double.add (int_to_double (INT_MAX)) (1 : double) \/ (Rcomplex_r x) <= (INT_MIN : double) then
    (* A warning has been formalised out here. *)
    NA_INTEGER
  else Double.double_to_int_zero (Rcomplex_r x).

Definition asInteger S x :=
  add%stack "asInteger" in
  let%success t := TYPEOF S x using S in
  if%success
      if%success isVectorAtomic S x using S then
        let%success l := XLENGTH S x using S in
        result_success S (decide (l >= 1))
      else result_success S false using S then
    match t with
    | LglSxp =>
      read%Logical x0 := x at 0 using S in
      result_success S (IntegerFromLogical x0)
    | IntSxp =>
      read%Integer x0 := x at 0 using S in
      result_success S x0
    | RealSxp =>
      read%Real x0 := x at 0 using S in
      result_success S (IntegerFromReal x0)
    | CplxSxp =>
      read%Complex x0 := x at 0 using S in
      result_success S (IntegerFromComplex x0)
    | StrSxp =>
      read%Pointer x0 := x at 0 using S in
      IntegerFromString S x0
    | _ => result_error S "Unimplemented type."
    end
  else ifb t = CharSxp then
    IntegerFromString S x
  else result_success S NA_INTEGER.

Definition RealFromLogical x :=
  ifb x = NA_LOGICAL then
    NA_REAL
  else (x : double).

Definition RealFromInteger x :=
  ifb x = NA_INTEGER then
    NA_REAL
  else (x : double).

Definition RealFromComplex x :=
  ifb ISNAN (Rcomplex_r x) \/ ISNAN (Rcomplex_i x) then
    NA_REAL
  else if ISNAN (Rcomplex_r x) then
    Rcomplex_r x
  else if ISNAN (Rcomplex_i x) then
    NA_REAL
  else Rcomplex_r x.

Definition RealFromString S (x : SEXP) :=
  add%stack "RealFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR S x using S in
      result_success S (negb (isBlankString c))
    else result_success S false using S then
    unimplemented_function "R_strtod."
  else result_success S NA_REAL.

Definition asReal S x :=
  add%stack "asReal" in
  let%success t := TYPEOF S x using S in
  if%success
      if%success isVectorAtomic S x using S then
        let%success l := XLENGTH S x using S in
        result_success S (decide (l >= 1))
      else result_success S false using S then
    match t with
    | LglSxp =>
      read%Logical x0 := x at 0 using S in
      result_success S (RealFromLogical x0)
    | IntSxp =>
      read%Integer x0 := x at 0 using S in
      result_success S (RealFromInteger x0)
    | RealSxp =>
      read%Real x0 := x at 0 using S in
      result_success S x0
    | CplxSxp =>
      read%Complex x0 := x at 0 using S in
      result_success S (RealFromComplex x0)
    | StrSxp =>
      read%Pointer x0 := x at 0 using S in
      RealFromString S x0
    | _ => result_error S "Unimplemented type."
    end
  else ifb t = CharSxp then
    RealFromString S x
  else result_success S NA_REAL.

Definition coerceSymbol S v type :=
  add%stack "coerceSymbol" in
  let%success rval :=
    ifb type = ExprSxp then
      let%success rval := allocVector S type 1 using S in
      run%success SET_VECTOR_ELT S rval 0 v using S in
      result_success S rval
    else ifb type = CharSxp then
      PRINTNAME S v
    else ifb type = StrSxp then
      let%success v_name := PRINTNAME S v using S in
      ScalarString S v_name
    else
      (* A warning has been formalised out here. *)
      result_success S (R_NilValue : SEXP) using S in
  result_success S rval.

Definition PairToVectorList (S : state) (x : SEXP) : result SEXP :=
  unimplemented_function "PairToVectorList".

Definition ComplexFromString S (x : SEXP) :=
  add%stack "ComplexFromString" in
  if%success
    ifb x <> R_NaString then
      let%success c := CHAR S x using S in
      result_success S (negb (isBlankString c))
    else result_success S false using S then
    unimplemented_function "R_strtod."
  else result_success S (make_Rcomplex NA_REAL NA_REAL).

Definition ComplexFromLogical x :=
  ifb x = NA_LOGICAL then
    make_Rcomplex NA_REAL NA_REAL
  else make_Rcomplex x 0.

Definition ComplexFromInteger x :=
  ifb x = NA_INTEGER then
    make_Rcomplex NA_REAL NA_REAL
  else make_Rcomplex x 0.

Definition ComplexFromReal x :=
  make_Rcomplex x 0.

Definition asComplex S x :=
  add%stack "asComplex" in
  let%success x_va := isVectorAtomic S x using S in
  let%success x_len := XLENGTH S x using S in
  let%success x_type := TYPEOF S x using S in
  ifb x_va /\ x_len >= 1 then
    match x_type with
    | LglSxp =>
      let%success x_0 := LOGICAL_ELT S x 0 using S in
      result_success S (ComplexFromLogical x_0)
    | IntSxp =>
      let%success x_0 := INTEGER_ELT S x 0 using S in
      result_success S (ComplexFromInteger x_0)
    | RealSxp =>
      let%success x_0 := REAL_ELT S x 0 using S in
      result_success S (ComplexFromReal x_0)
    | CplxSxp =>
      COMPLEX_ELT S x 0
    | StrSxp =>
      let%success x_0 := STRING_ELT S x 0 using S in
      ComplexFromString S x_0
    | _ =>
      result_error S "Unimplemented type."
    end
  else ifb x_type = CharSxp then
    ComplexFromString S x
  else result_success S (make_Rcomplex NA_REAL NA_REAL).

Definition coercePairList S v type :=
  add%stack "coercePairList" in
  let%exit (rval, n) :=
    ifb type = ListSxp then
      result_rreturn S v
    else ifb type = ExprSxp then
      let%success rval := allocVector S type 1 using S in
      run%success SET_VECTOR_ELT S rval 0 v using S in
      result_rreturn S rval
    else ifb type = StrSxp then
      let%success n := R_length S v using S in
      let%success rval := allocVector S type n using S in
      fold%success i := 0
      along v
      as v_car, _ do
        let%success v_car_is := isString S v_car using S in
        let%success v_car_len := R_length S v_car using S in
        run%success
          ifb v_car_is /\ v_car_len = 1 then
            let%success v_car_0 := STRING_ELT S v_car 0 using S in
            SET_STRING_ELT S rval i v_car_0
          else unimplemented_function "deparse1line" using S in
        result_success S (1 + i) using S, runs, globals in
      result_rsuccess S (rval, n)
    else ifb type = VecSxp then
      let%success rval := PairToVectorList S v using S in
      result_rreturn S rval
    else if%success isVectorizable S v using S then
      let%success n := R_length S v using S in
      let%success rval := allocVector S type n using S in
      run%success
        match type with
        | LglSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp using S in
            let%success vp_car_lgl := asLogical S vp_car using S in
            write%Logical rval at i := vp_car_lgl using S in
            result_success S vp_cdr using S
        | IntSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp using S in
            let%success vp_car_lgl := asInteger S vp_car using S in
            write%Integer rval at i := vp_car_lgl using S in
            result_success S vp_cdr using S
        | RealSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp using S in
            let%success vp_car_lgl := asReal S vp_car using S in
            write%Real rval at i := vp_car_lgl using S in
            result_success S vp_cdr using S
        | CplxSxp =>
          do%let vp := v
          for i from 0 to n - 1 do
            read%list vp_car, vp_cdr, _ := vp using S in
            let%success vp_car_lgl := asComplex S vp_car using S in
            write%Complex rval at i := vp_car_lgl using S in
            result_success S vp_cdr using S
        | RawSxp => result_not_implemented "Raw case."
        | _ => result_error S "Unimplemented type."
        end using S in
      result_rsuccess S (rval, n)
    else result_error S "‘pairlist’ object cannot be coerce as-is." using S in
  fold%success i := false
  along v
  as _, v_tag do
    ifb v_tag <> R_NilValue then
      result_success S true
    else result_success S i using S, runs, globals in
  run%success
    if i then
      let%success names := allocVector S StrSxp n using S in
      fold%success i := 0
      along v
      as _, v_tag do
        run%success
          ifb v_tag <> R_NilValue then
            let%success v_tag_name := PRINTNAME S v_tag using S in
            SET_STRING_ELT S names i v_tag_name
          else result_skip S using S in
        result_success S (1 + i) using S, runs, globals in
      result_skip S
    else result_skip S using S in
  result_success S rval.

Definition coerceVectorList (S : state) (v : SEXP) (type : SExpType) : result SEXP :=
  unimplemented_function "coerceVectorList".

Definition StringFromLogical S x :=
  add%stack "StringFromLogical" in
  ifb x = NA_LOGICAL then
    result_success S (NA_STRING : SEXP)
  else
    let (S, r) := mkChar S (EncodeLogical x) in
    result_success S r.

Definition StringFromInteger S x :=
  add%stack "StringFromInteger" in
  ifb x = NA_INTEGER then
    result_success S (NA_STRING : SEXP)
  else unimplemented_function "formatInteger".

Definition StringFromComplex S x :=
  add%stack "StringFromComplex" in
  ifb R_IsNA (Rcomplex_r x) \/ R_IsNA (Rcomplex_i x) then
    result_success S (NA_STRING : SEXP)
  else unimplemented_function "EncodeComplex".

Definition coerceToSymbol S v :=
  add%stack "coerceToSymbol" in
  let%success v_len := R_length S v using S in
  ifb v_len <= 0 then
    result_error S "Invalid data."
  else
    let%success v_type := TYPEOF S v using S in
    let%success ans :=
      match v_type with
      | LglSxp =>
        let%success v_0 := LOGICAL_ELT S v 0 using S in
        StringFromLogical S v_0
      | IntSxp =>
        let%success v_0 := INTEGER_ELT S v 0 using S in
        StringFromInteger S v_0
      | RealSxp =>
        let%success v_0 := REAL_ELT S v 0 using S in
        StringFromReal S v_0
      | CplxSxp =>
        let%success v_0 := COMPLEX_ELT S v 0 using S in
        StringFromComplex S v_0
      | StrSxp =>
        STRING_ELT S v 0
      | RawSxp => result_not_implemented "Raw case."
      | _ => result_error S "Unimplemented type."
      end using S in
    installTrChar S ans.

Definition coerceToLogical S v :=
  add%stack "coerceToLogical" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector S LglSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        let%success pa_i := LogicalFromInteger S v_i using S in
        write%Logical ans at i := pa_i using S in
        result_skip S using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        let%success pa_i := LogicalFromReal S v_i using S in
        write%Logical ans at i := pa_i using S in
        result_skip S using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        let%success pa_i := LogicalFromComplex S v_i using S in
        write%Logical ans at i := pa_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success pa_i := LogicalFromString S v_i using S in
        write%Logical ans at i := pa_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToInteger S v :=
  add%stack "coerceToInteger" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector S IntSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        write%Integer ans at i := IntegerFromLogical v_i using S in
        result_skip S using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        write%Integer ans at i := IntegerFromReal v_i using S in
        result_skip S using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        write%Integer ans at i := IntegerFromComplex v_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success pa_i := IntegerFromString S v_i using S in
        write%Integer ans at i := pa_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToReal S v :=
  add%stack "coerceToReal" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector S RealSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        write%Real ans at i := RealFromLogical v_i using S in
        result_skip S using S
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        write%Real ans at i := RealFromInteger v_i using S in
        result_skip S using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        write%Real ans at i := RealFromComplex v_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success pa_i := RealFromString S v_i using S in
        write%Real ans at i := pa_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToComplex S v :=
  add%stack "coerceToComplex" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector S CplxSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        write%Complex ans at i := ComplexFromLogical v_i using S in
        result_skip S using S
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        write%Complex ans at i := ComplexFromInteger v_i using S in
        result_skip S using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        write%Complex ans at i := ComplexFromReal v_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success pa_i := ComplexFromString S v_i using S in
        write%Complex ans at i := pa_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToRaw (S : state) (v : SEXP) : result SEXP :=
  unimplemented_function "coerceToRaw".

Definition coerceToString S v :=
  add%stack "coerceToString" in
  let%success n := XLENGTH S v using S in
  let%success ans := allocVector S StrSxp n using S in
  run%success SHALLOW_DUPLICATE_ATTRIB S ans v using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        let%success s_i := StringFromLogical S v_i using S in
        SET_STRING_ELT S ans i s_i using S
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        let%success s_i := StringFromInteger S v_i using S in
        SET_STRING_ELT S ans i s_i using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        let%success s_i := StringFromReal S v_i using S in
        SET_STRING_ELT S ans i s_i using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        let%success s_i := StringFromComplex S v_i using S in
        SET_STRING_ELT S ans i s_i using S
    | RawSxp => result_not_implemented "Raw case."
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  result_success S ans.

Definition coerceToExpression S v :=
  add%stack "coerceToExpression" in
  let%success ans :=
    if%success isVectorAtomic S v using S then
      let%success n := XLENGTH S v using S in
      let%success ans := allocVector S ExprSxp n using S in
      let%success v_type := TYPEOF S v using S in
      run%success
        match v_type with
        | LglSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := LOGICAL_ELT S v i using S in
            run%success SET_VECTOR_ELT S ans i (ScalarLogical v_i) using S in
            result_skip S using S
        | IntSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := INTEGER_ELT S v i using S in
            let (S, s_i) := ScalarInteger S v_i in
            run%success SET_VECTOR_ELT S ans i s_i using S in
            result_skip S using S
        | RealSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := REAL_ELT S v i using S in
            let (S, s_i) := ScalarReal S v_i in
            run%success SET_VECTOR_ELT S ans i s_i using S in
            result_skip S using S
        | CplxSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := COMPLEX_ELT S v i using S in
            let (S, s_i) := ScalarComplex S v_i in
            run%success SET_VECTOR_ELT S ans i s_i using S in
            result_skip S using S
        | StrSxp =>
          do%let
          for i from 0 to n - 1 do
            let%success v_i := STRING_ELT S v i using S in
            let%success s_i := ScalarString S v_i using S in
            run%success SET_VECTOR_ELT S ans i s_i using S in
            result_skip S using S
        | RawSxp => result_not_implemented "Raw case."
        | _ =>
          result_error S "Unimplemented type."
        end using S in
      result_success S ans
    else
      let%success ans := allocVector S ExprSxp 1 using S in
      let%success v_d := duplicate S v using S in
      run%success SET_VECTOR_ELT S ans 0 v_d using S in
      result_success S ans using S in
  result_success S ans.

Definition coerceToVectorList S v :=
  add%stack "coerceToVectorList" in
  let%success n := xlength S v using S in
  let%success ans := allocVector S VecSxp n using S in
  let%success v_type := TYPEOF S v using S in
  run%success
    match v_type with
    | LglSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := LOGICAL_ELT S v i using S in
        run%success SET_VECTOR_ELT S ans i (ScalarLogical v_i) using S in
        result_skip S using S
    | IntSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := INTEGER_ELT S v i using S in
        let (S, s_i) := ScalarInteger S v_i in
        run%success SET_VECTOR_ELT S ans i s_i using S in
        result_skip S using S
    | RealSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := REAL_ELT S v i using S in
        let (S, s_i) := ScalarReal S v_i in
        run%success SET_VECTOR_ELT S ans i s_i using S in
        result_skip S using S
    | CplxSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := COMPLEX_ELT S v i using S in
        let (S, s_i) := ScalarComplex S v_i in
        run%success SET_VECTOR_ELT S ans i s_i using S in
        result_skip S using S
    | StrSxp =>
      do%let
      for i from 0 to n - 1 do
        let%success v_i := STRING_ELT S v i using S in
        let%success s_i := ScalarString S v_i using S in
        run%success SET_VECTOR_ELT S ans i s_i using S in
        result_skip S using S
    | RawSxp => result_not_implemented "Raw case."
    | ListSxp
    | LangSxp =>
      do%success tmp := v
      for i from 0 to n - 1 do
        read%list tmp_car, tmp_cdr, _ := tmp using S in
        run%success SET_VECTOR_ELT S ans i tmp_car using S in
        result_success S tmp_cdr using S in
      result_skip S
    | _ =>
      result_error S "Unimplemented type."
    end using S in
  let%success tmp := runs_getAttrib runs S v R_NamesSymbol using S in
  run%success
    ifb tmp <> R_NilValue then
      run%success runs_setAttrib runs S ans R_NamesSymbol tmp using S in
      result_skip S
    else result_skip S using S in
  result_success S ans.

Definition coerceToPairList S v :=
  add%stack "coerceToPairList" in
  let%success n := LENGTH S v using S in
  let (S, ans) := allocList S n in
  do%success ansp := ans
  for i from 0 to n - 1 do
    read%list _, ansp_cdr, _ := ansp using S in
    run%success
      let%success v_type := TYPEOF S v using S in
      match v_type with
      | LglSxp =>
        let%success ansp_car := allocVector S LglSxp 1 using S in
        set%car ansp := ansp_car using S in
        let%success v_i := LOGICAL_ELT S v i using S in
        write%Logical ansp_car at 0 := v_i using S in
        result_skip S
      | IntSxp =>
        let%success ansp_car := allocVector S IntSxp 1 using S in
        set%car ansp := ansp_car using S in
        let%success v_i := INTEGER_ELT S v i using S in
        write%Integer ansp_car at 0 := v_i using S in
        result_skip S
      | RealSxp =>
        let%success ansp_car := allocVector S RealSxp 1 using S in
        set%car ansp := ansp_car using S in
        let%success v_i := REAL_ELT S v i using S in
        write%Real ansp_car at 0 := v_i using S in
        result_skip S
      | CplxSxp =>
        let%success ansp_car := allocVector S CplxSxp 1 using S in
        set%car ansp := ansp_car using S in
        let%success v_i := COMPLEX_ELT S v i using S in
        write%Complex ansp_car at 0 := v_i using S in
        result_skip S
      | StrSxp =>
        let%success v_i := STRING_ELT S v i using S in
        let%success ansp_car := ScalarString S v_i using S in
        set%car ansp := ansp_car using S in
        result_skip S
      | RawSxp => result_not_implemented "Raw case."
      | VecSxp =>
        let%success v_i := VECTOR_ELT S v i using S in
        set%car ansp := v_i using S in
        result_skip S
      | ExprSxp =>
        let%success v_i := VECTOR_ELT S v i using S in
        set%car ansp := v_i using S in
        result_skip S
      | _ =>
        result_error S "Unimplemented type."
      end using S in
    result_success S ansp_cdr using S in
  let%success ansp := runs_getAttrib runs S v R_NamesSymbol using S in
  run%success
    ifb ansp <> R_NilValue then
      run%success runs_setAttrib runs S ans R_NamesSymbol ansp using S in
      result_skip S
    else result_skip S using S in
  result_success S ans.

Definition coerceVector S v type :=
  add%stack "coerceVector" in
  let%success v_type := TYPEOF S v using S in
  ifb v_type = type then
    result_success S v
  else
    let%success v_s4 := IS_S4_OBJECT S v using S in
    let%exit v :=
      ifb v_s4 /\ v_type = S4Sxp then
        unimplemented_function "R_getS4DataSlot"
      else result_rsuccess S v using S in
    let%success ans :=
      let%success v_type := TYPEOF S v using S in
      match v_type with
      | SymSxp =>
        coerceSymbol S v type
      | NilSxp
      | ListSxp =>
        coercePairList S v type
      | LangSxp =>
        ifb type <> StrSxp then
          coercePairList S v type
        else
          let%success n := R_length S v using S in
          let%success ans := allocVector S type n using S in
          ifb n = 0 then
            result_success S ans
          else
            read%list v_car, v_cdr, _ := v using S in
            let op := v_car in
            let%success op_type := TYPEOF S op using S in
            let%success (i, v) :=
              ifb op_type = SymSxp then
                let%success op_name := PRINTNAME S op using S in
                run%success SET_STRING_ELT S ans 0 op_name using S in
                result_success S (1, v_cdr)
              else result_success S (0, v) using S in
            fold%success i := i
            along v
            as v_car, _ do
              let%success v_car_is := isString S v_car using S in
              let%success v_car_len := R_length S v_car using S in
              run%success
                ifb v_car_is /\ v_car_len = 1 then
                  let%success v_car_0 := STRING_ELT S v_car 0 using S in
                  SET_STRING_ELT S ans i v_car_0
                else unimplemented_function "deparse1line" using S in
              result_success S (1 + i) using S, runs, globals in
            result_success S ans
      | VecSxp
      | ExprSxp =>
        coerceVectorList S v type
      | EnvSxp =>
        result_error S "Environments can not be coerced."
      | LglSxp
      | IntSxp
      | RealSxp
      | CplxSxp
      | StrSxp
      | RawSxp =>
        match type with
        | SymSxp => coerceToSymbol S v
        | LglSxp => coerceToLogical S v
        | IntSxp => coerceToInteger S v
        | RealSxp => coerceToReal S v
        | CplxSxp => coerceToComplex S v
        | RawSxp => coerceToRaw S v
        | StrSxp => coerceToString S v
        | ExprSxp => coerceToExpression S v
        | VecSxp => coerceToVectorList S v
        | ListSxp => coerceToPairList S v
        | _ =>
          result_error S "Cannot coerce to this type."
        end
      | _ =>
        result_error S "Cannot coerce this type to this other type."
      end using S in
    result_success S ans.

Definition CreateTag S x :=
  add%stack "CreateTag" in
  let%success x_n := isNull S x using S in
  let%success x_sy := isSymbol S x using S in
  ifb x_n \/ x_sy then
    result_success S x
  else
    if%success
        let%success x_st := isString S x using S in
        let%success x_len := R_length S x using S in
        ifb x_st /\ x_len >= 1 then
          let%success x_0 := STRING_ELT S x 0 using S in
          let%success x_0_len := R_length S x_0 using S in
          result_success S (decide (x_0_len >= 1))
        else result_success S false using S then
      let%success x_0 := STRING_ELT S x 0 using S in
      installTrChar S x_0
    else unimplemented_function "deparse1".

Definition copyDimAndNames S x ans :=
  add%stack "copyDimAndNames" in
  if%success isVector S x using S then
    let%success dims := runs_getAttrib runs S x R_DimSymbol using S in
    run%success
      ifb dims <> R_NilValue then
        run%success runs_setAttrib runs S ans R_DimSymbol dims using S in
        result_skip S
      else result_skip S using S in
    if%success isArray S x using S then
      let%success names := runs_getAttrib runs S x R_DimNamesSymbol using S in
      ifb names <> R_NilValue then
        run%success runs_setAttrib runs S ans R_DimNamesSymbol names using S in
        result_skip S
      else result_skip S
    else
      let%success names := runs_getAttrib runs S x R_NamesSymbol using S in
      ifb names <> R_NilValue then
        run%success runs_setAttrib runs S ans R_NamesSymbol names using S in
        result_skip S
      else result_skip S
  else result_skip S.


(** ** attrib.c **)

(** The function names of this section corresponds to the function names
  in the file main/attrib.c. **)

Definition isOneDimensionalArray S vec :=
  add%stack "isOneDimensionalArray" in
  let%success ivec := isVector S vec using S in
  let%success ilist := isList S vec using S in
  let%success ilang := isLanguage S vec using S in
  ifb ivec \/ ilist \/ ilang then
    let%success s := runs_getAttrib runs S vec R_DimSymbol using S in
    let%success s_type := TYPEOF S s using S in
    ifb s_type = IntSxp then
      let%success s_len := R_length S s using S in
      ifb s_len = 1 then result_success S true
      else result_success S false
    else result_success S false
  else result_success S false.

Definition getAttrib0 S (vec name : SEXP) :=
  add%stack "getAttrib0" in
  run%exit
    ifb name = R_NamesSymbol then
      run%return
        if%success isOneDimensionalArray S vec using S then
          let%success s := runs_getAttrib runs S vec R_DimNamesSymbol using S in
          let%success s_null := isNull S s using S in
          if negb s_null then
            read%Pointer s_0 := s at 0 using S in
            run%success MARK_NOT_MUTABLE S s_0 using S in
            result_rreturn S s_0
          else result_rskip S
        else result_rskip S using S in
      let%success vec_list := isList S vec using S in
      let%success vec_lang := isLanguage S vec using S in
      ifb vec_list \/ vec_lang then
        let%success len := R_length S vec using S in
        let%success s := allocVector S StrSxp len using S in
        fold%success (i, any) := (0, false)
        along vec
        as _, vec_tag do
          let%success any :=
            ifb vec_tag = R_NilValue then
              run%success SET_STRING_ELT S s i R_BlankString using S in
              result_success S any
            else if%success isSymbol S vec_tag using S then
              let%success vec_name := PRINTNAME S vec_tag using S in
              run%success SET_STRING_ELT S s i vec_name using S in
              result_success S true
            else result_error S "Invalid type for TAG." using S in
          result_success S (1 + i, any) using S, runs, globals in
        if any then
          let%success s_null := isNull S s using S in
          run%success
            if negb s_null then
              MARK_NOT_MUTABLE S s
            else result_skip S using S in
          result_rreturn S s
        else result_rreturn S (R_NilValue : SEXP)
      else result_rskip S
    else result_rskip S using S in
  let%success vec_attr := ATTRIB S vec using S in
  fold%return
  along vec_attr
  as s_car, s_tag do
    ifb s_tag = name then
      let%success s_car_type := TYPEOF S s_car using S in
      ifb name = R_DimNamesSymbol /\ s_car_type = ListSxp then
        result_error S "Old list is no longer allowed for dimnames attributes."
      else
        run%success MARK_NOT_MUTABLE S s_car using S in
        result_rreturn S s_car
    else result_rskip S using S, runs, globals in
  result_success S (R_NilValue : SEXP).

Definition getAttrib S (vec name : SEXP) :=
  add%stack "getAttrib" in
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "Can not have attributes on a CharSxp."
  else
    let%success vec_attr := ATTRIB S vec using S in
    ifb vec_attr = R_NilValue /\ ~ (vec_type  = ListSxp \/ vec_type  = LangSxp) then
      result_success S (R_NilValue : SEXP)
    else
      let%success name :=
        if%success isString S name using S then
          let%success name_0 := STRING_ELT S name 0 using S in
          let%success name_sym := installTrChar S name_0 using S in
          result_success S name_sym
        else result_success S name using S in
      ifb name = R_RowNamesSymbol then
        let%success s := getAttrib0 S vec name using S in
        let%success s_in := isInteger S s using S in
        let%success s_len := LENGTH S s using S in
        ifb s_in /\ s_len = 2 then
          read%Integer s_0 := s at 0 using S in
          ifb s_0 = NA_INTEGER then
            read%Integer s_1 := s at 1 using S in
            let n := abs s_1 in
            ifb n > 0 then
              R_compact_intrange S 1 n
            else allocVector S IntSxp 0
          else result_success S s
        else result_success S s
      else getAttrib0 S vec name.

Definition installAttrib S vec name val :=
  add%stack "installAttrib" in
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "Cannot set attribute on a CharSxp."
  else ifb vec_type = SymSxp then
    result_error S "Cannot set attribute on a symbol."
  else
    let%success vec_attr := ATTRIB S vec using S in
    fold%return t := R_NilValue : SEXP
    along vec_attr
    as s, _, s_list do
      ifb list_tagval s_list = name then
        set%car s := val using S in
        result_rreturn S val
      else result_rsuccess S s
    using S, runs, globals in
    let (S, s) := CONS S val R_NilValue in
    set%tag s := name using S in
    run%success
      ifb vec_attr = R_NilValue then
        run%success SET_ATTRIB S vec s using S in
        result_skip S
      else
        set%cdr t := s using S in
        result_skip S using S in
    result_success S val.

Definition stripAttrib S (tag lst : SEXP) :=
  add%stack "stripAttrib" in
  ifb lst = R_NilValue then
    result_success S lst
  else
    read%list _, lst_cdr, lst_tag := lst using S in
    ifb tag = lst_tag then
      runs_stripAttrib runs S tag lst_cdr
    else
      let%success r :=
        runs_stripAttrib runs S tag lst_cdr using S in
      set%cdr lst := r using S in
      result_success S lst.

Definition removeAttrib S (vec name : SEXP) :=
  add%stack "removeAttrib" in
  let%success vec_type := TYPEOF S vec using S in
  ifb vec_type = CharSxp then
    result_error S "Cannot set attribute on a CharSxp."
  else
    let%success vec_pl := isPairList S vec using S in
    ifb name = R_NamesSymbol /\ vec_pl then
      fold%success
      along vec
      as t, _, _ do
        set%tag t := R_NilValue using S in
        result_skip S
      using S, runs, globals in
      result_success S (R_NilValue : SEXP)
    else
      run%success
        ifb name = R_DimSymbol then
          let%success r :=
            let%success vec_attr := ATTRIB S vec using S in
            stripAttrib S R_DimNamesSymbol vec_attr using S in
          run%success SET_ATTRIB S vec r using S in
          result_skip S
        else result_skip S using S in
      let%success r :=
        let%success vec_attr := ATTRIB S vec using S in
        stripAttrib S name vec_attr using S in
      run%success SET_ATTRIB S vec r using S in
      run%success
        ifb name = R_ClassSymbol then
          set%obj vec := false using S in
          result_skip S
        else result_skip S using S in
      result_success S (R_NilValue : SEXP).

Definition checkNames S x s :=
  add%stack "checkNames" in
  let%success x_vec := isVector S x using S in
  let%success x_list := isList S x using S in
  let%success x_lang := isLanguage S x using S in
  ifb x_vec \/ x_list \/ x_lang then
    let%success s_vec := isVector S s using S in
    let%success s_list := isList S s using S in
    ifb ~ s_vec /\ ~ s_list then
      result_error S "Invalid type for ‘names’: must be a vector."
    else
      let%success x_len := xlength S x using S in
      let%success s_len := xlength S s using S in
      ifb x_len <> x_len then
        result_error S "‘names’ attribute must be the same length as the vector."
      else result_skip S
  else if%success IS_S4_OBJECT S x using S then
    result_skip S
  else result_error S "‘names’ applied to a non-vector.".

Definition classgets S (vec klass : SEXP) :=
  add%stack "classgets" in
  let%success klass_null := isNull S klass using S in
  let%success klass_str := isString S klass using S in
  ifb klass_null \/ klass_str then
    let%success ncl := R_length S klass using S in
    ifb ncl <= 0 then
      let%success vec_attr := ATTRIB S vec using S in
      let%success sa := stripAttrib S R_ClassSymbol vec_attr using S in
      run%success SET_ATTRIB S vec sa using S in
      run%success SET_OBJECT S vec false using S in
      result_success S (R_NilValue : SEXP)
    else
      ifb vec = R_NilValue then
        result_error S "Attempt to set an attribute on NULL."
      else
        do%break isfactor := false
        for i from 0 to ncl - 1 do
          let%success klass_i := STRING_ELT S klass i using S in
          let%success klass_i_str := CHAR S klass_i using S in
          ifb klass_i_str = "factor"%string then
            result_rreturn S true
          else result_rsuccess S isfactor using S in
        let%success vec_type := TYPEOF S vec using S in
        ifb isfactor /\ vec_type <> IntSxp then
          result_error S "Adding class ‘factor’ to an invalid object."
        else
          run%success installAttrib S vec R_ClassSymbol klass using S in
          run%success SET_OBJECT S vec true using S in
          result_success S (R_NilValue : SEXP)
  else
    result_error S "Attempt to set invalid ‘class’ attribute.".

Definition namesgets S (vec val : SEXP) :=
  add%stack "namesgets" in
  let%success val :=
    if%success isList S val using S then
      let%success val_vec := isVectorizable S val using S in
      if negb val_vec then
        result_error S "Incompatible ‘names’ argument."
      else
        let%success vec_len := R_length S vec using S in
        let%success rval := allocVector S StrSxp vec_len using S in
        do%success (i, tval) := (0, val)
        whileb i < vec_len /\ rval <> R_NilValue do
          read%list tval_car, tval_cdr, _ := tval using S in
          let%success s := coerceVector S tval_car StrSxp using S in
          let%success s_0 := STRING_ELT S s 0 using S in
          run%success SET_STRING_ELT S rval i s_0 using S in
          result_success S (1 + i, tval_cdr) using S, runs in
        result_success S rval
    else coerceVector S val StrSxp using S in
  let%success val_len := xlength S val using S in
  let%success vec_len := xlength S vec using S in
  let%success val :=
    ifb val_len < vec_len then
      unimplemented_function "xlengthgets"
    else result_success S val using S in
  run%success checkNames S vec val using S in
  if%success isOneDimensionalArray S vec using S then
    let (S, val) := CONS S val R_NilValue in
    run%success runs_setAttrib runs S vec R_DimNamesSymbol val using S in
    result_success S vec
  else
    run%success
      let%success vec_list := isList S vec using S in
      let%success vec_lang := isLanguage S vec using S in
      ifb vec_list \/ vec_lang then
        fold%success i := 0
        along vec
        as s, _, _ do
          run%success
            let%success val_i := STRING_ELT S val i using S in
            let%success val_i_char := CHAR S val_i using S in
            ifb val_i <> R_NilValue /\ val_i <> R_NaString /\ String.length val_i_char > 0 then
              let%success ins := installTrChar S val_i using S in
              set%tag s := ins using S in
              result_skip S
            else
              set%tag s := R_NilValue using S in
              result_skip S using S in
          result_success S (1 + i) using S, runs, globals in
        result_skip S
      else
        let%success vec_vec := isVector S vec using S in
        let%success vec_S4 := IS_S4_OBJECT S vec using S in
        ifb vec_vec \/ vec_S4 then
          run%success installAttrib S vec R_NamesSymbol val using S in
          result_skip S
        else result_error S "Invalid type to set ‘names’ attribute." using S in
    result_success S vec.

Definition dimgets S (vec val : SEXP) :=
  add%stack "dimgets" in
  let%success vec_vec := isVector S vec using S in
  let%success vec_list := isList S vec using S in
  ifb ~ vec_vec /\ ~ vec_list then
    result_error S "Invalid first argument."
  else
    let%success val_vec := isVector S val using S in
    let%success val_list := isList S val using S in
    ifb ~ val_vec /\ ~ val_list then
      result_error S "Invalid second argument."
    else
      let%success val := coerceVector S val IntSxp using S in
      let%success len := xlength S vec using S in
      let%success ndim := R_length S val using S in
      ifb ndim = 0 then
        result_error S "Length-0 dimension vector is invalid."
      else
        do%success total := 1 : int
        for i from 0 to ndim - 1 do
          read%Integer val_i := val at i using S in
          ifb val_i = NA_INTEGER then
            result_error S "The dims contain missing values."
          else ifb val_i < 0 then
            result_error S "The dims contain negative values."
          else result_success S (total * val_i)%Z using S in
        ifb total <> len then
          result_error S "dims do not match the length of the object."
        else
          run%success removeAttrib S vec R_DimNamesSymbol using S in
          run%success installAttrib S vec R_DimSymbol val using S in
          run%success MARK_NOT_MUTABLE S val using S in
          result_success S vec.

Definition setAttrib S (vec name val : SEXP) :=
  add%stack "setAttrib" in
  let%success name :=
    if%success isString S name using S then
      let%success str := STRING_ELT S name 0 using S in
      installTrChar S str
    else result_success S name using S in
  ifb val = R_NilValue then
    removeAttrib S vec name
  else
    ifb vec = R_NilValue then
      result_error S "Attempt to set an attribute on NULL."
    else
      let%success val :=
        if%success MAYBE_REFERENCED S val using S then
          R_FixupRHS S vec val
        else result_success S val using S in
      ifb name = R_NamesSymbol then
        namesgets S vec val
      else ifb name = R_DimSymbol then
        dimgets S vec val
      else ifb name = R_DimNamesSymbol then
        unimplemented_function "dimnamesgets"
      else ifb name = R_ClassSymbol then
        classgets S vec val
      else ifb name = R_TspSymbol then
        unimplemented_function "tspgets"
      else ifb name = R_CommentSymbol then
        unimplemented_function "commentgets"
      else ifb name = R_RowNamesSymbol then
        unimplemented_function "row_names_gets"
      else installAttrib S vec name val.


(** ** objects.c **)

(** The function names of this section corresponds to the function names
  in the file main/objects.c. **)

Definition R_has_methods S (op : SEXP) :=
  add%stack "R_has_methods" in
  (** This definition is oversimplified.  The final value of the
    original function depends on the value of the global variable
    [R_standardGeneric].  The way this variable is initialised is not
    simple.  It is updated in [R_initMethodDispatch] from
    library/methods/src/methods_list_dispatch.c. **)
  result_success S false.

Definition isS4 S s :=
  add%stack "isS4" in
  IS_S4_OBJECT S s.

Definition asS4 S s (flag : bool) (complete : int) :=
  add%stack "asS4" in
  let%success s_s4 := IS_S4_OBJECT S s using S in
  ifb flag = s_s4 then
    result_success S s
  else
    let%success s :=
      if%success MAYBE_SHARED S s using S then
        shallow_duplicate S s
      else result_success S s using S in
    run%exit
      if flag then
        run%success SET_S4_OBJECT S s using S in
        result_rskip S
      else
        run%return
          ifb complete <> 0 then
            unimplemented_function "R_getS4DataSlot"
          else result_rskip S using S in
        run%success UNSET_S4_OBJECT S s using S in
        result_rskip S using S in
    result_success S s.


(** ** objects.c **)

(** The function names of this section corresponds to the function names
  in the file main/objects.c. **)

Definition R_possible_dispatch (S : state) (call op args rho : SEXP) (promisedArgs : bool) : result SEXP :=
  unimplemented_function "R_possible_dispatch".


(** ** eval.c **)

(** The function names of this section corresponds to the function names
  in the file main/eval.c. **)

Definition COPY_TAG S vto vfrom :=
  add%stack "COPY_TAG" in
  read%list _, _, vfrom_tag := vfrom using S in
  ifb vfrom_tag <> R_NilValue then
    set%tag vto := vfrom_tag using S in
    result_skip S
  else result_skip S.

Definition mkRHSPROMISE S expr rhs :=
  add%stack "mkRHSPROMISE" in
  R_mkEVPROMISE_NR S expr rhs.

Definition asLogicalNoNA S (s call : SEXP) :=
  add%stack "asLogicalNoNA" in
  let%exit cond :=
    if%success IS_SCALAR S s LglSxp using S then
      let%success cond := SCALAR_LVAL S s using S in
      ifb cond <> NA_LOGICAL then
        result_rreturn S cond
      else result_rsuccess S cond
    else
      if%success IS_SCALAR S s IntSxp using S then
        let%success val := SCALAR_IVAL S s using S in
        ifb val <> NA_INTEGER then
          ifb val <> 0 then
            result_rreturn S (1 : int)
          else result_rreturn S (0 : int)
        else result_rsuccess S NA_LOGICAL
      else result_rsuccess S NA_LOGICAL using S in
  let%success len := R_length S s using S in
  ifb len > 1 then
    result_error S "The condition has length > 1."
  else
    let%success cond :=
      ifb len > 0 then
        let%success s_type := TYPEOF S s using S in
        match s_type with
        | LglSxp =>
          read%Logical cond := s at 0 using S in
          result_success S cond
        | IntSxp =>
          read%Integer cond := s at 0 using S in
          result_success S cond
        | _ =>
          asLogical S s
        end
      else result_success S cond using S in
    ifb cond = NA_LOGICAL then
      ifb len = 0 then
        result_error S "Argument is of length zero."
      else
        if%success isLogical S s using S then
          result_error S "Missing value where TRUE/FALSE needed."
        else result_error S "Argument is not interpretable as logical."
    else result_success S cond.

Definition replaceCall S vfun val args rhs :=
  add%stack "replaceCall" in
  let%success args_len := R_length S args using S in
  let (S, tmp) := allocList S (3 + args_len) in
  let ptmp := tmp in
  set%car ptmp := vfun using S in
  read%list _, ptmp_cdr, _ := ptmp using S in
  let ptmp := ptmp_cdr in
  set%car ptmp := val using S in
  read%list _, ptmp_cdr, _ := ptmp using S in
  let ptmp := ptmp_cdr in
  fold%success ptmp := ptmp
  along args
  as args_car, args_tag do
    set%car ptmp := args_car using S in
    set%tag ptmp := args_tag using S in
    read%list _, ptmp_cdr, _ := ptmp using S in
    result_success S ptmp_cdr using S, runs, globals in
  set%car ptmp := rhs using S in
  set%tag ptmp := R_valueSym using S in
  map%pointer tmp with set_type LangSxp using S in
  result_success S tmp.

Definition assignCall S op symbol vfun val args rhs :=
  add%stack "assignCall" in
  let%success val := replaceCall S vfun val args rhs using S in
  lang3 S op symbol val.

Definition forcePromise S (e : SEXP) : result SEXP :=
  add%stack "forcePromise" in
  read%prom _, e_prom := e using S in
  ifb prom_value e_prom = R_UnboundValue then
    run%success
      let%success e_prseen := PRSEEN S e using S in
      ifb e_prseen <> 0 then
        ifb e_prseen = 1 then
          result_error S "Promise already under evaluation."
        else
          (** The C code emitted a warning here: restarting interrupted promise evaluation.
            This may be a sign that this part should be ignored. *)
          SET_PRSEEN S e 1 ltac:(nbits_ok)
      else result_skip S using S in
    run%success SET_PRSEEN S e 1 ltac:(nbits_ok) using S in
    let%success val := runs_eval runs S (prom_expr e_prom) (prom_env e_prom) using S in
    run%success SET_PRSEEN S e 0 ltac:(nbits_ok) using S in
    map%pointer val with set_named_plural using S in
    read%prom e_, e_prom := e using S in
    let e_prom := {|
        prom_value := val ;
        prom_expr := prom_expr e_prom ;
        prom_env := R_NilValue
      |} in
    let e_ := {|
        NonVector_SExpRec_header := e_ ;
        NonVector_SExpRec_data := e_prom
      |} in
    write%defined e := e_ using S in
    result_success S val
  else result_success S (prom_value e_prom).

Definition R_execClosure S (call newrho sysparent rho arglist op : SEXP)
    : result SEXP :=
  add%stack "R_execClosure" in
  let%success cntxt :=
    begincontext S Ctxt_Return call newrho sysparent arglist op using S in
  read%clo op_, op_clo := op using S in
  let body := clo_body op_clo in
  (** JIT functions have been ignored here. **)
  let%success R_srcef := getAttrib S op R_SrcrefSymbol using S in
  set%longjump context_cjmpbuf cntxt as jmp using S, runs in
  let%success cntxt_returnValue :=
    ifb jmp <> empty_context_type then
      ifb context_jumptarget cntxt = None then
        ifb R_ReturnedValue S = R_RestartToken then
          let cntxt := context_with_callflag cntxt Ctxt_Return in
          let S := state_with_context S cntxt in
          let S := update_R_ReturnedValue S R_NilValue in
          runs_eval runs S body newrho
        else result_success S (R_ReturnedValue S)
      else result_success S NULL
    else runs_eval runs S body newrho using S in
  let cntxt := context_with_returnValue cntxt cntxt_returnValue in
  let S := state_with_context S cntxt in
  run%success endcontext S cntxt using S in
  result_success S (context_returnValue cntxt).

Definition applyClosure S (call op arglist rho suppliedvars : SEXP)
    : result SEXP :=
  add%stack "applyClosure" in
  let%success rho_type := TYPEOF S rho using S in
  ifb rho_type <> EnvSxp then
    result_error S "‘rho’ must be an environment."
  else
    read%clo op_, op_clo := op using S in
    let formals := clo_formals op_clo in
    let savedrho := clo_env op_clo in
    let%success actuals := matchArgs S formals arglist call using S in
    let%success newrho := NewEnvironment S formals actuals savedrho using S in
    fold%success a := actuals
    along formals
    as f_car, f_tag do
      read%list a_car, a_cdr, _ := a using S in
      ifb a_car = R_MissingArg /\ f_car <> R_MissingArg then
        let%success newprom := mkPromise S f_car newrho using S in
        set%car a := newprom using S in
        run%success SET_MISSING S a 2 ltac:(nbits_ok) using S in
        result_success S a_cdr
      else result_success S a_cdr using S, runs, globals in
    run%success
      ifb suppliedvars <> R_NilValue then
         addMissingVarsToNewEnv S newrho suppliedvars
       else result_skip S using S in
    if%success R_envHasNoSpecialSymbols S newrho using S then
      run%success SET_SPECIAL_SYMBOL S newrho false using S in
      result_skip S in
    R_execClosure S call newrho
      (ifb context_callflag (R_GlobalContext S) = Ctxt_Generic then
         context_sysparent (R_GlobalContext S)
       else rho)
      rho arglist op.

Definition promiseArgs S (el rho : SEXP) : result SEXP :=
  add%stack "promiseArgs" in
  let (S, tail) := CONS S R_NilValue R_NilValue in
  fold%success (ans, tail) := (tail, tail)
  along el
  as el_car, el_tag do
    ifb el_car = R_DotsSymbol then
      let%success h := findVar S el_car rho using S in
      let%success h_type := TYPEOF S h using S in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%success tail := tail
        along h
        as h_car, h_tag do
          let%success h_car_type := TYPEOF S h_car using S in
          run%success
            ifb h_car_type = PromSxp \/ h_car = R_MissingArg then
              let (S, l) := CONS S h_car R_NilValue in
              set%cdr tail := l using S in
              result_skip S
            else
              let%success prom :=
                mkPromise S h_car rho using S in
              let (S, l) := CONS S prom R_NilValue in
              set%cdr tail := l using S in
              result_skip S using S in
          read%list _, tail_cdr, _ := tail using S in
          let tail := tail_cdr in
          run%success
            ifb h_tag <> R_NilValue then
              set%tag tail := h_tag using S in
              result_skip S
            else result_skip S using S in
          result_success S tail
        using S, runs, globals in
        result_success S (ans, tail)
      else ifb h <> R_MissingArg then
        result_error S "‘...’ used in an incorrect context."
      else result_success S (ans, tail)
    else ifb el_car = R_MissingArg then
      let (S, l) := CONS S R_MissingArg R_NilValue in
      set%cdr tail := l using S in
      read%list _, tail_cdr, _ := tail using S in
      let tail := tail_cdr in
      set%tag tail := el_tag using S in
      result_success S (ans, tail)
    else
      let%success prom :=
        mkPromise S el_car rho using S in
      let (S, l) := CONS S prom R_NilValue in
      set%cdr tail := l using S in
      read%list _, tail_cdr, _ := tail using S in
      let tail := tail_cdr in
      set%tag tail := el_tag using S in
      result_success S (ans, tail)
  using S, runs, globals in
  read%list _, ans_cdr, _ := ans using S in
  result_success S ans_cdr.

Definition PRIMFUN S x :=
  add%stack "PRIMFUN" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (fun_cfun x_fun).

Definition PRIMVAL S x :=
  add%stack "PRIMVAL" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (fun_code x_fun).

Definition PPINFO S x :=
  add%stack "PPINFO" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (fun_gram x_fun).

Definition PRIMARITY S x :=
  add%stack "PRIMARITY" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (fun_arity x_fun).

Definition PRIMINTERNAL S x :=
  add%stack "PRIMINTERNAL" in
  read%prim _, x_prim := x using S in
  let%success x_fun := read_R_FunTab S (prim_offset x_prim) using S in
  result_success S (funtab_eval_arg_internal (fun_eval x_fun)).

Definition evalList S (el rho call : SEXP) n :=
  add%stack "evalList" in
  fold%success (n, head, tail) := (n, R_NilValue : SEXP, R_NilValue : SEXP)
  along el
  as el_car, el_tag
    do
    let n := 1 + n in
    ifb el_car = R_DotsSymbol then
      let%success h := findVar S el_car rho using S in
      let%success h_type := TYPEOF S h using S in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%success tail := tail
        along h
        as h_car, h_tag
        do
          let%success tmp_ev := runs_eval runs S h_car rho using S in
          let (S, ev) := CONS_NR S tmp_ev R_NilValue in
          let%success head :=
            ifb head = R_NilValue then
              result_success S ev
            else
              set%cdr tail := ev using S in
              result_success S head using S in
          run%success
            ifb h_tag <> R_NilValue then
              set%tag ev := h_tag using S in
              result_skip S
            else result_skip S using S in
          result_success S ev
        using S, runs, globals in
        result_success S (n, head, tail)
      else ifb h <> R_MissingArg then
        result_error S "‘...’ used in an incorrect context."
      else result_success S (n, head, tail)
    else ifb el_car = R_MissingArg then
      result_error S "Argument is empty."
    else
      let%success ev := runs_eval runs S el_car rho using S in
      let (S, ev) := CONS_NR S ev R_NilValue in
      let%success head :=
        ifb head = R_NilValue then
          result_success S ev
        else
          set%cdr tail := ev using S in
          result_success S head using S in
      run%success
        ifb el_tag <> R_NilValue then
          set%tag ev := el_tag using S in
          result_skip S
        else result_skip S using S in
      result_success S (n, head, ev)
  using S, runs, globals in
  result_success S head.

Definition evalListKeepMissing (S : state) (el rho : SEXP) : result SEXP :=
  add%stack "evalListKeepMissing" in
  fold%success (head, tail) := (R_NilValue : SEXP, R_NilValue : SEXP)
  along el
  as _, _, el_list do
    let el_car := list_carval el_list in
    let el_cdr := list_cdrval el_list in
    ifb el_car = R_DotsSymbol then
      let%success h := findVar S el_car rho using S in
      let%success h_type := TYPEOF S h using S in
      ifb h_type = DotSxp \/ h = R_NilValue then
        fold%let (head, tail) := (head, tail)
        along h
        as _, _, h_list do
          let h_car := list_carval h_list in
          let%success val :=
            ifb h_car = R_MissingArg then
              result_success S (R_MissingArg : SEXP)
            else runs_eval runs S h_car rho using S in
          run%success INCREMENT_LINKS S val using S in
          let (S, ev) := CONS_NR S val R_NilValue in
          let%success head :=
            ifb head = R_NilValue then
              result_success S ev
            else
              set%cdr tail := ev using S in
              result_success S head using S in
          run%success COPY_TAG S ev h using S in
          result_success S (head, ev) using S, runs, globals
      else ifb h <> R_MissingArg then
        result_error S "‘...’ used in an incorrect context."
      else result_success S (head, tail)
    else
      let%success val :=
        let%success el_car_sy := isSymbol S el_car using S in
        let%success el_car_mi := R_isMissing S el_car rho using S in
        ifb el_car = R_MissingArg \/ (el_car_sy /\ el_car_mi) then
          result_success S (R_MissingArg : SEXP)
        else runs_eval runs S el_car rho using S in
      run%success
        ifb el_cdr <> R_NilValue then
          INCREMENT_LINKS S val
        else result_skip S using S in
      let (S, ev) := CONS_NR S val R_NilValue in
      let%success head :=
        ifb head = R_NilValue then
          result_success S ev
        else
          set%cdr tail := ev using S in
          result_success S head using S in
      run%success COPY_TAG S ev el using S in
      result_success S (head, ev) using S, runs, globals in
  fold%success
  along head
  as _, _, head_list do
    let el_cdr := list_cdrval head_list in
    let el_car := list_carval head_list in
    ifb el_cdr <> R_NilValue then
      DECREMENT_LINKS S el_car
    else result_skip S using S, runs, globals in
  result_success S head.

Definition evalArgs S el rho (dropmissing : bool) call n :=
  add%stack "evalArgs" in
  if dropmissing then
    evalList S el rho call n
  else evalListKeepMissing S el rho.

(** The original function [DispatchGroup] returns a boolean and, if this boolean is true,
  overwrites its additional argument [ans]. This naturally translates as an option type. **)
Definition DispatchGroup S group (call op args rho : SEXP)
    : result (option SEXP) :=
  add%stack "DispatchGroup" in
  read%list args_car, args_cdr, _ := args using S in
  let%success args_car_is := isObject S args_car using S in
  read%list args_cdr_car, _, _ := args_cdr using S in
  let%success args_cdr_car_is := isObject S args_cdr_car using S in
  ifb args_car <> R_NilValue /\ ~ args_car_is /\ (args_cdr = R_NilValue \/ ~ args_cdr_car_is) then
    result_success S None
  else
    let isOps := decide (group = "Ops"%string) in
    let%success args_len := R_length S args using S in
    let%success args_car_S4 := IS_S4_OBJECT S args_car using S in
    let%success args_cdr_car_S4 := IS_S4_OBJECT S args_cdr_car using S in
    let useS4 :=
      ifb args_len = 1 /\ ~ args_car_S4 then false
      else ifb args_len = 2 /\ ~ args_car_S4 /\ ~ args_cdr_car_S4 then false
      else true in
    run%exit
      if useS4 then
        run%success
          if isOps then
            fold%let
            along args
            as s, _, _ do
              set%tag s := R_NilValue using S in
              result_skip S using S, runs, globals
          else result_skip S using S in
        let%success op_hm := R_has_methods S op using S in
        let%success value := R_possible_dispatch S call op args rho false using S in
        ifb op_hm /\ value <> NULL then
          result_rreturn S (Some value)
        else result_rskip S
      else result_rskip S using S in
    read%list call_car, _, _ := call using S in
    run%exit
      if%success isSymbol S call_car using S then
        let%success call_car_name := PRINTNAME S call_car using S in
        let%success call_car_str := CHAR S call_car_name using S in
        let cstr := String.index 0 "." call_car_str in
        match cstr with
        | None => result_rskip S
        | Some cstr =>
          let cstr_ := String.substring (1 + cstr) (String.length call_car_str - cstr - 1) call_car_str in
          ifb cstr_ = "default"%string then
            result_rreturn S None
          else result_rskip S
        end
      else result_rskip S using S in
    let%success nargs :=
      if isOps then
        R_length S args
      else result_success S 1 using S in
    read%list args_car, args_cdr, _ := args using S in
    run%exit
      let%success args_car_obj := isObject S args_car using S in
      ifb nargs = 1 /\ ~ args_car_obj then
        result_rreturn S None
      else result_rskip S using S in
    let%success generic := PRINTNAME S op using S in
    unimplemented_function "classForGroupDispatch".

Definition DispatchOrEval S (call op : SEXP) (generic : string) (args rho : SEXP)
    (dropmissing argsevald : bool) : result (bool * SEXP) :=
  add%stack "DispatchOrEval" in
  let%success (x, dots) :=
    if argsevald then
      read%list args_car, _, _ := args using S in
      result_success S (args_car, false)
    else
      fold%return (x, dots) := (R_NilValue : SEXP, false)
      along args as args_car, _ do
        ifb args_car = R_DotsSymbol then
          let%success h := findVar S R_DotsSymbol rho using S in
          let%success h_type := TYPEOF S h using S in
          ifb h_type = DotSxp then
            read%list h_car, _, _ := h using S in
            let%success h_car_type := TYPEOF S h_car using S in
            ifb h_car_type <> PromSxp then
              result_error S "Value in ‘...’ is not a promise."
            else
              let%success r := runs_eval runs S h_car rho using S in
              result_rreturn S (r, true)
          else ifb h <> R_NilValue /\ h <> R_MissingArg then
            result_error S "‘...’ used in an incorrect context."
          else result_rsuccess S (x, dots)
        else
          let%success r := runs_eval runs S args_car rho using S in
          result_rreturn S (r, false) using S, runs, globals in
      result_success S (x, dots) using S in
  run%exit
    if%success isObject S x using S then
      result_not_implemented "Object case."
    else result_rskip S using S in
  let%success ans :=
    if negb argsevald then
      if dots then
        evalArgs S args rho dropmissing call 0
      else
        read%list _, args_cdr, args_tag := args using S in
        let%success r := evalArgs S args_cdr rho dropmissing call 1 using S in
        let (S, ans) := CONS_NR S x r in
        let%success t := CreateTag S args_tag using S in
        set%tag ans := t using S in
        result_success S ans
    else result_success S args using S in
  result_success S (false, ans).

Definition DispatchAnyOrEval S (call op : SEXP) (generic : string) (args rho : SEXP)
    (dropmissing argsevald : bool) : result (bool * SEXP) :=
  add%stack "DispatchAnyOrEval" in
  if%success R_has_methods S op using S then
    result_not_implemented "Method case."
  else DispatchOrEval S call op generic args rho dropmissing argsevald.

Definition eval S (e rho : SEXP) :=
  add%stack "eval" in
  let%success e_type := TYPEOF S e using S in
  match e_type with
  | NilSxp
  | ListSxp
  | LglSxp
  | IntSxp
  | RealSxp
  | StrSxp
  | CplxSxp
  | RawSxp
  | S4Sxp
  | SpecialSxp
  | BuiltinSxp
  | EnvSxp
  | CloSxp
  | VecSxp
  | ExtptrSxp
  | WeakrefSxp
  | ExprSxp =>
    map%pointer e with set_named_plural using S in
    result_success S e
  | _ =>
    let%success rho_type := TYPEOF S rho using S in
    ifb rho_type <> EnvSxp then
      result_error S "‘rho’ must be an environment."
    else
      match e_type with
      | BcodeSxp =>
        unimplemented_function "bcEval"
      | SymSxp =>
        ifb e = R_DotsSymbol then
          result_error S "‘...’ used in an incorrect context."
        else
          let%success tmp :=
            if%success DDVAL S e using S then
              ddfindVar S e rho
            else
              findVar S e rho using S in
          ifb tmp = R_UnboundValue then
            result_error S "Object not found."
          else
            let%success ddval := DDVAL S e using S in
            ifb tmp = R_MissingArg /\ ~ ddval then
              result_error S "Argument is missing, with no default."
            else
              let%success tmp_type := TYPEOF S tmp using S in
              ifb tmp_type = PromSxp then
                read%prom _, tmp_prom := tmp using S in
                let%success tmp :=
                  ifb prom_value tmp_prom = R_UnboundValue then
                    forcePromise S tmp
                  else result_success S (prom_value tmp_prom) using S in
                map%pointer tmp with set_named_plural using S in
                result_success S tmp
              else
                let%success tmp_type := TYPEOF S tmp using S in
                let%success tmp_named := NAMED S tmp using S in
                run%success
                  ifb tmp_type <> NilSxp /\ tmp_named = named_temporary then
                    map%pointer tmp with set_named_unique using S in
                    result_skip S
                  else result_skip S using S in
                result_success S tmp
      | PromSxp =>
        run%success
          read%prom _, e_prom := e using S in
          ifb prom_value e_prom = R_UnboundValue then
            run%success forcePromise S e using S in
            result_skip S
          else result_skip S using S in
        read%prom _, e_prom := e using S in
        result_success S (prom_value e_prom)
      | LangSxp =>
        read%list e_car, e_cdr, _ := e using S in
        let%success e_car_type := TYPEOF S e_car using S in
        let%success op :=
          ifb e_car_type = SymSxp then
            let%success ecall :=
              ifb context_callflag (R_GlobalContext S) = Ctxt_CCode then
                result_success S (context_call (R_GlobalContext S))
              else result_success S e using S in
            findFun3 S e_car rho ecall
          else runs_eval runs S e_car rho using S in
        let%success op_type := TYPEOF S op using S in
        match op_type with
        | SpecialSxp =>
          let%success f := PRIMFUN S op using S in
          f S e op e_cdr rho
        | BuiltinSxp =>
          let%success tmp := evalList S e_cdr rho e 0 using S in
          let%success infos := PPINFO S op using S in
          ifb PPinfo_kind infos = PP_FOREIGN then
            let%success cntxt :=
              begincontext S Ctxt_Builtin e R_BaseEnv R_BaseEnv R_NilValue R_NilValue using S in
            let%success f := PRIMFUN S op using S in
            let%success tmp := f S e op tmp rho using S in
            run%success endcontext S cntxt using S in
            result_success S tmp
          else
            let%success f := PRIMFUN S op using S in
            f S e op tmp rho
        | CloSxp =>
          let%success tmp := promiseArgs S e_cdr rho using S in
          applyClosure S e op tmp rho R_NilValue
        | _ => result_error S "Attempt to apply non-function."
        end
      | DotSxp => result_error S "‘...’ used in an incorrect context"
      | _ => result_error S "Type unimplemented in the R source code."
      end
  end.

Definition evalseq S expr rho (forcelocal : bool) tmploc :=
  add%stack "evalseq" in
  if%success isNull S expr using S then
    result_error S "Invalid left side assignment."
  else if%success isSymbol S expr using S then
    let%success nval :=
      if forcelocal then
        EnsureLocal S expr rho
      else
        read%env _, rho_env := rho using S in
        eval S expr (env_enclos rho_env) using S in
    let%success nval :=
      if%success MAYBE_SHARED S nval using S then
        shallow_duplicate S nval
      else result_success S nval using S in
    let (S, r) := CONS_NR S nval expr in
    result_success S r
  else if%success isLanguage S expr using S then
    read%list expr_car, expr_cdr, _ := expr using S in
    read%list expr_cdr_car, expr_cdr_cdr, _ := expr_cdr using S in
    let%success val := runs_evalseq runs S expr_cdr_car rho forcelocal tmploc using S in
    read%list val_car, _, _ := val using S in
    run%success R_SetVarLocValue S tmploc val_car using S in
    let%success tmploc_sym := R_GetVarLocSymbol S tmploc using S in
    let%success nexpr := LCONS S tmploc_sym expr_cdr_cdr using S in
    let%success nexpr := LCONS S expr_car nexpr using S in
    let%success nval := eval S nexpr rho using S in
    let%success nval :=
      if%success MAYBE_REFERENCED S nval using S then
        if%success MAYBE_SHARED S nval using S then
          shallow_duplicate S nval
        else
          read%list nval_car, _, _ := nval using S in
          if%success MAYBE_SHARED S nval_car using S then
            shallow_duplicate S nval
          else result_success S nval
      else result_success S nval using S in
    let (S, r) := CONS_NR S nval val in
    result_success S r
  else result_error S "Target of assignment expands to non-language object.".

(** Evaluates the expression in the global environment. **)
Definition eval_global S e :=
  add%stack "eval_global" in
  eval S e R_GlobalEnv.

End Parameterised.

Arguments SET_MISSING : clear implicits.
Arguments SET_PRSEEN : clear implicits.

