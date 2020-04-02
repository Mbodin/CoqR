(** Core.CRinternals.
  The function names in this file correspond to the macro names
  in the file include/Rinternals.h. **)

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
Require Import Loops.


Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition TYPEOF x :=
  add%stack "TYPEOF" in
  read%defined x_ := x in
  result_success (type x_).

Definition ALTREP x :=
  add%stack "ALTREP" in
  read%defined x_ := x in
  result_success (alt x_).

Definition OBJECT x :=
  add%stack "OBJECT" in
  read%defined x_ := x in
  result_success (obj x_).

Definition SET_OBJECT x v :=
  add%stack "SET_OBJECT" in
  map%pointer%contextual x with set_obj v in
  result_skip.

Definition PRINTNAME x :=
  add%stack "PRINTNAME" in
  read%sym _, x_sym := x in
  result_success (sym_pname x_sym).

Definition CHAR x :=
  add%stack "CHAR" in
  read%VectorChar x_vector := x in
  result_success (list_to_string (ArrayList.to_list x_vector)).

Definition MISSING x :=
  add%stack "MISSING" in
  read%defined x_ := x in
  result_success (nbits_to_nat (sub_nbits 0 4 (gp x_) ltac:(nbits_ok))).

Definition SET_MISSING e (m : nat) I :=
  add%stack "SET_MISSING" in
  map%gp e with @write_nbits 16 4 0 (nat_to_nbits m I) ltac:(nbits_ok) in
  result_skip.
Arguments SET_MISSING : clear implicits.

Definition ATTRIB x :=
  add%stack "ATTRIB" in
  read%defined x_ := x in
  result_success (attrib x_).

(** We suppose that [COMPUTE_REFCNT_VALUES] is not defined. **)

Definition REFCNT (x : SEXP) :=
  add%stack "REFCNT" in
  result_success 0.

Definition TRACKREFS (x : SEXP) :=
  add%stack "TRACKREFS" in
  result_success false.

Definition SET_REFCNT (x : SEXP) (v : bool) :=
  add%stack "SET_REFCNT" in
  result_skip.

Definition SET_TRACKREFS (x : SEXP) (v : bool) :=
  add%stack "SET_TRACKREFS" in
  result_skip.

Definition DECREMENT_REFCNT (x : SEXP) :=
  add%stack "DECREMENT_REFCNT" in
  result_skip.

Definition INCREMENT_REFCNT (x : SEXP) :=
  add%stack "INCREMENT_REFCNT" in
  result_skip.

Definition ENABLE_REFCNT x :=
  add%stack "ENABLE_REFCNT" in
  SET_TRACKREFS x true.

Definition DISABLE_REFCNT x :=
  add%stack "DISABLE_REFCNT" in
  SET_TRACKREFS x false.

Definition NAMED x :=
  add%stack "NAMED" in
  read%defined x_ := x in
  result_success (named x_).

Definition INCREMENT_NAMED x :=
  add%stack "INCREMENT_NAMED" in
  let%success x_named := NAMED x in
  match x_named with
  | named_temporary =>
    set%named x := named_unique in
    result_skip
  | named_unique =>
    set%named x := named_plural in
    result_skip
  | named_plural =>
    result_skip
  end.

Definition INCREMENT_LINKS x :=
  add%stack "INCREMENT_LINKS" in
  INCREMENT_NAMED x.

Definition DECREMENT_NAMED x :=
  add%stack "DECREMENT_NAMED" in
  let%success x_named := NAMED x in
  match x_named with
  | named_temporary =>
    result_skip
  | named_unique =>
    set%named x := named_temporary in
    result_skip
  | named_plural =>
    set%named x := named_unique in
    result_skip
  end.

Definition DECREMENT_LINKS x :=
  add%stack "DECREMENT_LINKS" in
  DECREMENT_NAMED x.

Definition NO_REFERENCES x :=
  add%stack "NO_REFERENCES" in
  let%success x_named := NAMED x in
  result_success (decide (x_named = named_temporary)).

Definition MAYBE_REFERENCED x :=
  add%stack "MAYBE_REFERENCED" in
  let%success r := NO_REFERENCES x in
  result_success (negb r).

Definition MAYBE_SHARED x :=
  add%stack "MAYBE_SHARED" in
  let%success x_named := NAMED x in
  result_success (decide (x_named = named_plural)).

Definition MARK_NOT_MUTABLE x :=
  add%stack "MARK_NOT_MUTABLE" in
  set%named x := named_plural in
  result_skip.

Definition ENSURE_NAMED x :=
  add%stack "ENSURE_NAMED" in
  let%success x_named := NAMED x in
  match x_named with
  | named_temporary =>
    set%named x := named_unique in
    result_skip
  | _ => result_skip
  end.

Definition SETTER_CLEAR_NAMED x :=
  add%stack "SETTER_CLEAR_NAMED" in
  let%success x_named := NAMED x in
  ifb x_named = named_unique then
    set%named x := named_temporary in
    result_skip
  else result_skip.

Definition RAISE_NAMED x n :=
  add%stack "RAISE_NAMED" in
  let%success x_named := NAMED x in
  ifb x_named < n then
    set%named x := n in
    result_skip
  else result_skip.


Definition DDVAL_BIT := 0.

Definition DDVAL x :=
  add%stack "DDVAL" in
  read%defined x_ := x in
  result_success (nth_bit DDVAL_BIT (gp x_) ltac:(nbits_ok)).

Definition SET_DDVAL_BIT x :=
  add%stack "SET_DDVAL_BIT" in
  map%gp x with @write_nbit 16 DDVAL_BIT ltac:(nbits_ok) true in
  result_skip.

Definition UNSET_DDVAL_BIT x :=
  add%stack "UNSET_DDVAL_BIT" in
  map%gp x with @write_nbit 16 DDVAL_BIT ltac:(nbits_ok) false in
  result_skip.

Definition SET_DDVAL x v :=
  add%stack "SET_DDVAL" in
  map%gp x with @write_nbit 16 DDVAL_BIT ltac:(nbits_ok) v in
  result_skip.

Definition S4_OBJECT_BIT := 4.

Definition IS_S4_OBJECT x :=
  add%stack "IS_S4_OBJECT" in
  read%defined x_ := x in
  result_success (nth_bit S4_OBJECT_BIT (gp x_) ltac:(nbits_ok)).

Definition SET_S4_OBJECT x :=
  add%stack "SET_S4_OBJECT" in
  map%gp x with @write_nbit 16 S4_OBJECT_BIT ltac:(nbits_ok) true in
  result_skip.

Definition UNSET_S4_OBJECT x :=
  add%stack "UNSET_S4_OBJECT" in
  map%gp x with @write_nbit 16 S4_OBJECT_BIT ltac:(nbits_ok) false in
  result_skip.

Definition GROWABLE_BIT := 5.

Definition IS_GROWABLE x :=
  add%stack "IS_GROWABLE" in
  read%defined x_ := x in
  result_success (nth_bit GROWABLE_BIT (gp x_) ltac:(nbits_ok)).

Definition IS_SCALAR x t :=
  add%stack "IS_SCALAR" in
  read%defined x_ := x in
  result_success (decide (type x_ = t /\ scalar x_)).

Definition IS_SIMPLE_SCALAR x t :=
  add%stack "IS_SIMPLE_SCALAR" in
  let%success x_scal := IS_SCALAR x t in
  read%defined x_ := x in
  (x_scal '&& (attrib x_ '== R_NilValue) : result_bool).

Definition isLogical s :=
  add%stack "isLogical" in
  let%success s_type := TYPEOF s in
  result_success (decide (s_type = LglSxp)).

Definition IS_LOGICAL := isLogical.

Definition isSymbol s :=
  add%stack "isSymbol" in
  let%success s_type := TYPEOF s in
  result_success (decide (s_type = SymSxp)).

Definition isString s :=
  add%stack "isString" in
  let%success s_type := TYPEOF s in
  result_success (decide (s_type = StrSxp)).

Definition isReal s :=
  add%stack "isReal" in
  let%success s_type := TYPEOF s in
  result_success (decide (s_type = RealSxp)).

Definition isNull s :=
  add%stack "isNull" in
  let%success s_type := TYPEOF s in
  result_success (decide (s_type = NilSxp)).

Definition isExpression s :=
  add%stack "isExpression" in
  let%success s_type := TYPEOF s in
  result_success (decide (s_type = ExprSxp)).

Definition isComplex s :=
  add%stack "isComplex" in
  let%success s_type := TYPEOF s in
  result_success (decide (s_type = CplxSxp)).

Definition isObject s :=
  add%stack "isObject" in
  OBJECT s.

Definition isEnvironment s :=
  add%stack "isEnvironment" in
  let%success s_type := TYPEOF s in
  result_success (decide (s_type = EnvSxp)).

Definition isByteCode x :=
  add%stack "isByteCode" in
  let%success x_type := TYPEOF x in
  result_success (decide (x_type = BcodeSxp)).

Definition BCODE_CODE x :=
  add%stack "BCODE_CODE" in
  read%list x_car, _, _ := x in
  result_success x_car.

Definition BCODE_CONSTS x :=
  add%stack "BCODE_CONSTS" in
  read%list _, x_cdr, _ := x in
  result_success x_cdr.

Definition BCODE_EXPR x :=
  add%stack "BCODE_EXPR" in
  read%list _, _, x_tag := x in
  result_success x_tag.

Definition STDVEC_LENGTH x :=
  add%stack "STDVEC_LENGTH" in
  read%defined x_ := x in
  match x_ with
  | SExpRec_NonVector _ => result_impossible "Not a vector."
  | SExpRec_VectorChar x_ => result_success (VecSxp_length x_)
  | SExpRec_VectorInteger x_ => result_success (VecSxp_length x_)
  | SExpRec_VectorComplex x_ => result_success (VecSxp_length x_)
  | SExpRec_VectorReal x_ => result_success (VecSxp_length x_)
  | SExpRec_VectorPointer x_ => result_success (VecSxp_length x_)
  end.

Definition STDVEC_TRUELENGTH x :=
  add%stack "STDVEC_LENGTH" in
  read%defined x_ := x in
  match x_ with
  | SExpRec_NonVector _ => result_impossible "Not a vector."
  | SExpRec_VectorChar x_ => result_success (VecSxp_truelength x_)
  | SExpRec_VectorInteger x_ => result_success (VecSxp_truelength x_)
  | SExpRec_VectorComplex x_ => result_success (VecSxp_truelength x_)
  | SExpRec_VectorReal x_ => result_success (VecSxp_truelength x_)
  | SExpRec_VectorPointer x_ => result_success (VecSxp_truelength x_)
  end.

Definition SET_STDVEC_TRUELENGTH x v :=
  add%stack "SET_STDVEC_TRUELENGTH" in
  read%defined x_ := x in
  let%success x_ :=
    match x_ with
    | SExpRec_NonVector _ => result_impossible "Not a vector."
    | SExpRec_VectorChar x_ => result_success (SExpRec_VectorChar (Vector_SExpRec_with_truelength x_ v))
    | SExpRec_VectorInteger x_ => result_success (SExpRec_VectorInteger (Vector_SExpRec_with_truelength x_ v))
    | SExpRec_VectorComplex x_ => result_success (SExpRec_VectorComplex (Vector_SExpRec_with_truelength x_ v))
    | SExpRec_VectorReal x_ => result_success (SExpRec_VectorReal (Vector_SExpRec_with_truelength x_ v))
    | SExpRec_VectorPointer x_ => result_success (SExpRec_VectorPointer (Vector_SExpRec_with_truelength x_ v))
    end in
  write%defined x := x_ in
  result_skip.

Definition SET_TRUELENGTH x v :=
  add%stack "SET_TRUELENGTH" in
  if%success ALTREP x then
    result_error "Can’t set ALTREP truelength."
  else
    SET_STDVEC_TRUELENGTH x v.

End Parameterised.

Arguments SET_MISSING : clear implicits.

