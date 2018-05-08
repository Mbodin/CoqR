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
Require Import Ascii Double.
Require Import Loops.


Section Parameterised.

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

End Parameterised.

Arguments SET_MISSING : clear implicits.

