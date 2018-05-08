(** Core.CMemory.
  The function names in this file correspond to the function
  names in the file main/memory.c. **)

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

End Parameterised.

