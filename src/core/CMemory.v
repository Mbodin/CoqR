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
From Lib Require Import Double.
From CoqR Require Import Loops.
Require Import CRinternals.

Section Parameterised.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.


Definition CONS (car cdr : _SEXP) : result_SEXP :=
  let%alloc%contextual e := make_SExpRec_list R_NilValue car cdr R_NilValue in
  result_success e.

Definition CONS_NR := CONS.

Fixpoint allocList_aux n (p : _SEXP) : result_SEXP :=
  match n with
  | 0 => p
  | S n =>
    let%success p := allocList_aux n p in
    CONS R_NilValue p
  end.

Definition allocList (n : nat) : result_SEXP :=
  allocList_aux n R_NilValue.

Definition SET_ATTRIB (x v : _SEXP) :=
  add%stack "SET_ATTRIB" in
  let%success v_type := TYPEOF v in
  ifb v_type <> ListSxp /\ v_type <> NilSxp then
    result_error "The value must be a pairlist or NULL."
  else
    set%attrib x := v in
    result_skip.

Definition STRING_ELT (x : _SEXP) i : result_SEXP :=
  add%stack "STRING_ELT" in
  let%success x_type := TYPEOF x in
  ifb x_type <> StrSxp then
    result_error "Not a character vector."
  else
    read%Pointer r := x at i in
    result_success r.

Definition VECTOR_ELT x i : result_SEXP :=
  add%stack "VECTOR_ELT" in
  read%Pointer x_i := x at i in
  result_success x_i.

Definition SET_PRVALUE (x v : _SEXP) :=
  add%stack "SET_PRVALUE" in
  let%fetch v in
  read%prom x_, x_prom := x in
  let x_prom := {|
      prom_value := v ;
      prom_expr := prom_expr x_prom ;
      prom_env := prom_env x_prom
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_prom
    |} in
  write%defined x := x_ in
  result_skip.

Definition SET_PRCODE (x v : _SEXP) :=
  add%stack "SET_PRCODE" in
  let%fetch v in
  read%prom x_, x_prom := x in
  let x_prom := {|
      prom_value := prom_value x_prom ;
      prom_expr := v ;
      prom_env := prom_env x_prom
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_prom
    |} in
  write%defined x := x_ in
  result_skip.

Definition SET_SYMVALUE (x v : _SEXP) :=
  add%stack "SET_SYMVALUE" in
  let%fetch v in
  read%sym x_, x_sym := x in
  let x_sym := {|
      sym_pname := sym_pname x_sym ;
      sym_value := v ;
      sym_internal := sym_internal x_sym
    |} in
  let x_ := {|
      NonVector_SExpRec_header := x_ ;
      NonVector_SExpRec_data := x_sym
    |} in
  write%defined x := x_ in
  result_skip.

(** Note: there is a macro definition renaming [NewEnvironment] to
  [Rf_NewEnvironment] in the file include/Defn.h. As a consequence,
  the compiled C files references [Rf_NewEnvironment] and not
  [NewEnvironment]. These two functions are exactly the same.
  This is a relatively frequent scheme in R source code. **)
Definition NewEnvironment (namelist valuelist rho : _SEXP) : result_SEXP :=
  add%stack "NewEnvironment" in
  let%alloc%contextual newrho := make_SExpRec_env R_NilValue valuelist rho in
  do%success (v, n) := (valuelist, namelist)
  while (v '!= R_NilValue) '&& (n '!= R_NilValue) do
    read%list _, n_cdr, n_tag := n in
    set%tag v := n_tag in
    read%list _, v_cdr, _ := v in
    result_success (v_cdr, n_cdr) using runs in
  result_success newrho.

(** Similarly, there is a macro renaming [mkPROMISE] to [Rf_mkPROMISE]. **)
Definition mkPromise (expr rho : _SEXP) : result_SEXP :=
  add%stack "mkPromise" in
  set%named expr := named_plural in
  let%alloc%contextual s := make_SExpRec_prom R_NilValue R_UnboundValue expr rho in
  result_success s.

Definition R_mkEVPROMISE_NR expr val : result_SEXP :=
  add%stack "R_mkEVPROMISE_NR" in
  let%success prom := mkPromise expr R_NilValue in
  run%success SET_PRVALUE prom val in
  result_success prom.

(** The way this function has originally been defined is not
  implementable in Coq.  This is thus a loosy translation. **)
Definition allocFormalsList l : result_SEXP :=
  add%stack "allocFormalsList" in
  let%success res :=
    fold_left (fun _ (Sres : result_SEXP) =>
      let%success res := Sres in
      CONS R_NilValue res) R_NilValue l in
  do%success n := contextual_ret res
  for sym in%list l do
    set%tag n := sym in
    run%success MARK_NOT_MUTABLE n in
    read%list _, n_cdr, _ := n in
    result_success n_cdr in
  result_success res.

Definition allocFormalsList2 sym1 sym2 : result_SEXP :=
  add%stack "allocFormalsList2" in
  allocFormalsList [sym1; sym2].

Definition allocFormalsList3 sym1 sym2 sym3 : result_SEXP :=
  add%stack "allocFormalsList3" in
  allocFormalsList [sym1; sym2; sym3].

Definition allocFormalsList4 sym1 sym2 sym3 sym4 : result_SEXP :=
  add%stack "allocFormalsList4" in
  allocFormalsList [sym1; sym2; sym3; sym4].

Definition allocFormalsList5 sym1 sym2 sym3 sym4 sym5 : result_SEXP :=
  add%stack "allocFormalsList5" in
  allocFormalsList [sym1; sym2; sym3; sym4; sym5].

Definition allocFormalsList6 sym1 sym2 sym3 sym4 sym5 sym6 : result_SEXP :=
  add%stack "allocFormalsList6" in
  allocFormalsList [sym1; sym2; sym3; sym4; sym5; sym6].

End Parameterised.

