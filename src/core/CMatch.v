(** Core.CMatch.
  The function names in this file correspond to the function names
  in the file main/match.c. **)

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
Require Import CMemory.


Section Parameterised.

Variable globals : Globals.

Let read_globals := read_globals globals.
Local Coercion read_globals : GlobalVariable >-> SEXP.

Variable runs : runs_type.

Definition int_to_double := Double.int_to_double : int -> double.

Local Coercion int_to_double : Z >-> double.

Arguments SET_MISSING : clear implicits.


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
    let (S, a) := allocList globals S i in
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
        let (S, unused) := CONS globals S (list_carval b_list) R_NilValue in
        set%tag unused := list_tagval b_list using S in
        result_success S (unused, unused)
      else
        let (S, l) := CONS globals S (list_carval b_list) R_NilValue in
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
    let (S, actuals) := CONS_NR globals S R_MissingArg actuals in
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


Definition matchArgs_RC S formals supplied call :=
  add%stack "matchArgs_RC" in
  let%success args := matchArgs S formals supplied call using S in
  fold%success
  along args
  as a, _, a_list do
    let%success a_track := TRACKREFS S a using S in
    if negb a_track then
      unimplemented_function "ENABLE_REFCNT"
    else result_skip S
  using S, runs, globals in
  result_success S args.

End Parameterised.

