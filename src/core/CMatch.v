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

Definition pmatch (formal tag : SEXP) exact : result bool :=
  add%stack "pmatch" in
  let get_name str :=
    let%success str_type := TYPEOF str in
    match str_type with
    | SymSxp =>
      let%success str_name := PRINTNAME str in
      CHAR str_name
    | CharSxp =>
      CHAR str
    | StrSxp =>
      let%success str_ := STRING_ELT str 0 in
      result_not_implemented "translateChar(str_)"
    | _ =>
      result_error "Invalid partial string match."
    end in
  let%success f := get_name formal in
  let%success t := get_name tag in
  result_success (psmatch f t exact).

(** The function [matchArgs] matches the arguments supplied to a given
  call with the formal, expected arguments.
  This is more complex as it may seem as arguments in R can be named
  (and thus provided in any order), or can be ‘...’.
  The algorithm presented in this function is thus crucial to understand
  the semantics of function calls in R.
  It is furthermore rather complicated. **)

  (** As it is a large function, it has been divided into all its three
  passes for readability purposes. **)

(** The function makes use of some bits from the general purpose pool
  to mark some arguments as being used or missing. **)

Definition argused e_ :=
  nbits_to_nat (gp e_).

Definition set_argused (used : nat) I :=
  set_gp (nat_to_nbits used I).
Arguments set_argused : clear implicits.

(** First pass: matching exact matches. **)
Definition matchArgs_first formals actuals supplied : result (list nat) :=
  add%stack "matchArgs_first" in
  (** The [fargused] array has been inlined and implemented as a Coq list.
    As such, we build it step by step, the current step being [fargusedi],
    which starts as [0], mimicking the [memset].
    At the end of the step, it is added to the previous [fargused] list.
    This way of building [fargused] builds it backwards compared to the C,
    and we have to revert it at the end of the execution. **)
  fold%success (a, fargusedrev) := (actuals, nil)
  along formals
  as _, f_tag do
    let ftag := f_tag in
    let fargusedi := 0 in
    let%success ftag_sym_name := PRINTNAME ftag in
    let%success ftag_name := CHAR ftag_sym_name in
    let%success fargusedi :=
      ifb ftag <> R_DotsSymbol /\ ftag <> R_NilValue then
        fold%let fargusedi := fargusedi
        along supplied
        as b, b_, b_list do
          let btag := list_tagval b_list in
          ifb btag <> R_NilValue then
            let%success btag_sym_name := PRINTNAME btag in
            let%success btag_name := CHAR btag_sym_name in
            ifb ftag_name = btag_name then
              ifb fargusedi = 2 then
                result_error "Formal argument matched by multiple actual arguments."
              else ifb argused b_ = 2 then
                result_error "Actual argument matches multiple formal arguments."
              else
                set%car a := list_carval b_list in
                run%success
                  ifb list_carval b_list <> R_MissingArg then
                    SET_MISSING a 0 ltac:(nbits_ok)
                  else result_skip in
                map%pointer b with set_argused 2 ltac:(nbits_ok) in
                result_success 2
            else result_success fargusedi
          else result_success fargusedi using runs
      else result_success fargusedi in
    read%list _, a_cdr, _ := a in
    result_success (a_cdr, fargusedi :: fargusedrev) using runs in
  result_success (List.rev fargusedrev).

(** Second pass: matching partial matches. **)
Definition matchArgs_second actuals formals supplied fargused :=
  add%stack "matchArgs_second" in
  (** Similarly than in the previous function, [fargused] is a Coq list.
     Along the R list formals, we pop it out to get the current element
     [fargusedi].  As the list [fargused] has been defined from the same
     [formals] list, it is not possible for it to have a different size.
     We check its size during and after the loop. **)
  fold%success (a, fargused, dots, seendots) :=
    (actuals, fargused, R_NilValue : SEXP, false)
  along formals
  as _, f_tag do
    match fargused with
    | nil =>
      result_impossible "The list/array “fargused” has an unexpected size."
    | fargusedi :: fargused =>
      let%success (dots, seendots) :=
        ifb fargusedi = 0 then
          ifb f_tag = R_DotsSymbol /\ ~ seendots then
            result_success (a, true)
          else
            fold%success fargusedi := fargusedi
            along supplied
            as b, b_, b_list do
              let b_tag := list_tagval b_list in
              ifb argused b_ <> 2 /\ b_tag <> R_NilValue then
                if%success pmatch f_tag b_tag seendots then
                  ifb argused b_ <> 0 then
                    result_error "Actual argument matches several formal arguments."
                  else ifb fargusedi = 1 then
                    result_error "Formal argument matched by multiple actual arguments."
                  else
                    set%car a := list_carval b_list in
                    run%success
                      ifb list_carval b_list <> R_MissingArg then
                        SET_MISSING a 0 ltac:(nbits_ok)
                      else result_skip in
                    map%pointer b with set_argused 1 ltac:(nbits_ok) in
                    result_success 1
                else result_success fargusedi
              else result_success fargusedi using runs in
            result_success (dots, seendots)
        else result_success (dots, seendots) in
      read%list _, a_cdr, _ := a in
      result_success (a_cdr, fargused, dots, seendots)
    end using runs in
  ifb fargused <> nil then
    result_impossible "The list/array “fargused” is bigger than it should be."
  else result_success dots.

(** Third pass: matching based on order. **)
Definition matchArgs_third (formals actuals supplied : SEXP) :=
  add%stack "matchArgs_third" in
  do%success (f, a, b, seendots) := (formals, actuals, supplied, false)
  whileb f <> R_NilValue /\ b <> R_NilValue /\ ~ seendots do
    read%list _, f_cdr, f_tag := f in
    read%list a_car, a_cdr, _ := a in
    ifb f_tag = R_DotsSymbol then
      result_success (f_cdr, a_cdr, b, true)
    else ifb a_car <> R_MissingArg then
      result_success (f_cdr, a_cdr, b, seendots)
    else
      read%list b_, b_car, b_cdr, b_tag := b in
      ifb argused b_ <> 0 \/ b_tag <> R_NilValue then
        result_success (f, a, b_cdr, seendots)
      else
        set%car a := b_car in
        run%success
          ifb b_car <> R_MissingArg then
            SET_MISSING a 0 ltac:(nbits_ok)
          else result_skip in
        map%pointer b with set_argused 1 ltac:(nbits_ok) in
        result_success (f_cdr, a_cdr, b_cdr, seendots) using runs in
  result_skip.

(** In the case there is a ‘...’ in the code, then all non-matching
  arguments are associated to it. **)
Definition matchArgs_dots dots supplied :=
  add%stack "matchArgs_dots" in
  run%success SET_MISSING dots 0 ltac:(nbits_ok) in
  fold%success i := 0
  along supplied
  as _, a_, _ do
    ifb argused a_ = 0 then
      result_success (1 + i)
    else
      result_success i using runs in
  ifb i <> 0 then
    let%success a := allocList globals i in
    set%type a := DotSxp in
    fold%success f := a
    along supplied
    as _, b_, b_list do
      ifb argused b_ = 0 then
        set%car f := list_carval b_list in
        set%tag f := list_tagval b_list in
        read%list _, f_cdr, _ := f in
        result_success f_cdr
      else result_success f using runs in
    set%car dots := a in
    result_skip
  else result_skip.

(** In the case there is no ‘...’ in the code, then there should
  be no unmatched argument left. **)
Definition matchArgs_check supplied :=
  add%stack "matchArgs_check" in
  fold%success (unused, last) := (R_NilValue : SEXP, R_NilValue : SEXP)
  along supplied
  as _, b_, b_list do
    ifb argused b_ = 0 then
      ifb last = R_NilValue then
        let%success unused := CONS globals (list_carval b_list) R_NilValue in
        set%tag unused := list_tagval b_list in
        result_success (unused, unused)
      else
        let%success l := CONS globals (list_carval b_list) R_NilValue in
        set%cdr last := l in
        read%list _, last_cdr, _ := last in
        let last := last_cdr in
        set%tag last := list_tagval b_list in
        result_success (unused, last)
    else result_success (unused, last) using runs in
  ifb last <> R_NilValue then
    result_error "Unused argument(s)."
  else
    result_skip.


Definition matchArgs formals supplied (call : SEXP) :=
  add%stack "matchArgs" in
  fold%success (actuals, argi) := (R_NilValue : SEXP, 0)
  along formals
  as _, _ do
    let%success actuals := CONS_NR globals R_MissingArg actuals in
    run%success SET_MISSING actuals 1 ltac:(nbits_ok) in
    result_success (actuals, 1 + argi) using runs in
  (** A call to [memset] has been inlined here.
     See the definition of [matchArgs_first] for more details. **)
  fold%success
  along supplied
  as b, _, _ do
    map%pointer b with set_argused 0 ltac:(nbits_ok) in
    result_skip using runs in
  (** First pass: matching exact matches. **)
  let%success fargused := matchArgs_first formals actuals supplied in
  (** Second pass: matching partial matches. **)
  let%success dots := matchArgs_second actuals formals supplied fargused in
  (** Third pass: matching based on order. **)
  run%success matchArgs_third formals actuals supplied in
  (** Last stage: checking that all arguments are used. **)
  run%success
    ifb dots <> R_NilValue then
      matchArgs_dots dots supplied
    else
      matchArgs_check supplied in
  result_success actuals.


Definition matchArgs_RC formals supplied call :=
  add%stack "matchArgs_RC" in
  let%success args := matchArgs formals supplied call in
  fold%success
  along args
  as a, _, a_list do
    let%success a_track := TRACKREFS a in
    if negb a_track then
      run%success ENABLE_REFCNT a in
      run%success INCREMENT_REFCNT (list_carval a_list) in
      run%success INCREMENT_REFCNT (list_cdrval a_list) in
      result_skip
    else result_skip
  using runs in
  result_success args.

End Parameterised.

