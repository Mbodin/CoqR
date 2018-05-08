(** Core.CAltrep.
  The function names in this file correspond to the function names
  in the file main/altrep.c. **)

(** The alternative representation ALTREP is meant to symbolically
  represent some operations, to avoid allocating trivial arrays into
  the memory.  The relevant code is however under active
  developpement, and it would not make sense to start formalising it
  right now.  We thus implement the following function using the
  traditionnal representation, although it needs more memory and time
  resources. **)

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
Require Import CRinlinedfuns.


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


Definition new_compact_intseq S n (n1 inc : int) :=
  add%stack "new_compact_intseq" in
  ifb n = 1 then
    let (S, r) := ScalarInteger globals S n1 in
    result_success S r
  else ifb inc <> 1 /\ inc <> (-1)%Z then
    result_error S "Compact sequences can only have an increment of -1 or 1."
  else
    let%success ans := allocVector globals S IntSxp n using S in
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
    let (S, r) := ScalarReal globals S n1 in
    result_success S r
  else ifb inc <> 1 /\ inc <> (-1)%Z then
    result_error S "Compact sequences can only have an increment of -1 or 1."
  else
    let%success ans := allocVector globals S RealSxp n using S in
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

End Parameterised.

